/*
 * Copyright 2010 Henry Coles
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing,
 * software distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and limitations under the License.
 */
package org.pitest.mutationtest.execute;

import static org.pitest.util.Unchecked.translateCheckedException;

import java.io.BufferedInputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.net.Socket;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.concurrent.ConcurrentHashMap;
import java.util.logging.Level;
import java.util.logging.Logger;
import java.util.stream.Collectors;

import org.pitest.classinfo.ClassName;
import org.pitest.coverage.BlockLocation;
import org.pitest.coverage.CoverageReceiver;
import org.pitest.coverage.execute.CoverageDecorator;
import org.pitest.coverage.execute.CoverageOptions;
import org.pitest.coverage.execute.CoveragePipe;
import org.pitest.functional.F3;
import org.pitest.functional.SideEffect1;
import org.pitest.mutationtest.DetectionStatus;
import org.pitest.mutationtest.MutationStatusTestPair;
import org.pitest.mutationtest.engine.Mutant;
import org.pitest.mutationtest.engine.Mutater;
import org.pitest.mutationtest.engine.MutationDetails;
import org.pitest.mutationtest.engine.MutationIdentifier;
import org.pitest.mutationtest.mocksupport.JavassistInterceptor;
import org.pitest.testapi.TestResult;
import org.pitest.testapi.TestUnit;
import org.pitest.testapi.execute.Container;
import org.pitest.testapi.execute.ExitingResultCollector;
import org.pitest.testapi.execute.MultipleTestGroup;
import org.pitest.testapi.execute.Pitest;
import org.pitest.testapi.execute.containers.ConcreteResultCollector;
import org.pitest.testapi.execute.containers.UnContainer;
import org.pitest.util.Id;
import org.pitest.util.Log;
import org.pitest.util.ReceiveStrategy;
import org.pitest.util.SafeDataInputStream;
import org.pitest.util.SafeDataOutputStream;

public class MutationTestWorker {

  private static final Logger                               LOG   = Log
      .getLogger();

  // micro optimise debug logging
  private static final boolean                              DEBUG = LOG
      .isLoggable(Level.FINE);

  private final Mutater                                     mutater;
  private final ClassLoader                                 loader;
  private final F3<ClassName, ClassLoader, byte[], Boolean> hotswap;
  private final boolean                                     fullMutationMatrix;
  private final CoveragePipe                                invokeQueue;
  private final Socket                                      covSocket;
  private final ReceiveStrategy                             covReceive;
  private final ConcurrentHashMap<String, Collection<BlockLocation>> covMapping;
  private final CoverageOptions                             covOpts;

  public MutationTestWorker(
      final F3<ClassName, ClassLoader, byte[], Boolean> hotswap,
      final Mutater mutater, final ClassLoader loader, final boolean fullMutationMatrix) {
    this.loader = loader;
    this.mutater = mutater;
    this.hotswap = hotswap;
    this.fullMutationMatrix = fullMutationMatrix;
    this.invokeQueue = null;
    this.covSocket = null;
    this.covReceive = null;
    this.covMapping = null;
    this.covOpts = null;
  }

  public MutationTestWorker(
      final F3<ClassName, ClassLoader, byte[], Boolean> hotswap,
      final Mutater mutater, final ClassLoader loader, final boolean fullMutationMatrix,
      final CoveragePipe invokeQueue, final Socket covSocket,
      final ReceiveStrategy covReceive,
      final ConcurrentHashMap<String, Collection<BlockLocation>> covMapping,
      final CoverageOptions covOpts) {
    this.loader = loader;
    this.mutater = mutater;
    this.hotswap = hotswap;
    this.fullMutationMatrix = fullMutationMatrix;
    this.invokeQueue = invokeQueue;
    this.covSocket = covSocket;
    this.covReceive = covReceive;
    this.covMapping = covMapping;
    this.covOpts = covOpts;
  }

  protected void run(final Collection<MutationDetails> range, final Reporter r,
      final TimeOutDecoratedTestSource testSource) throws IOException {

    for (final MutationDetails mutation : range) {
      if (DEBUG) {
        LOG.fine("Running mutation " + mutation);
      }
      final long t0 = System.currentTimeMillis();
      processMutation(r, testSource, mutation);
      if (DEBUG) {
        LOG.fine("processed mutation in " + (System.currentTimeMillis() - t0)
            + " ms.");
      }
    }

  }

  private void processMutation(final Reporter r,
      final TimeOutDecoratedTestSource testSource,
      final MutationDetails mutationDetails) throws IOException {

    final MutationIdentifier mutationId = mutationDetails.getId();
    final Mutant mutatedClass = this.mutater.getMutation(mutationId);

    // For the benefit of mocking frameworks such as PowerMock
    // mess with the internals of Javassist so our mutated class
    // bytes are returned
    JavassistInterceptor.setMutant(mutatedClass);

    if (DEBUG) {
      LOG.fine("mutating method " + mutatedClass.getDetails().getMethod());
    }
    final List<TestUnit> relevantTests = testSource
        .translateTests(mutationDetails.getTestsInOrder());

    r.describe(mutationId);

    final MutationStatusTestPair mutationDetected = handleMutation(
        mutationDetails, mutatedClass, relevantTests);

    r.report(mutationId, mutationDetected);
    if (DEBUG) {
      LOG.fine("Mutation " + mutationId + " detected = " + mutationDetected);
    }
  }

  private MutationStatusTestPair handleMutation(
      final MutationDetails mutationId, final Mutant mutatedClass,
      final List<TestUnit> relevantTests) {
    MutationStatusTestPair mutationDetected;
    if ((relevantTests == null) || relevantTests.isEmpty()) {
      LOG.info("No test coverage for mutation  " + mutationId + " in "
          + mutatedClass.getDetails().getMethod());
      mutationDetected = new MutationStatusTestPair(0,
          DetectionStatus.RUN_ERROR);
    } else {
      mutationDetected = handleCoveredMutation(mutationId, mutatedClass,
          relevantTests);

    }
    return mutationDetected;
  }

  private MutationStatusTestPair handleCoveredMutation(
      final MutationDetails mutationId, final Mutant mutatedClass,
      final List<TestUnit> relevantTests) {
    MutationStatusTestPair mutationDetected;
    if (DEBUG) {
      LOG.fine("" + relevantTests.size() + " relevant test for "
          + mutatedClass.getDetails().getMethod());
    }

    final Container c = createNewContainer();
    final long t0 = System.currentTimeMillis();
    if (this.hotswap.apply(mutationId.getClassName(), this.loader,
        mutatedClass.getBytes())) {
      if (DEBUG) {
        LOG.fine("replaced class with mutant in "
            + (System.currentTimeMillis() - t0) + " ms");
      }
      mutationDetected = doTestsDetectMutation(c, relevantTests);
    } else {
      LOG.warning("Mutation " + mutationId + " was not viable ");
      mutationDetected = new MutationStatusTestPair(0,
          DetectionStatus.NON_VIABLE);
    }
    return mutationDetected;
  }

  private static Container createNewContainer() {
    final Container c = new UnContainer() {
      @Override
      public List<TestResult> execute(final TestUnit group) {
        final List<TestResult> results = new ArrayList<>();
        final ExitingResultCollector rc = new ExitingResultCollector(
            new ConcreteResultCollector(results));
        group.execute(rc);
        return results;
      }
    };
    return c;
  }



  @Override
  public String toString() {
    return "MutationTestWorker [mutater=" + this.mutater + ", loader="
        + this.loader + ", hotswap=" + this.hotswap + "]";
  }

  private MutationStatusTestPair doTestsDetectMutation(final Container c,
      final List<TestUnit> tests) {
    try {
      // Wrap the tests in coverage decorator to collect coverage
      final List<TestUnit> covtests = decorateForCoverage(tests, this.invokeQueue);
      //final List<TestUnit> covtests = tests;

      final CheckTestHasFailedResultListener listener = new CheckTestHasFailedResultListener(fullMutationMatrix);

      final Pitest pit = new Pitest(listener);

      // Send some information over the socket to start (?)
      OutputStream os = this.covSocket.getOutputStream();
      SafeDataOutputStream dos = new SafeDataOutputStream(os);
      // Copying stuff from SendData
      SideEffect1<SafeDataOutputStream> sendInitialData = new SideEffect1<SafeDataOutputStream>() {
        @Override
        public void apply(final SafeDataOutputStream dos) {
          dos.write(covOpts);
          dos.flush();
          List<String> testClasses = new ArrayList<String>();
          for (TestUnit tu : tests) {
            testClasses.add(tu.getDescription().getQualifiedName());
          }
          dos.writeInt(testClasses.size());
          for (final String tc : testClasses) {
            dos.writeString(tc);
          }
          dos.flush();
        }
      };
      sendInitialData.apply(dos);
      
      if (this.fullMutationMatrix) {
        pit.run(c, covtests);
      } else {
        pit.run(c, createEarlyExitTestGroup(covtests));
      }

      return createStatusTestPair(listener);
    } catch (final Exception ex) {
      throw translateCheckedException(ex);
    }

  }

  private MutationStatusTestPair createStatusTestPair(
      final CheckTestHasFailedResultListener listener) {
    List<String> failingTests = listener.getFailingTests().stream()
        .map(description -> description.getQualifiedName()).collect(Collectors.toList());
    List<String> succeedingTests = listener.getSucceedingTests().stream()
        .map(description -> description.getQualifiedName()).collect(Collectors.toList());

    // Receive coverage results
    //receiveResults();
    LOG.fine("AWSHI2 RESULTS?");
    for (String key : covMapping.keySet()) {
        LOG.fine("AWSHI2 KEY " + key + " -> " + covMapping.get(key));
    }

    return new MutationStatusTestPair(listener.getNumberOfTestsRun(),
        listener.status(), failingTests, succeedingTests);
  }

  private List<TestUnit> createEarlyExitTestGroup(final List<TestUnit> tests) {
    return Collections.<TestUnit> singletonList(new MultipleTestGroup(tests));
  }

  // Copied from CoverageWorker
  private List<TestUnit> decorateForCoverage(final List<TestUnit> plainTests,
      final CoverageReceiver queue) {
    final List<TestUnit> decorated = new ArrayList<>(plainTests.size());
    for (final TestUnit each : plainTests) {
      decorated.add(new CoverageDecorator(queue, each));
    }
    return decorated;
  }

  // Copied code from SocketReadingCallable, duplicate for coverage collection
  private void receiveResults() {
    try {
      SafeDataInputStream is = new SafeDataInputStream(new BufferedInputStream(this.covSocket.getInputStream()));
      LOG.fine("AWSHI2 BEFORE control");
      byte control = is.readByte();
      LOG.fine("AWSHI2 AFTER control");
      while (control != Id.DONE) {
        this.covReceive.apply(control, is);
        control = is.readByte();
      }
    } catch (IOException ex) {
      // What to do?
    }
  }

}
