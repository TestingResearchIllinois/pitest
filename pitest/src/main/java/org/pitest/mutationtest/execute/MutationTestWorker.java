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

import org.pitest.classinfo.ClassName;
import org.pitest.functional.F3;
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
import org.pitest.util.Log;

import java.io.IOException;
import java.util.*;
import java.util.logging.Level;
import java.util.logging.Logger;
import java.util.stream.Collectors;

import static org.pitest.util.Unchecked.translateCheckedException;

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

  public MutationTestWorker(
      final F3<ClassName, ClassLoader, byte[], Boolean> hotswap,
      final Mutater mutater, final ClassLoader loader, final boolean fullMutationMatrix) {
    this.loader = loader;
    this.mutater = mutater;
    this.hotswap = hotswap;
    this.fullMutationMatrix = fullMutationMatrix;
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
      if (System.getenv("PIT_RERUN_SAME_JVM") != null) {
        mutationDetected = doTestsDetectMutationWithReruns(c, relevantTests);
      } else {
        mutationDetected = doTestsDetectMutation(c, relevantTests);
      }
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

  private MutationStatusTestPair doTestsDetectMutationWithReruns(final Container c,
      final List<TestUnit> tests) {
    try {
      // Store some values concerning overall runs with reruns
      int numTotalRuns = 0;
      List<String> allKillingAndCovering = new ArrayList<String>();
      List<String> allSucceedingAndCovering = new ArrayList<String>();
      List<String> allKilling = new ArrayList<>();
      List<String> allSucceeding = new ArrayList<>();
      List<String> allCoveringTests = new ArrayList<String>();

      // Determine what tests can be saved and which need to be rerun
      // NOTE: Run at most 10 times for now
      for (int count = 0; count < 10; count++) {
        MutationStatusTestPair pair = doTestsDetectMutation(c, tests);
        // Exit early if found some status without knowledge of tests...
        if (pair.getStatus() == DetectionStatus.TIMED_OUT
          || pair.getStatus() == DetectionStatus.NON_VIABLE
          || pair.getStatus() == DetectionStatus.MEMORY_ERROR
          || pair.getStatus() == DetectionStatus.RUN_ERROR) {
          return pair;
        }
        pair.renameTests("#" + count);

        List<String> coveringTests = pair.getCoveringTests();

        // Intersect to get all the ones that both cover and kill/survive
        Set<String> killingAndCoveringTests = new HashSet<String>(pair.getKillingTests());
        killingAndCoveringTests.retainAll(coveringTests);
        Set<String> succeedingAndCoveringTests = new HashSet<String>(pair.getSucceedingTests());
        succeedingAndCoveringTests.retainAll(coveringTests);

        // Accumulate all data from this run
        numTotalRuns += pair.getNumberOfTestsRun();
        allKillingAndCovering.addAll(killingAndCoveringTests);
        allSucceedingAndCovering.addAll(succeedingAndCoveringTests);
        allCoveringTests.addAll(pair.getCoveringTests());
        allKilling.addAll(pair.getKillingTests());
        allSucceeding.addAll(pair.getSucceedingTests());

        // If not full matrix and found that a test has actually killed the mutant, stop
        if (!this.fullMutationMatrix && killingAndCoveringTests.size() > 0) {
          break;
        }

        // Remove any test that was covering already from set of tests to rerun next iteration
        Set<TestUnit> toRemove = new HashSet<TestUnit>();
        for (TestUnit tu : tests) {
          if (coveringTests.contains(
              tu.getDescription().getQualifiedName() + "#" + count)) {
            toRemove.add(tu);
          }
        }
        tests.removeAll(toRemove);
        // Can quit if no more tests to rerun
        if (tests.isEmpty()) {
          break;
        }
      }

      // Make an overall pair with accumulated data
      DetectionStatus overallStatus;    // TODO: Double-check status logic
      if (allKillingAndCovering.size() > 0) {
        //If at least one test killed and covered then "killed"
        overallStatus = DetectionStatus.KILLED;
      } else if (allSucceedingAndCovering.size() > 0 && allSucceeding.size() == allSucceedingAndCovering.size() && allKilling.size() == 0) {
        //If EVERY time it's supposed to be covered it IS covered and succeeds every time
        overallStatus = DetectionStatus.SURVIVED;
      } else if (allCoveringTests.size() == 0) {
        overallStatus = DetectionStatus.NOT_COVERED_DURING_RUN;
      } else {
        //Primarily: COVERED but SURVIVED, also has some NOT COVERED
        overallStatus = DetectionStatus.UNKNOWN_WEIRD;
      }
      MutationStatusTestPair overallPair = new MutationStatusTestPair(numTotalRuns, overallStatus, allKilling, allSucceeding, allCoveringTests);

      return overallPair;
    } catch (final Exception ex) {
      throw translateCheckedException(ex);
    }
  }

  private MutationStatusTestPair doTestsDetectMutation(final Container c,
      final List<TestUnit> tests) {
    try {
      final CheckTestHasFailedResultListener listener = new CheckTestHasFailedResultListener(fullMutationMatrix);

      final Pitest pit = new Pitest(listener);
      
      if (this.fullMutationMatrix) {
        pit.run(c, tests);
      } else {
        pit.run(c, createEarlyExitTestGroup(tests));
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
    List<String> coveringTests = listener.getCoveringTests().stream()
            .map(description -> description.getQualifiedName()).collect(Collectors.toList());

    return new MutationStatusTestPair(listener.getNumberOfTestsRun(),
        listener.status(), failingTests, succeedingTests, coveringTests);
  }

  private List<TestUnit> createEarlyExitTestGroup(final List<TestUnit> tests) {
    return Collections.<TestUnit> singletonList(new MultipleTestGroup(tests));
  }

}
