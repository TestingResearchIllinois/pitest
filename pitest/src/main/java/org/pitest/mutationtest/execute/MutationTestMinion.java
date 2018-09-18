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

import java.io.BufferedOutputStream;
import java.io.IOException;
import java.lang.management.MemoryNotificationInfo;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.function.Predicate;
import java.util.logging.Level;
import java.util.logging.Logger;
import java.util.stream.Collectors;

import javax.management.NotificationListener;
import javax.management.openmbean.CompositeData;

import org.pitest.boot.HotSwapAgent;
import org.pitest.classinfo.CachingByteArraySource;
import org.pitest.classinfo.ClassByteArraySource;
import org.pitest.classinfo.ClassName;
import org.pitest.classpath.ClassloaderByteArraySource;
import org.pitest.coverage.BlockLocation;
import org.pitest.coverage.CoverageResult;
import org.pitest.coverage.execute.CoveragePipe;
import org.pitest.coverage.CoverageTransformer;
import org.pitest.coverage.execute.CoverageOptions;
import org.pitest.functional.F3;
import org.pitest.functional.SideEffect1;
import org.pitest.functional.prelude.Prelude;
import org.pitest.mutationtest.EngineArguments;
import org.pitest.mutationtest.config.ClientPluginServices;
import org.pitest.mutationtest.config.MinionSettings;
import org.pitest.mutationtest.config.TestPluginArguments;
import org.pitest.mutationtest.engine.Location;
import org.pitest.mutationtest.engine.MethodName;
import org.pitest.mutationtest.engine.MutationEngine;
import org.pitest.mutationtest.engine.MutationDetails;
import org.pitest.mutationtest.mocksupport.BendJavassistToMyWillTransformer;
import org.pitest.mutationtest.mocksupport.JavassistInputStreamInterceptorAdapater;
import org.pitest.mutationtest.mocksupport.JavassistInterceptor;
import org.pitest.testapi.Configuration;
import org.pitest.testapi.Description;
import org.pitest.testapi.TestUnit;
import org.pitest.testapi.execute.FindTestUnits;
import org.pitest.util.ExitCode;
import org.pitest.util.Glob;
import org.pitest.util.Id;
import org.pitest.util.IsolationUtils;
import org.pitest.util.Log;
import org.pitest.util.ReceiveStrategy;
import org.pitest.util.SafeDataInputStream;

import sun.pitest.CodeCoverageStore;

public class MutationTestMinion {

  private static final Logger       LOG = Log.getLogger();

  // We maintain a small cache to avoid reading byte code off disk more than once
  // Size is arbitrary but assumed to be large enough to cover likely max number of inner classes
  private static final int CACHE_SIZE = 12;

  private final SafeDataInputStream dis;
  private final Reporter            reporter;
  private final MinionSettings      plugins;

  public MutationTestMinion(MinionSettings plugins, final SafeDataInputStream dis,
      final Reporter reporter) {
    this.dis = dis;
    this.reporter = reporter;
    this.plugins = plugins;
  }

  public void run() {
    ExitCode exitCode = ExitCode.OK;
    CoveragePipe invokeQueue = null;
    Socket s = null;

    try {

      final MinionArguments paramsFromParent = this.dis
          .read(MinionArguments.class);

      Log.setVerbose(paramsFromParent.isVerbose());

      final ClassLoader loader = IsolationUtils.getContextClassLoader();

      final ClassByteArraySource byteSource = new CachingByteArraySource(new ClassloaderByteArraySource(
          loader), CACHE_SIZE);

      final F3<ClassName, ClassLoader, byte[], Boolean> hotswap = new HotSwap(
          byteSource);

      final MutationEngine engine = createEngine(paramsFromParent.engine, paramsFromParent.engineArgs);

      // Copying some coverage-related code over
      ServerSocket socket = new ServerSocket(0);    // Take newly allocated port (0 indicates new)
      int port = socket.getLocalPort();
      s = new Socket("localhost", port);
      invokeQueue = new CoveragePipe(new BufferedOutputStream(
          s.getOutputStream()));
      CodeCoverageStore.init(invokeQueue);
      // Add transformer to each mutation class
      List<String> mutantClasses = new ArrayList<String>();
      for (MutationDetails mutationDetail : paramsFromParent.mutations) {
        mutantClasses.add(mutationDetail.getClassName().asJavaName());
      }
      Predicate<String> filter = Prelude.or(Glob.toGlobPredicates(mutantClasses));
      HotSwapAgent.addTransformer(new CoverageTransformer(
          convertToJVMClassFilter(filter)));
      // Construct the CoverageOptions that seems to be needed
      final CoverageOptions covOpts = new CoverageOptions(mutantClasses,
          new ArrayList<String>(), paramsFromParent.pitConfig, false, 0);
      // Send some information over to get coverage started (?)
      // Use custom map to keep track of coverage overall
      final ConcurrentHashMap<String, Collection<BlockLocation>> coverageMapping =
          new ConcurrentHashMap<String, Collection<BlockLocation>>();
      // Special ReceiveStrategy object (copied from Receive in pitest-entry)
      ReceiveStrategy receive = new ReceiveStrategy() {
        private final Map<Integer, ClassName>     classIdToName = new ConcurrentHashMap<>();
        private final Map<Long, BlockLocation>    probeToBlock  = new ConcurrentHashMap<>();
        // Make custom handler to deal with the different CoverageResult
        private final SideEffect1<CoverageResult> handler = new SideEffect1<CoverageResult>() {
          @Override
          public void apply(final CoverageResult cr) {
            Description desc = cr.getTestUnitDescription();
            Collection<BlockLocation> blocks = cr.getCoverage();
            coverageMapping.put(desc.getQualifiedName(), blocks);
          }
        };

        @Override
        public void apply(byte control, SafeDataInputStream is) {
          switch (control) {
          case Id.CLAZZ:
            final int id = is.readInt();
            final String name = is.readString();
            this.classIdToName.put(id, ClassName.fromString(name));
            break;
          case Id.PROBES:
            handleProbes(is);
            break;
          case Id.OUTCOME:
            handleTestEnd(is);
            break;
          case Id.DONE:
            // nothing to do ?
          }
        }

        private void handleProbes(final SafeDataInputStream is) {
          final int classId = is.readInt();
          final String methodName = is.readString();
          final String methodSig = is.readString();
          final int first = is.readInt();
          final int last = is.readInt();
          final Location loc = Location.location(this.classIdToName.get(classId),
              MethodName.fromString(methodName), methodSig);
          for (int i = first; i != (last + 1); i++) {
            // nb, convert from classwide id to method scoped index within
            // BlockLocation
            this.probeToBlock.put(CodeCoverageStore.encode(classId, i),
                new BlockLocation(loc, i - first));
          }
        }

        private void handleTestEnd(final SafeDataInputStream is) {
          final Description d = is.read(Description.class);
          final int numberOfResults = is.readInt();

          final Set<BlockLocation> hits = new HashSet<>(numberOfResults);

          for (int i = 0; i != numberOfResults; i++) {
            readProbeHit(is, hits);
          }

          this.handler.apply(createCoverageResult(is, d, hits));
        }

        private void readProbeHit(final SafeDataInputStream is,
            final Set<BlockLocation> hits) {
          final long encoded = is.readLong();
          final BlockLocation location = probeToBlock(encoded);
          hits.add(location);
        }

        private BlockLocation probeToBlock(long encoded) {
          return this.probeToBlock.get(encoded);
        }

        private CoverageResult createCoverageResult(final SafeDataInputStream is,
            final Description d, Collection<BlockLocation> visitedBlocks) {
          final boolean isGreen = is.readBoolean();
          final int executionTime = is.readInt();
          final CoverageResult cr = new CoverageResult(d, executionTime, isGreen,
              visitedBlocks);
          return cr;
        }
      };

      final MutationTestWorker worker = new MutationTestWorker(hotswap,
          engine.createMutator(byteSource), loader, paramsFromParent.fullMutationMatrix,
          invokeQueue, s, receive, coverageMapping, covOpts);

      final List<TestUnit> tests = findTestsForTestClasses(loader,
          paramsFromParent.testClasses, createTestPlugin(paramsFromParent.pitConfig));

      worker.run(paramsFromParent.mutations, this.reporter,
          new TimeOutDecoratedTestSource(paramsFromParent.timeoutStrategy,
              tests, this.reporter));

      this.reporter.done(ExitCode.OK);
    } catch (final Throwable ex) {
      ex.printStackTrace(System.out);
      LOG.log(Level.WARNING, "Error during mutation test", ex);
      this.reporter.done(ExitCode.UNKNOWN_ERROR);
      exitCode = ExitCode.UNKNOWN_ERROR;
    } finally {
      if (invokeQueue != null) {
        invokeQueue.end(exitCode);
      }
    }

  }

  private MutationEngine createEngine(String engine, EngineArguments args) {
    return this.plugins.createEngine(engine).createEngine(args);
  }

  private Configuration createTestPlugin(TestPluginArguments pitConfig) {
    return this.plugins.getTestFrameworkPlugin(pitConfig, ClassloaderByteArraySource.fromContext());
  }

  public static void main(final String[] args) {

    LOG.log(Level.FINE, "minion started");

    enablePowerMockSupport();

    final int port = Integer.valueOf(args[0]);

    Socket s = null;
    try {
      s = new Socket("localhost", port);
      final SafeDataInputStream dis = new SafeDataInputStream(
          s.getInputStream());

      final Reporter reporter = new DefaultReporter(s.getOutputStream());
      addMemoryWatchDog(reporter);
      final ClientPluginServices plugins = new ClientPluginServices(IsolationUtils.getContextClassLoader());
      final MinionSettings factory = new MinionSettings(plugins);
      final MutationTestMinion instance = new MutationTestMinion(factory, dis, reporter);
      instance.run();
    } catch (final Throwable ex) {
      ex.printStackTrace(System.out);
      LOG.log(Level.WARNING, "Error during mutation test", ex);
    } finally {
      if (s != null) {
        safelyCloseSocket(s);
      }
    }

  }

  private static List<TestUnit> findTestsForTestClasses(
      final ClassLoader loader, final Collection<ClassName> testClasses,
      final Configuration pitConfig) {
    final Collection<Class<?>> tcs = testClasses.stream().flatMap(ClassName.nameToClass(loader)).collect(Collectors.toList());
    final FindTestUnits finder = new FindTestUnits(pitConfig);
    return finder.findTestUnitsForAllSuppliedClasses(tcs);
  }

  private static void enablePowerMockSupport() {
    // Bwahahahahahahaha
    HotSwapAgent.addTransformer(new BendJavassistToMyWillTransformer(Prelude
        .or(new Glob("javassist/*")), JavassistInputStreamInterceptorAdapater.inputStreamAdapterSupplier(JavassistInterceptor.class)));
  }

  private static void safelyCloseSocket(final Socket s) {
    if (s != null) {
      try {
        s.close();
      } catch (final IOException e) {
        LOG.log(Level.WARNING, "Couldn't close socket", e);
      }
    }
  }

  private static void addMemoryWatchDog(final Reporter r) {
    final NotificationListener listener = (notification, handback) -> {
    final String type = notification.getType();
    if (type.equals(MemoryNotificationInfo.MEMORY_THRESHOLD_EXCEEDED)) {
    final CompositeData cd = (CompositeData) notification.getUserData();
    final MemoryNotificationInfo memInfo = MemoryNotificationInfo
        .from(cd);
    CommandLineMessage.report(memInfo.getPoolName()
        + " has exceeded the shutdown threshold : " + memInfo.getCount()
        + " times.\n" + memInfo.getUsage());

    r.done(ExitCode.OUT_OF_MEMORY);

    } else {
    LOG.warning("Unknown notification: " + notification);
    }
   };

    MemoryWatchdog.addWatchDogToAllPools(90, listener);

  }

  private static Predicate<String> convertToJVMClassFilter(
      final Predicate<String> child) {
    return a -> child.test(a.replace("/", "."));
  }


}
