package org.pitest.aggregate;

import java.io.File;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Map;

import org.pitest.classinfo.ClassName;
import org.pitest.coverage.BlockCoverage;
import org.pitest.coverage.BlockLocation;
import org.pitest.coverage.TestInfo;
import org.pitest.mutationtest.engine.Location;
import org.pitest.mutationtest.engine.MethodName;

class BlockCoverageDataLoader extends DataLoader<BlockCoverage> {

  private static final String METHOD     = "method";
  private static final String CLASSNAME  = "classname";
  private static final String NUMBER     = "number";
  private static final String TESTS      = "tests";

  private static final String OPEN_PAREN = "(";

  BlockCoverageDataLoader(final Collection<File> filesToLoad) {
    super(filesToLoad);
  }

  @Override
  protected BlockCoverage mapToData(final Map<String, Object> map) {
    final String method = (String) map.get(METHOD);
    final Location location = new Location(ClassName.fromString((String) map.get(CLASSNAME)),
        MethodName.fromString(method.substring(0, method.indexOf(OPEN_PAREN))), method.substring(method.indexOf(OPEN_PAREN)));

    final BlockLocation blockLocation = new BlockLocation(location, Integer.parseInt((String) map.get(NUMBER)));

    @SuppressWarnings("unchecked")
    final Collection<String> tests = (Collection<String>) map.get(TESTS);
    final Collection<TestInfo> testInfos = new ArrayList<>();
    for (String test : tests) {
      testInfos.add(new TestInfo(test, test, 0, null, 0, false));
    }

    return new BlockCoverage(blockLocation, testInfos);
  }

}
