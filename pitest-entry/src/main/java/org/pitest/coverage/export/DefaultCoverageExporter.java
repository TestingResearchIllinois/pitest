package org.pitest.coverage.export;

import org.pitest.coverage.*;
import org.pitest.mutationtest.engine.Location;
import org.pitest.util.ResultOutputStrategy;
import org.pitest.util.StringUtil;
import org.pitest.util.Unchecked;

import java.io.IOException;
import java.io.Writer;
import java.util.*;

/**
 * Quick and dirty export of coverage data into XML
 */
public class DefaultCoverageExporter implements CoverageExporter {

  private final ResultOutputStrategy outputStrategy;

  public DefaultCoverageExporter(final ResultOutputStrategy outputStrategy) {
    this.outputStrategy = outputStrategy;
  }

  private CoverageData covData;
  @Override
  public void recordCoverage(final Collection<BlockCoverage> coverage,
      CoverageData covData) {
    final Writer out = this.outputStrategy
        .createWriterForFile("linecoverage.xml");
    this.covData = covData;
    writeHeader(out, covData.createSummary());
    for (final BlockCoverage each : coverage) {
      writeLineCoverage(each, out);
    }

    writeFooterAndClose(out);
  }

  private void writeHeader(final Writer out, CoverageSummary summary) {
    write(out, "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n");
    write(out,
        "<coverage linesCovered='" + summary.getNumberOfCoveredLines() + "'"
            + " totalLines='" + summary.getNumberOfLines()
            + "' coverage='" + summary.getCoverage() + "'>\n");
  }

  private void writeLineCoverage(final BlockCoverage each, final Writer out) {
    final Location l = each.getBlock().getLocation();

    Set<Integer> lines = covData.getLinesForBlock(each.getBlock());
    write(
        out,
        "<block classname='" + l.getClassName().asJavaName() + "'"
            + " method='"
            + StringUtil.escapeBasicHtmlChars(l.getMethodName().name()) + StringUtil.escapeBasicHtmlChars(l.getMethodDesc())
            + "' number='" + each.getBlock().getBlock() + "'>");
    write(out, "<lines>");
    for (Integer i : lines) {
      write(out, "<line>" + i + "</line>");
    }
    write(out, "</lines>\n");
    write(out, "<tests>\n");
    final List<TestInfo> ts = new ArrayList<>(each.getTests());
    Collections.sort(ts,(o1, o2) -> o1.getName().compareTo(o2.getName()));
    for (final TestInfo test : ts) {
      write(out,
          "<test name='" + StringUtil.escapeBasicHtmlChars(test.getName())
              + "' hitCount='" + test.getHitCount() + "'/>\n");
    }
    write(out, "</tests>\n");
    write(out, "</block>\n");
  }

  private void writeFooterAndClose(final Writer out) {
    try {
      write(out, "</coverage>\n");
      out.close();
    } catch (final IOException e) {
      throw Unchecked.translateCheckedException(e);
    }
  }

  private void write(final Writer out, final String value) {
    try {
      out.write(value);
    } catch (final IOException e) {
      throw Unchecked.translateCheckedException(e);
    }
  }

}
