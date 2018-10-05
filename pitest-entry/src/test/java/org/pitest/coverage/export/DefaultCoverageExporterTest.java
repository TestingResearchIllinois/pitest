package org.pitest.coverage.export;

import static org.assertj.core.api.Assertions.assertThat;
import static org.pitest.coverage.CoverageMother.aBlockLocation;
import static org.pitest.mutationtest.LocationMother.aLocation;

import java.io.StringWriter;
import java.io.Writer;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;

import org.junit.Before;
import org.junit.Test;
import org.pitest.classinfo.ClassName;
import org.pitest.coverage.BlockCoverage;
import org.pitest.coverage.CoverageData;
import org.pitest.coverage.CoverageMother.BlockLocationBuilder;
import org.pitest.coverage.CoverageSummary;
import org.pitest.coverage.TestInfo;
import org.pitest.mutationtest.LocationMother.LocationBuilder;
import org.pitest.util.ResultOutputStrategy;

public class DefaultCoverageExporterTest {

  private DefaultCoverageExporter testee;

  private final Writer            out = new StringWriter();

  @Before
  public void setup() {
    this.testee = new DefaultCoverageExporter(createOutputStrategy());
  }

  private ResultOutputStrategy createOutputStrategy() {
    return sourceFile -> DefaultCoverageExporterTest.this.out;
  }

  @Test
  public void shouldWriteValidXMLDocumentWhenNoCoverage() {
    this.testee.recordCoverage(Collections.<BlockCoverage> emptyList(),
       null);
    final String actual = this.out.toString();
    assertThat(actual).contains("<?xml version=\"1.0\" encoding=\"UTF-8\"?>");
    assertThat(actual).contains("<coverage>");
    assertThat(actual).contains("</coverage>");
  }

  @Test
  public void shouldExportSuppliedCoverage() {
    final LocationBuilder loc = aLocation().withMethod("method");
    final BlockLocationBuilder block = aBlockLocation().withBlock(42);
    final Collection<BlockCoverage> coverage = Arrays.asList(
        new BlockCoverage(block.withLocation(
            loc.withClass(ClassName.fromString("Foo"))).build(), Arrays.asList(
            new TestInfo("Test1", "Test1", 0, null, 0, false),
            new TestInfo("Test2", "Test2", 0, null, 0, false))),
        new BlockCoverage(block.withLocation(
            loc.withClass(ClassName.fromString("Bar"))).build(), Arrays.asList(
            new TestInfo("Test3", "Test3", 0, null, 0, false),
            new TestInfo("Test4", "Test4", 0, null, 0, false))));
    this.testee.recordCoverage(coverage, null);

    final String actual = this.out.toString();
    assertThat(actual).contains(
        "<block classname='Foo' method='method()I' number='42'>");
    assertThat(actual).contains(
        "<block classname='Bar' method='method()I' number='42'>");
    assertThat(actual).contains(
        "<tests>\n<test name='Test1'/>\n<test name='Test2'/>\n</tests>");
    assertThat(actual).contains(
        "<tests>\n<test name='Test3'/>\n<test name='Test4'/>\n</tests>");
  }

  @Test
  public void shouldEscapeSpecialCharsInTestName() {
    final LocationBuilder loc = aLocation().withMethod("method");
    final BlockLocationBuilder block = aBlockLocation().withBlock(42);
    final Collection<BlockCoverage> coverage = Arrays.asList(
        new BlockCoverage(
            block.withLocation(loc.withClass(ClassName.fromString("Foo"))).build(),
            Collections.singletonList(new TestInfo("ParameterizedTest", "ParameterizedTest[case='Not so simple quotes']", 0, null, 0, false))),
        new BlockCoverage(
            block.withLocation(loc.withClass(ClassName.fromString("Foo"))).build(),
            Collections.singletonList(new TestInfo("ParameterizedTest", "ParameterizedTest[case=\0 Null-Byte]", 0, null, 0, false)))
        );

    testee.recordCoverage(coverage, null);

    final String actual = this.out.toString();
    assertThat(actual).contains(
        "<tests>\n<test name='ParameterizedTest[case=&#39;Not so simple quotes&#39;]'/>\n</tests>");
    assertThat(actual).contains(
        "<tests>\n<test name='ParameterizedTest[case=\\0 Null-Byte]'/>\n</tests>");
  }

}
