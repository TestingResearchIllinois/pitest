package org.pitest.coverage;

import java.util.Collection;

public class BlockCoverage {

  private final BlockLocation      block;
  private final Collection<TestInfo> tests;

  public BlockCoverage(final BlockLocation block, final Collection<TestInfo> tests) {
    this.block = block;
    this.tests = tests;
  }

  public BlockLocation getBlock() {
    return this.block;
  }

  public Collection<TestInfo> getTests() {
    return this.tests;
  }

}
