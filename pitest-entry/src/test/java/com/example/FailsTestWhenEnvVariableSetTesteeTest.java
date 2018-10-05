package com.example;

import org.junit.Test;

import static org.junit.Assert.assertTrue;

public class FailsTestWhenEnvVariableSetTesteeTest {

  @Test
  public void testNotCurrentlyFalse() {
    final FailsTestWhenEnvVariableSetTestee testee = new FailsTestWhenEnvVariableSetTestee();
    assertTrue(testee.returnTrue());
  }
}
