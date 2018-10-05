package com.example;

import org.junit.Test;

import static org.junit.Assert.assertEquals;

public class HasMutationInFinallyBlockTest {

  @Test
  public void testIncrementsI() {
    final HasMutationsInFinallyBlock testee = new HasMutationsInFinallyBlock();
    assertEquals(2, testee.foo(1));
  }

}
