package org.pitest.junit.adapter;

import org.junit.runner.Description;
import org.junit.runner.notification.Failure;
import org.junit.runner.notification.RunListener;
import org.junit.runner.notification.StoppedByUserException;
import org.pitest.testapi.ResultCollector;

class AdaptingRunListener extends RunListener {

  private final org.pitest.testapi.Description description;
  private final ResultCollector                rc;
  private       boolean                        failed = false;

  AdaptingRunListener(final org.pitest.testapi.Description description,
      final ResultCollector rc) {
    this.description = description;
    this.rc = rc;
  }

  static org.pitest.testapi.Description toDescription(Description desc) {
    return new org.pitest.testapi.Description(desc.toString(), desc.getClassName());
  }

  @Override
  public void testFailure(final Failure failure) throws Exception {
    this.rc.notifyEnd(toDescription(failure.getDescription()), failure.getException());
    this.failed = true;
  }

  @Override
  public void testAssumptionFailure(final Failure failure) {
    // do nothing so treated as success
    // see http://junit.sourceforge.net/doc/ReleaseNotes4.4.html#assumptions
  }

  @Override
  public void testIgnored(final Description description) throws Exception {
    this.rc.notifySkipped(

        toDescription(description));
  }

  @Override
  public void testStarted(final Description description) throws Exception {
    if (this.failed) {
      // If the JUnit test has been annotated with @BeforeClass or @AfterClass
      // need to force the exit after the first failure as tests will be run as
      // a block
      // rather than individually.
      // This is apparently the junit way.
      throw new StoppedByUserException();
    }
    this.rc.notifyStart(toDescription(description));
  }

  @Override
  public void testFinished(final Description description) throws Exception {
    if (!this.failed) {
      this.rc.notifyEnd(toDescription(description));

    }

  }

}
