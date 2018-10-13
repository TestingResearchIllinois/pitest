/*
 * Copyright 2011 Henry Coles
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
package org.pitest.mutationtest;

import java.io.Serializable;
import java.util.*;

public final class MutationStatusTestPair implements Serializable {

  private static final long serialVersionUID = 1L;

  private int             numberOfTestsRun;
  private DetectionStatus status;
  private final List<String>    killingTests;
  private final List<String>    succeedingTests;
  private final List<String>    coveringTests;
  private final HashMap<String, Integer> timesSeen = new HashMap<>();

  public MutationStatusTestPair(final int numberOfTestsRun,
      final DetectionStatus status) {
    this(numberOfTestsRun, status, null);
  }

  public MutationStatusTestPair(final int numberOfTestsRun,
      final DetectionStatus status, final String killingTest) {
    this(numberOfTestsRun, status, killingTestToList(killingTest),
      Collections.emptyList(), Collections.emptyList());
  }

  public MutationStatusTestPair(final int numberOfTestsRun,
                                final DetectionStatus status, final List<String> killingTests,
                                final List<String> succeedingTests, final List<String> coveringTests) {
    this.status = status;
    this.killingTests = new LinkedList<>(killingTests);
    this.succeedingTests = new LinkedList<>(succeedingTests);
    this.numberOfTestsRun = numberOfTestsRun;
    this.coveringTests = new LinkedList<>(coveringTests);

    HashSet<String> allTests = new HashSet<>(getKillingTests());
    allTests.addAll(getSucceedingTests());
    allTests.addAll(getCoveringTests());
    renameTests(allTests);//initialize counts

  }

  public void renameTests(String suffix) {
    _renameTests(killingTests, suffix);
    _renameTests(succeedingTests, suffix);
    _renameTests(coveringTests, suffix);
  }

  private void _renameTests(List<String> aList, String suffix)
  {
    for(int i = 0; i < aList.size(); i++)
    {
      aList.set(i,aList.get(i)+suffix);
    }
  }

  
  private static List<String> killingTestToList(String killingTest) {
    if (killingTest == null) {
      return new ArrayList<>();
    }
    
    return Arrays.asList(killingTest);
  }

  public DetectionStatus getStatus() {
    return this.status;
  }

  /**
   * Get the killing test.
   * If the full mutation matrix is enabled, the first test will be returned.
   */
  public Optional<String> getKillingTest() {
    if (this.killingTests.isEmpty()) {
      return Optional.empty();
    }
    return Optional.of(this.killingTests.get(0));
  }

  /** Get all killing tests.
   *  If the full mutation matrix is not enabled, this will only be the first killing test. 
   */
  public List<String> getKillingTests() {
    return killingTests;
  }

  public List<String> getCoveringTests() {
    return coveringTests;
  }

  /** Get all succeeding tests.
   *  If the full mutation matrix is not enabled, this list will be empty. 
   */
  public List<String> getSucceedingTests() {
    return succeedingTests;
  }

  public int getNumberOfTestsRun() {
    return this.numberOfTestsRun;
  }

  @Override
  public String toString() {
    if (this.killingTests.isEmpty()) {
      return this.status.name();
    } else {
      return this.status.name() + " by " + this.killingTests;
    }

  }

  @Override
  public int hashCode() {
    final int prime = 31;
    int result = 1;
    result = (prime * result)
        + ((this.killingTests == null) ? 0 : this.killingTests.hashCode());
    result = (prime * result)
        + ((this.succeedingTests == null) ? 0 : this.succeedingTests.hashCode());
    result = (prime * result) + this.numberOfTestsRun;
    result = (prime * result)
        + ((this.status == null) ? 0 : this.status.hashCode());
    return result;
  }

  @Override
  public boolean equals(final Object obj) {
    if (this == obj) {
      return true;
    }
    if (obj == null) {
      return false;
    }
    if (getClass() != obj.getClass()) {
      return false;
    }
    final MutationStatusTestPair other = (MutationStatusTestPair) obj;
    if (!Objects.equals( this.killingTests,other.killingTests)) {
      return false;
    }
    if (!Objects.equals(this.succeedingTests, other.succeedingTests)) {
      return false;
    }
    if (this.numberOfTestsRun != other.numberOfTestsRun) {
      return false;
    }
    if (this.status != other.status) {
      return false;
    }
    return true;
  }

  private int runCount = 0;
  private String renameTestIfPreviouslySeen(String test){
    Integer idx = this.timesSeen.putIfAbsent(test,1);
    if(idx == null)
      return test;
    this.timesSeen.put(test,idx+1);
    if(idx > runCount)
      runCount = idx;
    return test+"#"+idx;
  }
  private HashMap<String,String> renameTests(Iterable<String> in){
    HashMap<String,String> ret = new HashMap<>();
    for(String s : in)
      if(!ret.containsKey(s))
        ret.put(s,renameTestIfPreviouslySeen(s));
    return ret;
  }
  private LinkedList<String> remapTests(Iterable<String> in, HashMap<String,String> map) {
    LinkedList<String> ret = new LinkedList<>();
    for (String s : in)
    {
      ret.add(map.get(s));
    }
    return ret;
  }

  public void checkForNotFullyTried(){
    HashSet<String> allTests = new HashSet<>(getKillingTests());
    allTests.addAll(getSucceedingTests());
    allTests.addAll(getCoveringTests());
    HashMap<String,String> map = renameTests(allTests);
    allTests.removeAll(getCoveringTests());
    if(allTests.size() > 0 && runCount < 10)
    {
      //Still not done yet, this test is not determined
      this.status = DetectionStatus.NOT_TRIED_FULLY;
    }

  }

  public void accumulate(MutationStatusTestPair status) {

    HashSet<String> allTests = new HashSet<>(status.getKillingTests());
    allTests.addAll(status.getSucceedingTests());
    allTests.addAll(status.getCoveringTests());
    HashMap<String,String> map = renameTests(allTests);

    this.killingTests.addAll(remapTests(status.getKillingTests(), map));
    this.succeedingTests.addAll(remapTests(status.getSucceedingTests(), map));
    this.coveringTests.addAll(remapTests(status.getCoveringTests(), map));
    this.numberOfTestsRun+=status.getNumberOfTestsRun();

    this.status = status.status;

    allTests.removeAll(status.getCoveringTests());
    if(allTests.size() > 0 && runCount < 10)
    {
      //Still not done yet, this test is not determined
      this.status = DetectionStatus.NOT_TRIED_FULLY;
    }
    else
    {
      //Calculate the final status
      HashSet<String> killingCovering = new HashSet<>(this.killingTests);
      killingCovering.retainAll(this.coveringTests);
      HashSet<String> succCovering = new HashSet<>(this.coveringTests);
      succCovering.retainAll(this.coveringTests);
      if(killingCovering.size() > 0)
        this.status = DetectionStatus.KILLED;
      else if(this.killingTests.size() > 0 && this.succeedingTests.size() == 0)
        this.status = DetectionStatus.KILLED_NOT_COVERED;
      else if(this.killingTests.size() > 0)
        this.status = DetectionStatus.UNKNOWN_WEIRD;
      else if(succCovering.size() > 0)
        this.status= DetectionStatus.SURVIVED;
      else if(this.succeedingTests.size() > 0)
        this.status = DetectionStatus.SURVIVED_NOT_COVERED;
      else
        this.status = DetectionStatus.UNKNOWN_WEIRD;
      if (status.status == DetectionStatus.MEMORY_ERROR
          || status.status == DetectionStatus.NON_VIABLE
          || status.status == DetectionStatus.TIMED_OUT
          || status.status == DetectionStatus.RUN_ERROR)
        this.status = status.status;
    }


  }
}
