package org.pitest.mutationtest;

public class MutantCoverageRuntime {

    public static boolean isHit;

    public static void logMutantHit() {
        isHit = true;
    }
}
