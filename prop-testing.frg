#lang forge/temporal

open "sigs.frg"
open "operations.frg"

test suite for Init {
    assert { Init } is sat for exactly 1 Branch, exactly 1 User, exactly 1 CommitNode, exactly 1 Int
}

test suite for Invariants {
    // TESTS OF INCLUSION
    assert { UniqueCommitIDs } is necessary for Invariants
    assert { UniqueBranchIDs } is necessary for Invariants
    assert { Acyclic } is necessary for Invariants
    assert { Reachable } is necessary for Invariants
    assert { RootNoParents } is necessary for Invariants

    // TESTS OF EXLCUSION
    // is sufficient for, is sat/unsat, is checked
    //assert { NonUniqueCommitIDs } is unsat for exactly 1 Branch, exactly 1 User, 2 CommitNode, 3 Int
    //assert { NonUniqueBranchIDs } is unsat for exactly 1 Branch, exactly 1 User, 2 CommitNode, 3 Int
    assert { not Cyclic } is sat for exactly 1 Branch, exactly 1 User, 2 CommitNode, 3 Int
    assert { not NotReachable } is sat for exactly 1 Branch, exactly 1 User, 2 CommitNode, 3 Int
    assert { not RootWithParents } is sat for exactly 1 Branch, exactly 1 User, 2 CommitNode, 3 Int
}

// after any two arbitrary operations, properties must be preserved

pred twoStepTrace {
    Init
    WellformedRepo
    some b1: Branch |
        Branching[b1, Repo.mainBranch] //or Commit[b1]
    some b2: Branch |
        Branching[b2, Repo.mainBranch] //or Commit[b2] or Merge[b2, Repo.mainBranch] or Revert[b2]
}

test suite for PostOperationInvariants {
    assert { twoStepTrace } is sufficient for PostOperationInvariants
}


// unit testing: tests of inclusion and exclusion for every predicate
