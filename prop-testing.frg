#lang forge/temporal

open "sigs.frg"
open "operations.frg"

test suite for Init {
    assert { Init } is sat for exactly 1 Branch, exactly 1 User, exactly 1 CommitNode, exactly 1 Int
}

test suite for Invariants {
    assert { UniqueCommitIDs } is necessary for Invariants
    assert { UniqueBranchIDs } is necessary for Invariants
    assert { Acyclic } is necessary for Invariants
    assert { Reachable } is necessary for Invariants
    assert { RootNoParents } is necessary for Invariants
}

// after any two arbitrary operations, properties must be preserved

pred twoStepTrace {
    Init
    WellformedRepo
    some b1: Branch |
      Commit[b1] or Branching[b1, Repo.mainBranch]
    some b2: Branch |
      Commit[b2] or Branching[b2, Repo.mainBranch] //or Merge[b2, Repo.mainBranch] or Revert[b2]
}

test suite for PostOperationInvariants {
    assert { twoStepTrace and PostOperationInvariants } is necessary for PostOperationInvariants
}
