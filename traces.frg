#lang forge/temporal

open "operations.frg"
open "sigs.frg"

option max_tracelength 10
option min_tracelength 10

pred testDemoMerge {
    Init
    always {
        WellformedRepo
    }

    Branching[Repo.firstRoot]
    next_state Commit[Repo.firstRoot]
    next_state next_state {
        some br: Root | {
          br in Repo.firstRoot.outgoingBranches
          Merge[Repo.firstRoot, br]
        }
    }
}

run testDemoMerge for exactly 4 CommitNode, exactly 2 Root, 5 Int


pred testDemoCommitBranchRevert {
    Init
    always {
        WellformedRepo
    }
    
    Commit[Repo.firstRoot]
    next_state Revert[Repo.firstRoot]
    next_state next_state next_state Branching[Repo.firstRoot]
    next_state next_state next_state next_state Commit[Repo.firstRoot]

}

run testDemoCommitBranchRevert for exactly 7 CommitNode, exactly 3 Root, 5 Int

// test: single commit on initial root
pred testCommitOneNode {
    Init
    always{
        WellformedRepo
    }
    Commit[Repo.firstRoot]
}
// run testCommitOneNode for exactly 4 CommitNode, 5 Int

// test: single branch on initial root
pred testBranchOneNode {
    Init
    always{
        WellformedRepo
    }
    eventually {
        Branching[Repo.firstRoot]
    }
}
// run testBranchOneNode for exactly 4 CommitNode, exactly 2 Root, 5 Int

// test: single commit on initial root
pred testBranch3 {
    Init
    always{
        WellformedRepo
    }
    // Commit
    Branching[Repo.firstRoot]
    next_state Branching[Repo.firstRoot]
    next_state next_state Branching[Repo.firstRoot]

}
// run testBranch3 for exactly 4 CommitNode, exactly 4 Root, 5 Int

pred testBranchMerge {
    Init
    always {
        WellformedRepo
    }
    // Commit
    Branching[Repo.firstRoot]
    next_state {
        some br: Root | {
          br in Repo.firstRoot.outgoingBranches
          Merge[Repo.firstRoot, br]
        }
    }
}
// run testBranchMerge for exactly 4 CommitNode, exactly 2 Root, 7 Int

