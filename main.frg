#lang forge/temporal

open "operations.frg"
open "sigs.frg"

option max_tracelength 3
option min_tracelength 3

pred testCommitOneNode {
    Init
    always{
        WellformedRepo
        // TODO: how come we get Unsat when we try to always Commit?
        // Commit[Repo.firstRoot]
    }
    Commit[Repo.firstRoot]
}
//run testCommitOneNode for exactly 4 CommitNode, 5 Int


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

pred testBranch3 {
    Init
    always{
        WellformedRepo
    }

    Branching[Repo.firstRoot]
    next_state Branching[Repo.firstRoot]
    next_state next_state Branching[Repo.firstRoot]

}
run testBranch3 for exactly 4 CommitNode, exactly 4 Root, 5 Int

pred testBranchMerge {
    Init
    always {
        WellformedRepo
    }

    Branching[Repo.firstRoot]
    next_state 
    next_state {
        some br: Root | {
          br in Repo.firstRoot.outgoingBranches
          Merge[Repo.firstRoot, br]
        }
    }
}

run testBranchMerge for exactly 4 CommitNode, exactly 2 Root, 7 Int


pred testBranchCommitMerge {
    Init
    always {
        WellformedRepo
    }
    // Commit
    Branching[Repo.firstRoot]
    next_state Commit[Repo.firstRoot]
    next_state next_state Merge[Repo.firstRoot]
}

run testBranchCommitMerge for exactly 4 CommitNode, exactly 2 Root, 5 Int

