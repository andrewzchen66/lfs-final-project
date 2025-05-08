#lang forge/temporal

open "operations.frg"
open "sigs.frg"

option max_tracelength 2
option min_tracelength 2

// I want this to be the ideal test format, but things like always Commit return UNSAT
// pred genericTest {
//     Init
//     always{
//         WellformedRepo
//         Commit or Branch or Merge or …
//     }
// }
// This would align more with how we did the goats_and_wolves.frg assignment

pred testCommitOneNode {
    Init
    always{
        WellformedRepo
        // TODO: how come we get Unsat when we try to always Commit?
        // Commit[Repo.firstRoot]
    }
    Commit[Repo.firstRoot]
}
// run testCommitOneNode for exactly 4 CommitNode, 5 Int


pred testBranchOneNode {
    Init
    always{
        WellformedRepo
    }
    eventually {
        Branching[Repo.firstRoot]
    }
}

run testBranchOneNode for exactly 4 CommitNode, exactly 2 Root, 5 Int

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
    next_state Merge[Repo.firstRoot]
}

// run testBranchMerge for exactly 4 CommitNode, exactly 2 Root, 5 Int


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
// run testBranchCommitMerge for exactly 4 CommitNode, exactly 2 Root, 5 Int


pred testCommitCommitRevert {
    Init
    always {
        WellformedRepo
    }
    Commit[Repo.firstRoot]
    next_state Commit[Repo.firstRoot]
    next_state next_state Revert[Repo.firstRoot]
}
// run testCommitCommitRevert for exactly 4 CommitNode, exactly 1 Root, exactly 3 Int

// pred testCommitOneNode {
//     // Init
//     // WellformedRepo
//     // validCommitIDs
//     // validBranchIDs
//     // Commit[Repo.mainBranch]

//     Init

//     WellformedRepo
//     //Commit[Repo.mainBranch]
    
// }

// run testCommitOneNode for exactly 1 Branch, 2 CommitNode, 3 Int


-- valid commit: 
-- 1) deletion: keep track of set of files, if missing a file (size of set), then commit is valid
-- 2) creation: keep track of set of files, if an additional file (size of set compared to prev commit (next)), then commit is valid
-- 3) modification: if there exists a file in set of files where state is dirty, then we can commit, then change state of file back to clean

-- valid merge:
-- same # of files and within that, same file ids