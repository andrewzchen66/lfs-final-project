#lang forge/temporal

open "operations.frg"
open "sigs.frg"

option max_tracelength 2
option min_tracelength 2

pred testCommitOneNode {
    // Init
    // WellformedRepo
    // validCommitIDs
    // validBranchIDs
    // Commit[Repo.mainBranch]

    Init

    WellformedRepo
    //Commit[Repo.mainBranch]
    
}

run testCommitOneNode for exactly 1 Branch, 2 CommitNode, 3 Int


-- valid commit: 
-- 1) deletion: keep track of set of files, if missing a file (size of set), then commit is valid
-- 2) creation: keep track of set of files, if an additional file (size of set compared to prev commit (next)), then commit is valid
-- 3) modification: if there exists a file in set of files where state is dirty, then we can commit, then change state of file back to clean

// pred validCommit {
//     WellformedBranch[c.currBranch]
//     -- previous commits remain unchanged (fix syntax)
//     all c: CommitNode | {
//         -- to define a valid commit, there must be a change in file state
//         c.fileState' != c.fileState

        
//         c in c.currentBranch.commits implies c' in c.currentBranch.commits

//         -- add only one commit

//     }

//     // New Commit
//     some c: CommitNode | {
        
//     }

//     all c: CommitNode | {
//         c = c.
//     }
// }

-- valid merge:
-- same # of files and within that, same file ids