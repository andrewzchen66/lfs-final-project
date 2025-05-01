#lang forge/temporal
// option bitwidth 9

open "sigs.frg"

// establish the initial state of the repo
pred Init {
    // there exists a user
    Repo.user != none

    // main branch exists alone in repo
    Repo.mainBranch in Repo.branches
    Repo.branches = Repo.mainBranch

    // main branch only has root commit
    Repo.mainBranch.commits = Repo.mainBranch.root

    // total commits accounts for the root commit
    Repo.totalCommits = Repo.mainBranch.root

    // verify root node in main branch has no successors
    Repo.mainBranch.root.next = none

    // verify that root branch is the main branch
    Repo.mainBranch.root.currentBranch = Repo.mainBranch

    // verify that mainBranch does not have a parent branch
    Repo.mainBranch.prev = none
}

// helper predicate to ensure integrity of repo's DAG structure
pred Acyclic {
    no c: CommitNode | {
        c in c.^next
    }
}

// establish wellformedness for all branches, or if all commits stem linearly from the root
pred WellformedBranch[b: Branch] {
    // confirm DAG structure
    Acyclic

    // branch has a root
    b.root in b.commits

    all c: b.commits | {
        // all commits are valid and reachable
        c in b.root.*next 

        // all commits belong to this branch
        c.currentBranch = b
    }
}

   
pred WellformedRepo {
    // Each branch has at least its root commit
    all b: Repo.branches | {
        // wellformedness for all branches
        WellformedBranch[b]
    }
    
    // totalCommits accounts for all existing commits
    Repo.branches.commits in Repo.totalCommits
    
    // every commit (except root) has exactly one parent
    all c: CommitNode - Root | lone c.next
    
    // branches are properly linked via prev
    all b: Repo.branches - Repo.mainBranch | one b.prev
    
    // all brances are reachable from main branch roots
    Repo.branches in Repo.mainBranch.*prev

    all c: CommitNode | {
        // all commits are accounted for
        c in Repo.totalCommits

        // all commits are reachable from main branch root, no floating commits
        c in Repo.mainBranch.root.*next
    }
}

-- abstraction: all commits are presumed to be valid, file modification is out of scope
-- abstraction: concurrent committing modeled through interleaved commits in Forge (any branch modified at a given time)
// TODO: concurrent commiting-- add set Branches
// pred Commit[branch: Branch] | {
//     WellformedRepo

//     one c: CommitNode | {
//         c' not in branch.commits
//         c.currentBranch != none
//     }

//     // Only one new commit
//     branch.commits in branch.commits'
//     #{branch.commits'} = #{branch.commits} + 1

//     // The new commit is
// }



run { WellformedRepo } for exactly 1 Branch, exactly 1 CommitNode, exactly 1 User 


// pred Branch[branchId] {

//     Commit[b1, b2: Branch]
// }

// pred Merge[featureBranch, destinationBranch: Int] {

// }

// pred Revert[commitId: Int] {

// }

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
