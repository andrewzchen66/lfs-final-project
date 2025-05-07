#lang forge/temporal

// open "sigs.frg"
open "sigs-simple.frg"
// open "operations.frg"

option max_tracelength 2
option min_tracelength 2


// establish the initial state of the repo
pred Init {
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
    // Repo.mainBranch.prev = none

    // All other CommitNodes aside from the main root should be in Unused
    all c: CommitNode - Repo.mainBranch.root | {
        c in Unused.unusedCommits
        c.currentBranch = none
        c.next = none
        c.outgoingBranches = none
        c.prevBranch = none
        c.fileState = none
    }

    // #{Repo.branches} = 1
    // #{Repo.totalCommits} = 1
    // all c: CommitNode | {
    //     c in Repo.totalCommits
    // }
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
    b.root in Repo.totalCommits
    b.root in b.commits

    // Only one root allowed for this branch
    no otherRoot: Root | {
        otherRoot in Repo.totalCommits
        (otherRoot in b.commits or otherRoot.currentBranch = b)
        otherRoot != b.root
    }

    // Branch commits are consistent with CommitNode pointers
    // all c: CommitNode | {
    //     c.currentBranch = b <=> c in b.commits
    // }

    all c: b.commits | {
        // all commits are valid and reachable
        c in b.root.*next 

        // all commits belong to this branch
        c.currentBranch = b
    }

    
}

// establish wellformedness for the entire repo
pred WellformedRepo {

    all c: CommitNode | {
        // all commits are accounted for
        (c in Repo.totalCommits and c not in Unused.unusedCommits) or (c not in Repo.totalCommits and c in Unused.unusedCommits)

        c in Repo.totalCommits => {
            // Once utilized in our model:
            // 1) fileState never changes
            c.fileState = c.fileState'
            // 2) The commit will always be in use
            c in Repo.totalCommits'
        }

        c in Unused.unusedCommits => {
            c.currentBranch = none
            c.next = none
            c.outgoingBranches = none
            c.prevBranch = none
            c.fileState = none
        }
    }


    // all commits are reachable from main branch root, no floating commits
        // c in Repo.mainBranch.root.*next
    all b: Repo.branches | {
        // b.commits in b.commits'
        // Repo.totalCommits in Repo.totalCommits'
        // wellformedness for all branches
        WellformedBranch[b]
    }


    // No root should have a parent
    all root: Root | {
        no c: CommitNode | {
            c.next = root
        }
    }

    // all commits in branches are accounted for in totalCommits
    Repo.branches.commits in Repo.totalCommits
    
    // commits form a DAG (no cycles)
    no c: CommitNode | c in c.^next
    
    // each commit (except root) has exactly one parent
    all c: CommitNode - Root | one c.next
    
    // branches are properly linked via prev
    all b: Repo.branches - Repo.mainBranch | one b.prev

    // no dangling branches (all branches reachable via prev from main)
    Repo.branches in Repo.mainBranch.*prev



}

// valid and disjoint commit IDs
// pred validCommitIDs {
//     all disj c1, c2: Repo.totalCommits | c1.commitID != c2.commitID
// }

// valid and disjoint branch IDs
// pred validBranchIDs {
//     all disj b1, b2: Repo.branches | b1.branchID != b2.branchID
// }

-- abstraction: all commits are presumed to be valid, file modification is out of scope
-- abstraction: concurrent committing modeled through interleaved commits in Forge (any branch modified at a given time)
// TODO: concurrent commiting-- add set Branches
pred Commit[b: Branch] {
    // repo needs to be wellformed before proceeding

    // #{b.commits' - b.commits} = 1

    some parent: CommitNode | {
        parent in b.commits
        parent.next = none

        // account for only a single commit
        one new: CommitNode | {
            // new not in b.commits
            // new = b.commits' - b.commits

            // // link new commit to chain
            // parent.next' = new
            // new.next' = none

            // // assign new commit to correct branch
            // b.commits' = b.commits + new
            // new.currentBranch' = b

            // // track commit in total repo commits
            // Repo.totalCommits' = Repo.totalCommits + new
        }
    }

    
    // Repo.totalCommits' - Repo.totalCommits = b.commits' - b.commits
    // all c: b.commits' - b.commits | {
    //     c.next = none
    // }

    // assign a parent node for the incoming commit
    // some parent: CommitNode | {
    //     parent in b.commits
    //     parent.next = none

    //     // account for only a single commit
    //     one new: CommitNode | {
    //         new not in Repo.totalCommits

    //         // link new commit to chain
    //         parent.next' = new
    //         new.next' = none

    //         // assign new commit to correct branch
    //         b.commits' = b.commits + new
    //         new.currentBranch' = b

    //         // track commit in total repo commits
    //         Repo.totalCommits' = Repo.totalCommits + new

    //         // to ensure a valid commit, fileState needs to change
    //         new.fileState' != parent.fileState

    //         // all other commit nodes are untouched
    //         all old: CommitNode - new | { old.fileState' = old.fileState }

    //         // all other branches other than the one that the new node belongs to is unchanged
    //         all branches: Branch - b | { branches.commits' = branches.commits }
    //     }
    // }

}



pred testCommitOneNode {
    // Init
    always{
        WellformedRepo
        // Commit[Repo.mainBranch]
        // validCommitIDs
        // validBranchIDs
    }
    // eventually {
    //     Commit[Repo.mainBranch]
    // }
}

run testCommitOneNode for exactly 1 Branch, exactly 2 CommitNode, 5 Int






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