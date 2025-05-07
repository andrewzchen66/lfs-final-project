#lang forge/temporal
open "sigs-other.frg"

option min_tracelength 2
option max_tracelength 2



// establish the initial state of the repo
pred Init {
    // total commits accounts for the root commit
    Repo.totalCommits = Repo.firstRoot
    
    // Initialize firstRoot fields
    Repo.firstRoot.next = none
    Repo.firstRoot.outgoingBranches = none
    Repo.firstRoot.prevBranchNode = none

    // // Set all other Nodes as unused
    all c: CommitNode | {
        c != Repo.firstRoot => c in Unused.unusedCommits
    }
}

// helper predicate to ensure integrity of repo's DAG structure
pred Acyclic {
    no c: CommitNode | {
        c in c.^next
        // TODO: what is the correct way to implement reachable over two fields, one of them being a set?
        // reachable[c, c, next, outgoingBranches]
    }

    all c: CommitNode | {
        no branchRoot: c.outgoingBranches | {
            c in branchRoot.*next
        }
    } 
}

// establish wellformedness for all branches, or if all commits stem linearly from the root
pred WellformedBranch[r: Root] {
    // For now, we only allow branching off of main branch

    // (r = Repo.firstRoot) or (some parent: CommitNode | {
    //     parent in Repo.firstRoot.*next
    //     r.prevBranchNode = parent
    // })


    // confirm DAG structure
    Acyclic

    // branch is reflected in Repo fields
    r in Repo.totalCommits

    // First Root stays the same
    Repo.firstRoot = Repo.firstRoot'
    
    no otherRoot: Root | {
        // Only one root allowed for this branch
        otherRoot in r.^next 

        // No cycles from prevBranchNode
    }

    // root shouldn't have a parent CommitNode
    no c: CommitNode | {
        c.next = r
    }
}

// establish wellformedness for the entire repo
pred WellformedRepo {

    all c: CommitNode | {
        // all commits are either in Repo or Unused
        (c in Repo.totalCommits and c not in Unused.unusedCommits) or (c not in Repo.totalCommits and c in Unused.unusedCommits)

        // Reachable from firstRoot means it's in use
        reachable[c, Repo.firstRoot, next, outgoingBranches] => (c in Repo.totalCommits and c not in Unused.unusedCommits)
        // not reachable[c, Repo.firstRoot, next, outgoingBranches] => (c not in Repo.totalCommits and c in Unused.unusedCommits)

        // If commit in Repo
        c in Repo.totalCommits => {
            // 1) commitNode's states remain same
            c.fileState != none
            c.fileState = c.fileState'
            // c.next != none => c.next = c.next'
            // c.outgoingBranches = c.outgoingBranches'

            // 2) The commit will always be in use
            c in Repo.totalCommits'

            // 3) all commits are reachable from a root; no floating commits
            some r: Root | {
                r in Repo.totalCommits
                c in r.*next
            }

            // 4) Outgoing Branch Roots must all be in 
            c.outgoingBranches in Repo.totalCommits
        }

        // If commit Unused, set CommitNode fields to none
        c in Unused.unusedCommits => {
            c.next = none
            c.outgoingBranches = none
            c.fileState = none
        }
    }

    all r: Root | {
        // All active roots (branches) are wellformed
        r in Repo.totalCommits => {
            // Wellformed
            WellformedBranch[r]

            // All non-firstRoots are all properly linked to a different CommitNode
            r != Repo.firstRoot => {
                // TODO: For now, only branch off main branch
                r.prevBranchNode in Repo.firstRoot.*next
                r.prevBranchNode in Repo.totalCommits
                r in r.prevBranchNode.outgoingBranches
            }
        }

        r in Unused.unusedCommits => {
            r.prevBranchNode = none
        }
    }

    Repo.firstRoot.prevBranchNode = none
}

-- abstraction: all commits are presumed to be valid, file modification is out of scope
-- abstraction: concurrent committing modeled through interleaved commits in Forge (any branch modified at a given time)
// TODO: concurrent commiting-- add set Branches
pred Commit[r: Root] {
    // Move a CommitNode from Unused to Repo.totalCommits
    Unused.unusedCommits' in Unused.unusedCommits
    Repo.totalCommits in Repo.totalCommits'
    #{Unused.unusedCommits - Unused.unusedCommits'} = 1
    Unused.unusedCommits - Unused.unusedCommits' = Repo.totalCommits' - Repo.totalCommits

    // Add new CommitNode to the most recent CommitNode
    some c: Repo.totalCommits | {
        // c is the parent of the new commit
        (c in r.*next and c.next = none)
        c.next' = (Unused.unusedCommits - Unused.unusedCommits')
        c.next'.next' = none
        c.next'.outgoingBranches' = none
        c.next'.fileState' != none
        c.next'.fileState' != c.fileState // New commit has different fileState than parent
    }

    // All other CommitNodes' fields should remain the same
    all c: Repo.totalCommits | {
        not (c in r.*next and c.next = none) => {
            c.next' = c.next
            c.outgoingBranches = c.outgoingBranches'
            c.fileState = c.fileState'
        }

        // every active commit stays in totalCommits
        c in Repo.totalCommits'
    }
}


pred Commit2 {
    
    // // Move a CommitNode from Unused to Repo.totalCommits
    Unused.unusedCommits' in Unused.unusedCommits
    Repo.totalCommits in Repo.totalCommits'
    #{Unused.unusedCommits - Unused.unusedCommits'} = 1
    Unused.unusedCommits - Unused.unusedCommits' = Repo.totalCommits' - Repo.totalCommits

    // Add new CommitNode to the most recent CommitNode
    one parent: Repo.totalCommits | {
        // c is the parent of the new commit
        (parent.next = none)
        parent.next' = (Unused.unusedCommits - Unused.unusedCommits')
        parent.next'.next' = none
        parent.next'.outgoingBranches' = none
        parent.next'.fileState' != none
        parent.next'.fileState' != parent.fileState // New commit has different fileState than parent

        // All other CommitNodes' fields should remain the same
        all c: Repo.totalCommits | {
            (c != parent) => {
                c.next' = c.next
                c.outgoingBranches = c.outgoingBranches'
                c.fileState = c.fileState'
            }

            // every active commit stays in totalCommits
            c in Repo.totalCommits'
        }
    }
}

pred Branching[r: Root] {
    // Move a CommitNode from Unused to Repo.totalCommits
    Unused.unusedCommits' in Unused.unusedCommits
    Repo.totalCommits in Repo.totalCommits'
    #{Unused.unusedCommits - Unused.unusedCommits'} = 1
    Unused.unusedCommits - Unused.unusedCommits' = Repo.totalCommits' - Repo.totalCommits
    
    // Add new branching CommitNode to the most recent CommitNode
    // let newRoot = Unused.unusedCommits - Unused.unusedCommits' | {

    // } 
    
    one newRoot: Root | {
        newRoot = Unused.unusedCommits - Unused.unusedCommits'
        some c: Repo.totalCommits | {
            // c is the origin of the new branch
            (c in r.*next and c.next = none)
            c.outgoingBranches' = c.outgoingBranches + newRoot

            newRoot.next' = none
            newRoot.outgoingBranches' = none
            newRoot.fileState' = c.fileState // New root commit has same fileState as parent
            newRoot.prevBranchNode' = c // point prevBranchNode to parent CommitNode
        }
    }

    all c: Repo.totalCommits | {
        not (c in r.*next and c.next = none) => {
            c.next' = c.next
            c.outgoingBranches = c.outgoingBranches'
            c.fileState = c.fileState'
        }
    }
    

    // ________________________________________________________________

    // // Update CommitNode fields
    // all c: Repo.totalCommits | {
    //     (c in r.*next and c.next = none) => {
    //         // c is the parent of the new commit
    //         c.next' = (Unused.unusedCommits - Unused.unusedCommits')
    //         c.next'.next' = none
    //         c.next'.outgoingBranches' = none
    //         c.next'.fileState' != none
    //         c.next'.fileState' != c.fileState // New commit has different fileState than parent
    //     } else {
    //         // All other states' field should remain the same
    //         c.next = c.next'
    //         c.outgoingBranches = c.outgoingBranches'
    //         c.fileState = c.fileState'
    //     }
    // }
}


pred testCommitOneNode {
    Init
    always{
        WellformedRepo
        // Commit2
        // Commit[Repo.firstRoot]
    }
    // Commit
    eventually {
        Commit[Repo.firstRoot]
        // Commit2
    }

    //     #{Unused.unusedCommits} = 0
    // }
    // Commit[Repo.firstRoot]
    // Commit[Repo.firstRoot]

    // always Commit[Repo.firstRoot] until #{Unused.unusedCommits} = 0
}

// Get rid of all parameters in the operations. For example Commit predicate would just ensure that at this timestep a commit somewhere would happen, so our run would call something like:
// pred genericTest {
//     Init
//     always{
//         WellformedRepo
//         Commit or Branch or Merge or …
//     }
// }

// This would align more with how we did the goats_and_wolves.frg assignment
// run testCommitOneNode for exactly 4 CommitNode, 5 Int


pred testBranchOneNode {
    Init
    always{
        WellformedRepo
        // Commit2
        // Commit[Repo.firstRoot]
    }
    // Commit
    eventually {
        Branching[Repo.firstRoot]
        // Commit2
    }
}

run testBranchOneNode for exactly 4 CommitNode, exactly 2 Root, 5 Int



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