#lang forge/temporal
open "sigs-other.frg"

option min_tracelength 5
option max_tracelength 5



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
        // TODO: reachable may be auto-evaluating to false, double check this
        reachable[c, Repo.firstRoot, next, outgoingBranches] => (c in Repo.totalCommits and c not in Unused.unusedCommits)
        // not reachable[c, Repo.firstRoot, next, outgoingBranches] => (c not in Repo.totalCommits and c in Unused.unusedCommits)

        // If commit in Repo
        c in Repo.totalCommits => {
            // 1) commitNode's states remain same
            c.fileState != none
            c.fileState = c.fileState'
            // c.next != none => c.next = c.next'
            // c.outgoingBranches = c.outgoingBranches'

            // 2) Once a commit has been used, it will always be in use
            c in Repo.totalCommits'

            // 3) all commits are reachable from a root; no floating commits
            some r: Root | {
                r in Repo.totalCommits
                c in r.*next
            }

            // 4) Outgoing Branch Roots must all be in use
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

// Move a CommitNode from Unused to Repo.totalCommits
pred AddOneCommitNode {
    Unused.unusedCommits' in Unused.unusedCommits
    Repo.totalCommits in Repo.totalCommits'
    #{Unused.unusedCommits - Unused.unusedCommits'} = 1
    Unused.unusedCommits - Unused.unusedCommits' = Repo.totalCommits' - Repo.totalCommits
}

-- abstraction: all commits are presumed to be valid, file modification is out of scope
-- abstraction: concurrent committing modeled through interleaved commits in Forge (any branch modified at a given time)
// TODO: concurrent commiting-- add set Branches
pred Commit[r: Root] {
    AddOneCommitNode
    
    // Add new CommitNode to the most recent CommitNode
    some parent: Repo.totalCommits | {
        // parent is the parent of the new commit
        (parent in r.*next and parent.next = none)
        
        // Update parent.next' to the new commit , keep everything else the same
        parent.next' = (Unused.unusedCommits - Unused.unusedCommits')
        parent.outgoingBranches' = parent.outgoingBranches
        parent.fileState' = parent.fileState

        // Update New commit's fields
        parent.next'.next' = none
        parent.next'.outgoingBranches' = none
        // New commit has different fileState than any earlier commit in this branch
        parent.next'.fileState' != none
        no prevCommit: r.*next | {
            prevCommit.fileState = parent.next'.fileState'
        }
        // parent.next'.fileState' != parent.fileState

        // All other CommitNodes' fields should remain the same
        all c: Repo.totalCommits | {
            not (c = parent or c = parent.next') => {
                c.next' = c.next
                c.outgoingBranches = c.outgoingBranches'
                c.fileState = c.fileState'
            }
        }
    }

}

// A version of Commit I created with no parameters. Kinda works, haven't tested it much. 
// It just contrains that a single Commit will occur at this timestep, but you have no control on which branch it occurs
// Probably we can delete
pred Commit2 {
    AddOneCommitNode

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
        }
    }
}

pred Branching[r: Root] {
    AddOneCommitNode
    
    // Add new branching CommitNode to the most recent CommitNode
    // let newRoot = Unused.unusedCommits - Unused.unusedCommits' | {

    // } 
    
    one newRoot: Root | {
        newRoot = Unused.unusedCommits - Unused.unusedCommits'
        one c: Repo.totalCommits | {
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

// parentCommit is the CommitNode that the branch we want to merge branches off of.
// We create a new CommitNode that 
// NOTE: In our merge, we always override target branch's filestate with our to-be-merged branch's fileState
pred Merge[parentCommit: CommitNode] {
    
    AddOneCommitNode

    one newCommit: CommitNode | { // The new Commit we are adding after Merge
        newCommit = Unused.unusedCommits - Unused.unusedCommits'
        newCommit.next' = none
        newCommit.outgoingBranches' = none

        one targetCommit: CommitNode | { // The Commit we are merging into
            (targetCommit in parentCommit.*next and targetCommit.next = none)
            targetCommit.next' = newCommit // Point to newCommit!
            targetCommit.outgoingBranches' = targetCommit.outgoingBranches
            targetCommit.fileState' = targetCommit.fileState

            one rootToMerge: parentCommit.outgoingBranches | { // The root that we're merging into
                // Keep all rootToMerge fields the same
                one commitToMerge: Repo.totalCommits | { // commit that we are merging
                    (commitToMerge in rootToMerge.*next and commitToMerge.next = none)
                    commitToMerge.next' = newCommit // Point to newCommit!
                    commitToMerge.outgoingBranches' = commitToMerge.outgoingBranches
                    commitToMerge.fileState' = commitToMerge.fileState

                    // Override newCommit's fileState with the merged Commit's filestate
                    newCommit.fileState' = commitToMerge.fileState 

                    // Keep OtherCommits the same
                    all c: Repo.totalCommits | {
                        not (c = newCommit or c = targetCommit or c = commitToMerge) => {
                            c.next' = c.next
                            c.outgoingBranches = c.outgoingBranches'
                            c.fileState = c.fileState'
                        }
                    }
                }
            }
        }
    }
    
}


// revertingTo is the CommitNode whose state we want to revert to
pred Revert[revertingTo: CommitNode] {
    AddOneCommitNode
    
    one parent: Repo.totalCommits | {
        (parent in revertingTo.*next and parent.next = none)
        parent.next' = (Unused.unusedCommits - Unused.unusedCommits')
        parent.outgoingBranches' = parent.outgoingBranches
        parent.fileState' = parent.fileState
        
        parent.next'.next' = none
        parent.next'.outgoingBranches' = none
        parent.next'.fileState' = revertingTo.fileState // New commit has the same fileState as revertingTo

        // All other CommitNodes' fields should remain the same
        all c: Repo.totalCommits | {
            not (c = parent or c = parent.next') => {
                c.next' = c.next
                c.outgoingBranches = c.outgoingBranches'
                c.fileState = c.fileState'
            }
        }
    }
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

// run testBranchOneNode for exactly 4 CommitNode, exactly 2 Root, 5 Int

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