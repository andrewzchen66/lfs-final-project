#lang forge/temporal

open "sigs.frg"

// Move a CommitNode from Unused to Repo.totalCommits
pred AddOneCommitNode {
    Unused.unusedCommits' in Unused.unusedCommits
    Repo.totalCommits in Repo.totalCommits'
    #{Unused.unusedCommits - Unused.unusedCommits'} = 1
    Unused.unusedCommits - Unused.unusedCommits' = Repo.totalCommits' - Repo.totalCommits
}

-- abstraction: all commits are presumed to be valid, file modification is out of scope
-- abstraction: concurrent committing modeled through interleaved commits in Forge (any branch modified at a given time)
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
}

// parentCommit is the CommitNode that the branch we want to merge branches off of.
// We create a new CommitNode at the end of parentCommit's branch with the merged state of the branch we merge
// NOTE: In our merge, we always override target branch's filestate with our to-be-merged branch's fileState
pred Merge[parentCommit: CommitNode] {
    // TODO: Currently we are unable to specify the exact branch to merge, 
    // we just grab an arbitrary rootToMerge parentCommit.outgoingBranches.
    // It would involve adding a parameter for the Root that we want to merge.
    // I didn't do this because I didn't know how to test this, as the only root
    // I can access is Repo.firstRoot, which you obviously can't merge
    
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

-- abstraction: all commits are presumed to be valid, file modification is out of scope
-- abstraction: concurrent committing modeled through interleaved commits in Forge (any branch modified at a given time)
// TODO: concurrent commiting-- add set Branches
// pred Commit[b: Branch] {
//     // repo needs to be wellformed before proceeding
//     //WellformedRepo

//     // assign a parent node for the incoming commit
//     some parent: CommitNode | {
//         parent in b.commits
//         parent.next = none

//         // account for only a single commit
//         one new: CommitNode | {
//             new not in Repo.totalCommits

//             // link new commit to chain
//             parent.next' = new
//             new.next' = none

//             // assign new commit to correct branch
//             b.commits' = b.commits + new
//             new.currentBranch' = b

//             // track commit in total repo commits
//             Repo.totalCommits' = Repo.totalCommits + new

//             // to ensure a valid commit, fileState needs to change
//             new.fileState' != parent.fileState

//             // all other commit nodes are untouched
//             all old: CommitNode - new | { old.fileState' = old.fileState }

//             // all other branches other than the one that the new node belongs to is unchanged
//             all branches: Branch - b | { branches.commits' = branches.commits }
//         }
//     }

// }


// pred Branching[b: Branch, from: Branch] {
//     // pre 
//     WellformedBranch[b]
//     WellformedBranch[from]

//     some from.commits
//     b not in Branch
//     b.branchID != from.branchID

//     some latest: from.commits | {
//         latest.next = none  // must be tip of the branch
//         // set up new branch
//         b.root = latest
//         b.commits = latest
//         b.prev = from
        
//         // all existing branches remain unchanged
//         all existing: Branch - b | {
//             existing.commits' = existing.commits
//             existing.prev' = existing.prev
//         }
        
//         // all commits remain unchanged
//         CommitNode' = CommitNode
//         all c: CommitNode | {
//             c.next' = c.next
//             c.fileState' = c.fileState
//         }
//     }
// }

// When you run git revert <commit>, Git creates a new commit that inverts the changes introduced by <commit>—without altering history (unlike reset). It does so by computing a patch that undoes the diff introduced by the target commit.
// pred Revert[b: Branch, commitId: Int] {

// }

// both branches 
// pred Merge[featureBranch, destinationBranch: Branch] {
//     // both branches must be well-formed and distinct before merging
//     featureBranch != destinationBranch
//     WellformedBranch[featureBranch]
//     WellformedBranch[destinationBranch]

//     // create a single new commit merge off destination branch
//     one new: CommitNode | {
//         new not in Repo.totalCommits

//         // both parents/tips point to new commit
//         featureTip.next' = new
//         destinationTip.next' = new

//         // ensure new commmit is the latest leaf node off the destination branch
//         new.next' = none
//         new.currentBranch' = destinationBranch
//         destinationBranch.commits' = destinationBranch.commits + new

//         // record new commit in total commits
//         Repo.totalCommits' = Repo.totalCommits + new

//         // find the tips of both branches
//         some featureTip: CommitNode | {
//             featureTip in featureBranch.commits
//             featureTip.next = none
//         }
//         some destinationTip : CommitNode | {
//             destinationTip in destinationBranch.commits
//             destinationTip.next = none
//         }

//         // ensure commit is valid by checking filestates
//         new.fileState' != destinationTip.fileState
//         new.fileState' != featureTiip.fileState

//         // all other old commits and branches are untouched
//         all oldCommits: CommitNode - new | {
//             oldCommits.fileState' = oldCommit.fileState
//         }

//         all oldBranches: Branch - destinationBranch | {
//             oldBranches.commits' = oldBranches.commits
//         }
//     }
// }

// create end condition to eventually reach

// create traces, init, condiitions for the middle, then the end pred
// conditions in the trace: for x number of commits, the repo is acyclic

// do a revert, push, then a pop

// unit tests for core functions (branching, committing, reverting, etc)

// use preds for proerties of git to prove important parts of git (acyclic, etc)

// at the end, show what we really learned by modeling the system

// focus on presentation!!!
// prepare to answer any questions, make a readme

// design check: where do we call branching in the predicates when we run
