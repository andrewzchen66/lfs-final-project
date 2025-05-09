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

// creates new branch off of a specified root
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

// We create a new CommitNode at the end of parentCommit's branch with the merged state of the branch we merge
pred Merge[parentCommit: CommitNode, rootToMerge: Root] {
  // you can only merge an existing branch
  rootToMerge in parentCommit.outgoingBranches

  // pick the new merge‑commit and the two tips that will point at it
  some newCommit, intoTip, fromTip: CommitNode | {
    newCommit in Unused.unusedCommits
    Unused.unusedCommits' = Unused.unusedCommits - newCommit
    Repo.totalCommits' = Repo.totalCommits + newCommit

    // initialize the new merge‑commit
    newCommit.next' = none
    newCommit.outgoingBranches' = none

    // intoTip is tip of the parent commit of the branch you're merging into
    intoTip in parentCommit.*next and intoTip.next = none
    intoTip.next' = newCommit
    intoTip.outgoingBranches'= intoTip.outgoingBranches
    intoTip.fileState' = intoTip.fileState

    // get the tip of the root you're merging from
    fromTip in rootToMerge.*next and fromTip.next = none
    fromTip.next' = newCommit
    fromTip.outgoingBranches'= fromTip.outgoingBranches
    fromTip.fileState' = fromTip.fileState

    // pick the merge commit’s fileState from the “from” tip
    (intoTip.fileState = fromTip.fileState) implies ((newCommit.fileState' = intoTip.fileState) or (newCommit.fileState' = fromTip.fileState))
    (intoTip.fileState != fromTip.fileState) implies ((newCommit.fileState' != intoTip.fileState) and (newCommit.fileState' != fromTip.fileState))

    // all other commits should be untouched
    all c: CommitNode | c not in (newCommit + intoTip + fromTip) implies {
      c.next' = c.next
      c.outgoingBranches' = c.outgoingBranches
      c.fileState' = c.fileState
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