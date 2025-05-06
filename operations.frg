#lang forge/temporal

open "sigs.frg"

-- abstraction: all commits are presumed to be valid, file modification is out of scope
-- abstraction: concurrent committing modeled through interleaved commits in Forge (any branch modified at a given time)
// TODO: concurrent commiting-- add set Branches
// pred Commit[b: Branch] {
//     // repo needs to be wellformed before proceeding
//     WellformedRepo

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

pred Branching[b: Branch, from: Branch] {
    // pre 
    WellformedBranch[b]
    WellformedBranch[from]

    some from.commits
    b not in Branch
    b.branchID not from.branchID

    some latest: from.commits | {
        latest.next = none  // must be tip of the branch
        // set up new branch
        b.root = latest
        b.commits = latest
        b.prev = from
        
        // all existing branches remain unchanged
        all existing: Branch - b | {
            existing.commits' = existing.commits
            existing.prev' = existing.prev
        }
        
        // all commits remain unchanged
        CommitNode' = CommitNode
        all c: CommitNode | {
            c.next' = c.next
            c.fileState' = c.fileState
        }
    }
}

// When you run git revert <commit>, Git creates a new commit that inverts the changes introduced by <commit>—without altering history (unlike reset). It does so by computing a patch that undoes the diff introduced by the target commit.
pred Revert[b: Branch, commitId: Int] {

}

// both branches 
pred Merge[featureBranch, destinationBranch: Branch] {
    // both branches must be well-formed and distinct before merging
    featureBranch != destinationBranch
    WellformedBranch[featureBranch]
    WellformedBranch[destinationBranch]

    // find the tips of both branches
    some featureTip: CommitNode | {
        featureTip in featureBranch.commits
        featureTip.next = none
    }
    some destinationTip : CommitNode | {
        destinationTip in destinationBranch.commits
        destinationTip.next = none
    }

    // create a single new commit merge off destination branch
    one new: CommitNode | {
        new not in Repo.totalCommits

        // both parents/tips point to new commit
        featureTip.next' = new
        destinationTip.next' = new

        // ensure new commmit is the latest leaf node off the destination branch
        new.next' = none
        new.currentBranch' = destinationBranch
        destinationBranch.commits' = destinationBranch.commits + new

        // record new commit in total commits
        Repo.totalCommits' = Repo.totalCommits + new

        // ensure commit is valid by checking filestates
        new.fileState' != destinationTip.fileState
        new.fileState' != featureTiip.fileState

        // all other old commits and branches are untouched
        all oldCommits: CommitNode - new | {
            oldCommits.fileState' = oldCommit.fileState
        }

        all oldBranches: Branch - destinationBranch | {
            oldBranches.commits' = oldBranches.commits
        }
    }


}