#lang forge/temporal
// option bitwidth 9

// option min_tracelength 5
// option max_tracelength 5

sig CommitNode {
    // commitID: one Int,
    var next: lone CommitNode, -- sequential commits
    var outgoingBranches: set Root,
    var fileState: lone Int -- unique identifier for each file state
}


// Represents the first Commit in every Branch
sig Root extends CommitNode {
    // Pointer to parent branch's CommitNode that we've branched off of
    // For the firstRoot, points to none
    var prevBranchNode: lone CommitNode
}

one sig Repo {
    var firstRoot: one Root, // The first root CommitNode created in the Repo upon Init
    var totalCommits: set CommitNode // Set of all Commits that are currently being used in our model
}

one sig Unused {
    var unusedCommits: set CommitNode // Set of all all Commits that are NOT currently being used in our model
}

// abstract sig Modified extends File {}


