#lang forge/temporal
// option bitwidth 9

option max_tracelength 2
option min_tracelength 2

sig Branch {
    // branchID: one Int,
    var root: one Root,
    var commits: set CommitNode,
    var prev: lone Branch
}

sig CommitNode {
    // commitID: one Int,
    var currentBranch: lone Branch,
    var next: lone CommitNode, -- sequential commits
    var outgoingBranches: set Root,
    var prevBranch: lone Branch,
    var fileState: lone Int -- unique identifier for each file state
}

sig Root extends CommitNode {}

one sig Repo {
    var mainBranch: one Branch,
    var branches: set Branch,
    var totalCommits: set CommitNode
}

one sig Unused {
    var unusedCommits: set CommitNode,
    var unusedBranches: set Branch
}

// abstract sig Modified extends File {}


