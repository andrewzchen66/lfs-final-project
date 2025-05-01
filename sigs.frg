#lang forge/temporal
// option bitwidth 9

sig User {}

sig Branch {
    branchID: one Int,
    root: one Root,
    commits: set CommitNode,
    prev: lone Branch
}

sig CommitNode {
    commitID: one Int,
    currentBranch: one Branch,
    next: lone CommitNode, -- sequential commits
    commitBranches: set Branch,
    fileState: one Int -- unique identifier for each file state
}

one sig Root extends CommitNode {}

one sig Repo {
    user: one User,
    mainBranch: one Branch,
    branches: set Branch,
    totalCommits: set CommitNode
}


// abstract sig Modified extends File {}


