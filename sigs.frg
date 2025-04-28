#lang forge/temporal

sig User {}

one sig Root extends CommitNode {}

one sig Repo {
    user: one User
    mainBranch: Branch
    branches: pfunc Int -> Branch
    totalcommits: set CommitNode
}

sig Branch {
    branchID: Int
    root: one Root
    commits: set CommitNode
    prev: lone Branch
}

// abstract sig Modified extends File {}

sig CommitNode {
    commitID: Int
    currentBranch: one Branch
    next: lone Commit -- sequential commits
    branches: set Branch
    fileState: Int -- unique identifier for each file state
}


