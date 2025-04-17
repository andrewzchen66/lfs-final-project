#lang forge/temporal

one sig User {}

one sig Repo {
    user: one User
    root: lone Root
    branches: pfunc Int -> Branch
    totalcommits: set CommitNode
}

sig Branch {
    branchID: Int
    root: one Root
    commits: set CommitNode
    prev: lone Branch
}

abstract sig File {
    id: Int -- unique identifier for each file
}

abstract sig Modified extends File {}

sig CommitNode {
    commitID: Int
    currentBranch: one Branch
    next: lone Commit -- sequential commits
    branches: set Branch
    content: set File -- maps number of commit to files
}

one sig Root extends CommitNode {}


