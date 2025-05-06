#lang forge/temporal
// option bitwidth 9

option max_tracelength 2
option min_tracelength 2

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


// establish the initial state of the repo
pred Init {
    // there exists a user
    Repo.user != none

    // main branch exists alone in repo
    Repo.mainBranch in Repo.branches
    Repo.branches = Repo.mainBranch

    // main branch only has root commit
    Repo.mainBranch.commits = Repo.mainBranch.root

    // total commits accounts for the root commit
    Repo.totalCommits = Repo.mainBranch.root

    // verify root node in main branch has no successors
    Repo.mainBranch.root.next = none

    // verify that root branch is the main branch
    Repo.mainBranch.root.currentBranch = Repo.mainBranch

    // verify that mainBranch does not have a parent branch
    Repo.mainBranch.prev = none
}

////////////////////////////////////////////////////////////////////////////////////////
// PROPERTY TESTING!!!!!

// helper predicate to ensure integrity of repo's DAG structure
pred Acyclic {
    no c: CommitNode | {
        c in c.^next
    }
}

// valid and disjoint commit IDs
pred UniqueCommitIDs {
    all disj c1, c2: Repo.totalCommits | c1.commitID != c2.commitID
}

// valid and disjoint branch IDs
pred UniqueBranchIDs {
    all disj b1, b2: Repo.branches | b1.branchID != b2.branchID
}

// all commit nodes are reachable from the main node and are accounted for
pred Reachable { 
    all c: CommitNode | {
        c in Repo.mainBranch.root.*next
    }
}

// root commit has no parents, ensuring its root properties
pred RootNoParents {
    no c: CommitNode | {
        Repo.mainBranch.root in c.next
    }
}

// existing ids do not change across operations, commit history is maintained
pred ImmutableIDs {
    all c: CommitNode | {
        c.commitID' = c.commitID
    }
    
    all b: Branch | {
        b.branchID' = b.branchID
    }
}


// integrity of commit history is maintained: no commit deletion allowed
pred NoCommitDeletion {
    all c: CommitNode | {
        c in Repo.totalCommits implies c in Repo.totalCommits'
    }
}

// git invariants that must hold regardless of transition state/operation
pred Invariants {
    Acyclic
    UniqueCommitIDs
    UniqueBranchIDs
    Reachable
    RootNoParents
    
}

// git invariants that must hold after an operation (commit, branch, merge or revert)
pred PostOperationInvariants {
    Invariants
    ImmutableIDs
    NoCommitDeletion
}

////////////////////////////////////////////////////////////////////////////////////////

// establish wellformedness for all branches, or if all commits stem linearly from the root
pred WellformedBranch[b: Branch] {
    // confirm DAG structure
    Acyclic

    // branch has a root
    b.root in b.commits

    all c: b.commits | {
        // all commits are valid and reachable
        c in b.root.*next 

        // all commits belong to this branch
        c.currentBranch = b
    }
}

// establish wellformedness for the entire repo
pred WellformedRepo {
    all b: Repo.branches | {
        // wellformedness for all branches
        WellformedBranch[b]
    }

    all c: CommitNode | {
        // all commits are accounted for
        c in Repo.totalCommits

        // all commits are reachable from main branch root, no floating commits
        c in Repo.mainBranch.root.*next
    }

    // totalCommits accounts for all existing commits
    Repo.branches.commits in Repo.totalCommits

    // each branch has at least its root commit
    all b: Repo.branches | b.root in b.commits
    
    // all commits in branches are accounted for in totalCommits
    Repo.branches.commits in Repo.totalCommits
    
    // commits form a DAG (no cycles)
    no c: CommitNode | c in c.^next
    
    // each commit (except root) has exactly one parent
    all c: CommitNode - Root | one c.next
    
    // branches are properly linked via prev
    all b: Repo.branches - Repo.mainBranch | one b.prev

    // no dangling branches (all branches reachable via prev from main)
    Repo.branches in Repo.mainBranch.*prev


}

