#lang forge/temporal

open "operations.frg"
open "sigs.frg"
open "main.frg"

option max_tracelength 2
option min_tracelength 2

// Property-based testing: should hold before and after an operation (branch, merge, revert)
// ______________________________________________________
// The following should hold before and after every operation:
// Unique and Immutable identifiers-- Branch IDs and CommitIDs are same
// DAG properties-- entire tree is Acyclic
// Every node is Reachable from Commitnode
// Initial Commit has no parents
// ______________________________________________________

// Unit Tests?
// Idempotence for Revert
// init states
// more properties for merging


test suite for Init {
    // assert {InitSAT and Init} is sat for exactly 1 Repo, exactly 4 CommitNode, exactly 1 Root, exactly 3 Int
    // assert {InitUNSAT and Init} is unsat for exactly 1 Repo, exactly 4 CommitNode, exactly 1 Root, exactly 3 Int
}

// SAT: one firstRoot, others unused
pred InitSAT {
    some r: Repo, fr: CommitNode | {
        r.totalCommits = fr
        r.firstRoot = fr

        fr.next = none
        fr.outgoingBranches = none
        fr.prevBranchNode = none

        all c: CommitNode - fr | c in Unused.unusedCommits
    }
}

// UNSAT: one firstRoot, others are used in next fields of firstRoot but shouldn't be 
pred InitUNSAT {
    some r: Repo, fr: CommitNode, c: CommitNode | {
        r.totalCommits = fr
        r.firstRoot = fr

        fr.next = none
        fr.outgoingBranches = none
        fr.prevBranchNode = none

        c != fr
        c not in Unused.unusedCommits
    }
}

test suite for AddOneCommitNode {
    // assert {AddOneCommitNodeSAT and AddOneCommitNode} is sat for exactly 1 Repo, exactly 3 CommitNode, exactly 1 Root, exactly 3 Int
    // assert {AddOneCommitNodeUNSAT and AddOneCommitNode} is unsat for exactly 1 Repo, exactly 3 CommitNode, exactly 1 Root, exactly 3 Int
}

// SAT: adding a commitNode into Repo reduces the number of unusedCommits by 1
pred AddOneCommitNodeSAT {
    Init
    one c: Unused.unusedCommits | {
        Unused.unusedCommits' = Unused.unusedCommits - c
        Repo.totalCommits' = Repo.totalCommits + c
    }
}

// UNSAT: can’t move anything from unused to repo because none are unused
pred AddOneCommitNodeUNSAT {
    Init
    Unused.unusedCommits = none
    some Repo.totalCommits
    Unused.unusedCommits' = Unused.unusedCommits
}

test suite for Commit {
    // assert {CommitSAT} is sat for exactly 1 Repo, exactly 4 CommitNode, exactly 1 Root, exactly 3 Int
    // assert {CommitUNSAT} is unsat for exactly 1 Repo, exactly 4 CommitNode, exactly 1 Root, exactly 3 Int
}

// SAT: can commit from inital state
pred CommitSAT {
    Init
    some r: Root | Commit[r]
}

// UNSAT: no unused commits to add
pred CommitUNSAT {
    Init
    Unused.unusedCommits = none
    some r: Root | Commit[r]
}

// test suite for Commit2 {
//     assert {Commit2SAT} is sat for exactly 1 Repo, exactly 4 CommitNode, exactly 1 Root, exactly 3 Int
//     assert {Commit2UNSAT} is unsat for exactly 1 Repo, exactly 4 CommitNode, exactly 1 Root, exactly 3 Int
// }
// pred Commit2SAT {
//     Init
//     Commit2
// }

// pred Commit2UNSAT {
//     Init
//     Unused.unusedCommits = none
//     Commit2
// }

test suite for Branching {
    // assert {BranchingSAT} is sat for exactly 1 Repo, exactly 4 CommitNode, exactly 2 Root, exactly 3 Int
    // assert {BranchingUNSAT} is unsat for exactly 1 Repo, exactly 2 CommitNode, exactly 2 Root, exactly 3 Int
}

// SAT: sanity 
pred BranchingSAT {
    Init
    some r: Root | Branching[r]
}

// UNSAT: cannot branch with no unusedCommits 
pred BranchingUNSAT {
    Init
    Unused.unusedCommits = none
    some r: Root | Branching[r]
}

test suite for Merge {
    // assert {MergeSAT} is sat for exactly 1 Repo, exactly 4 CommitNode, exactly 2 Root, exactly 3 Int
    // assert {MergeUNSAT} is unsat for exactly 1 Repo, exactly 4 CommitNode, exactly 2 Root, exactly 3 Int
}

// not working
pred MergeSAT {
    Init
    // manually add a child to allow branching for merge
    some parent: CommitNode, r: Root | {
        next_state Branching[r] 
        next_state next_state {
            parent in Repo.totalCommits
            parent.next = none
            parent.outgoingBranches = r
            Merge[parent]
        }
    }
}

pred MergeUNSAT {
    Init
    Unused.unusedCommits = none
    some c: CommitNode | Merge[c]
}

test suite for Revert {
    assert {RevertSAT} is sat for exactly 1 Repo, exactly 4 CommitNode, exactly 2 Root, exactly 3 Int
    assert {RevertUNSAT} is unsat for exactly 1 Repo, exactly 4 CommitNode, exactly 2 Root, exactly 3 Int
}

pred RevertSAT {
    Init
    some c: CommitNode | {
        c in Repo.totalCommits
        some p: CommitNode | {
            p in c.*next and p.next = none
            Revert[c]
        }
    }
}

// UNSAT parent.next future timesteps do not match what's expected... EXPLAIN 
pred RevertUNSAT {
    Init
    some c: CommitNode | Revert[c]
    one parent: Repo.totalCommits | {
        (parent in revertingTo.*next and parent.next = none)
        parent.next' = (Unused.unusedCommits - Unused.unusedCommits')
        parent.outgoingBranches' = parent.outgoingBranches
        parent.fileState' = parent.fileState
        
        parent.next'.next' != none
        parent.next'.outgoingBranches' != none
        parent.next'.fileState' != revertingTo.fileState // new commit should have the same fileState as revertingTo, testing when it doesn't
    }
}



