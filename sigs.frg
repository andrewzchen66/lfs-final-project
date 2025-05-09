#lang forge/temporal
// option bitwidth 9

// option max_tracelength 5
// option min_tracelength 5

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

////////////////////////////////////////////////////////////

// establish the initial state of the repo
pred Init {
    // total commits accounts for the root commit
    Repo.totalCommits = Repo.firstRoot
    
    // Initialize firstRoot fields
    Repo.firstRoot.next = none
    Repo.firstRoot.outgoingBranches = none
    Repo.firstRoot.prevBranchNode = none

    // // Set all other Nodes as unused
    all c: CommitNode | {
        c != Repo.firstRoot => c in Unused.unusedCommits
    }
}

////////////////////////////////////////////////////////////////////////////////////////
// PROPERTY TESTING!!!!!

// helper predicate to ensure integrity of repo's DAG structure
pred Acyclic {
    no c: CommitNode | {
        c in c.^(next + outgoingBranches)
        // the correct way to implement reachable over two fields, one of them being a set
    }

    all c: CommitNode | {
        no branchRoot: c.outgoingBranches | {
            c in branchRoot.*next
        }
    } 
}

// should not be sat
pred Cyclic {
    some c: CommitNode | {
        c in c.^(next + outgoingBranches)
    }
}

// valid and disjoint commit file states
pred UniqueCommits {
    all disj c1, c2: Repo.totalCommits | c1.fileState != c2.fileState
}

// should not be sat, there exists at least two different commit nodes with the same file states
pred NonUniqueCommits {
    some disj c1, c2: Repo.totalCommits | c1.fileState = c2.fileState
}

// all commit nodes are reachable from the main node and are accounted for
pred Reachable { 
    all c: CommitNode | {
        c in Repo.totalCommits implies reachable[c, Repo.firstRoot, next, outgoingBranches]
        //c in Repo.mainBranch.root.*next
    }
}

// should not be sat
pred NotReachable { 
    some c: CommitNode | {
        c in Repo.totalCommits and not reachable[c, Repo.firstRoot, next, outgoingBranches]
        //c not in Repo.mainBranch.root.*next
    }
}

// root commit has no parents, ensuring its root properties
pred RootNoParents {
    no c: CommitNode | {
        Repo.firstRoot in c.next
    }
}

// should not be sat, root commit is not actually the root commit and has parents
pred RootWithParents {
    some c: CommitNode | {
        Repo.firstRoot in c.next
    }
}

// integrity of commit history is maintained: no commit deletion allowed
pred NoCommitDeletion {
    all c: CommitNode | {
        c in Repo.totalCommits implies c in Repo.totalCommits'
    }
}

// should not be say, again, the integrity of the commit history is compromised b/c commit deletion is allowed
pred CommitDeletionAllowed {
    some c: CommitNode | {
        c in Repo.totalCommits
        c not in Repo.totalCommits'
    }
}

// existing ids do not change across operations, commit history is maintained
pred ImmutableHistory {
    all c: Repo.totalCommits | {
        c.fileState' = c.fileState
    }

    all c: CommitNode | {
        (c in Repo.totalCommits) and (c in Repo.totalCommits')
    }
    
}

// should not be sat, existing commit file states could change across operations, interrupting the integrity of commit history
pred MutableHistory {
    some c: CommitNode | {
        c.fileState' != c.fileState
        (c in Repo.totalCommits) and not (c in Repo.totalCommits')
    }
}

// git invariants that must hold regardless of transition state/operation
pred Invariants {
    Acyclic
    UniqueCommits
    Reachable
    RootNoParents
}

// git invariants that must hold after an operation (commit, branch, merge or revert)
pred PostOperationInvariants {
    Invariants
    ImmutableHistory
    NoCommitDeletion
}

////////////////////////////////////////////////////////////////////////////////////////

// establish wellformedness for all branches, or if all commits stem linearly from the root
pred WellformedBranch[r: Root] {
    // confirm DAG structure
    Acyclic

    // branch is reflected in Repo fields
    r in Repo.totalCommits

    // First Root stays the same
    Repo.firstRoot = Repo.firstRoot'
    
    no otherRoot: Root | {
        // Only one root allowed for this branch
        otherRoot in r.^next         
    }

    // root shouldn't have a parent CommitNode
    no c: CommitNode | {
        c.next = r
    }
}

// establish wellformedness for the entire repo
pred WellformedRepo {
    all c: CommitNode | {
        // all commits are either in Repo or Unused
        (c in Repo.totalCommits and c not in Unused.unusedCommits) or (c not in Repo.totalCommits and c in Unused.unusedCommits)

        // Reachable from firstRoot means it's in use
        reachable[c, Repo.firstRoot, next, outgoingBranches] => (c in Repo.totalCommits and c not in Unused.unusedCommits)

        // If commit in Repo
        c in Repo.totalCommits => {
            // 1) commitNode's states remain same
            c.fileState != none
            c.fileState = c.fileState'

            // 2) Once a commit has been used, it will always be in use
            c in Repo.totalCommits'

            // 3) all commits are reachable from a root; no floating commits
            some r: Root | {
                r in Repo.totalCommits
                c in r.*next
            }

            // 4) Outgoing Branch Roots must all be in use
            c.outgoingBranches in Repo.totalCommits
        }

        // If commit Unused, set CommitNode fields to none
        c in Unused.unusedCommits => {
            c.next = none
            c.outgoingBranches = none
            c.fileState = none
        }
    }

    all r: Root | {
        // All active roots (branches) are wellformed
        r in Repo.totalCommits => {
            // Wellformed
            WellformedBranch[r]

            // All non-firstRoots are all properly linked to a different CommitNode
            r != Repo.firstRoot => {
                r.prevBranchNode in Repo.totalCommits
                r in r.prevBranchNode.outgoingBranches
            }
        }

        r in Unused.unusedCommits => {
            r.prevBranchNode = none
        }
    }

    Repo.firstRoot.prevBranchNode = none
}
