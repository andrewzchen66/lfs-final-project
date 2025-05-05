#lang forge/temporal
option max_tracelength 5
option min_tracelength 2

// ========== Core Signatures ==========
sig User {}

var sig Branch {
    branchID: one Int,
    root: one Root,
    commits: set CommitNode,
    prev: lone Branch
}

var sig CommitNode {
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


// ========== Initial State ==========
pred Init {
    // Only main branch exists initially
    Branch = Repo.mainBranch
    
    // Main branch setup
    Repo.mainBranch.commits = Root
    Repo.mainBranch.root = Root
    Repo.mainBranch.prev = none
    Repo.mainBranch.branchID = 0
    
    // Root commit setup
    Root.next = none
    Root.currentBranch = Repo.mainBranch
    Root.commitID = 0
    Root.fileState = 0
    
    // No other commits exist initially
    CommitNode = Root
}

// ========== Helper Functions ==========
fun maxBranchID : one Int {
    max[Branch.branchID]
}

fun maxCommitID : one Int {
    max[CommitNode.commitID]
}

// ========== Branching Operation ==========
pred doBranch {
    // Pre-conditions
    some from: Branch | {
        some latest: from.commits | {
            latest.next = none  // Branch from tip
            
            // State changes
            one newBr: Branch | {
                newBr not in Branch
                
                // Calculate next ID safely
                newBr.branchID' = maxBranchID + 1
                
                newBr.root' = latest
                newBr.commits' = latest
                newBr.prev' = from
                latest.currentBranch' = newBr
                
                // Frame conditions
                all b: Branch - newBr | {
                    b.commits' = b.commits
                    b.prev' = b.prev
                    b.branchID' = b.branchID
                    b.root' = b.root
                }
                all c: CommitNode - latest | {
                    c.next' = c.next
                    c.fileState' = c.fileState
                    c.currentBranch' = c.currentBranch
                    c.commitID' = c.commitID
                }
            }
        }
    }
}

// ========== Commit Operation ==========
pred doCommit {
    some b: Branch | {
        some parent: b.commits | {
            parent.next = none
            one new: CommitNode | {
                new not in CommitNode
                
                // Calculate next ID safely
                let nextID = maxCommitID + 1 | {
                    new.commitID' = nextID
                }
                
                // State changes
                parent.next' = new
                new.next' = none
                b.commits' = b.commits + new
                new.currentBranch' = b
                new.fileState' = parent.fileState + 1
                
                // Frame conditions
                all otherB: Branch - b | {
                    otherB.commits' = otherB.commits
                }
                all c: CommitNode - new | {
                    c.next' = c.next
                    c.fileState' = c.fileState
                    c.currentBranch' = c.currentBranch
                }
            }
        }
    }
}

// ========== Temporal Trace ==========
pred traces {
    Init
    always {
        doBranch or doCommit
    }
}

// ========== Example Run ==========
pred pls {
    traces
    eventually {
        #Branch = 2 and #CommitNode = 3
    }
}

run pls for exactly 2 Branch, 3 CommitNode, 5 Int