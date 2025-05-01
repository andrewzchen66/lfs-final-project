#lang forge/temporal
open "sigs.frg"

pred commit[pre, post: Repo, newCommit: CommitNode, modifiedFiles: set Int] {
    // Preconditions
    newCommit not in pre.totalCommits
    
    some currentBranch: pre.branches | {
        // The committer is working on an existing branch
        currentBranch in pre.branches
        newCommit.currentBranch = currentBranch
        
        // Post-state changes
        post.totalCommits = pre.totalCommits + newCommit
        post.branches = pre.branches
        
        // File state changes
        newCommit.fileState in modifiedFiles  // New file state
        some parent: CommitNode | {
            // Parent is current branch head
            no parent.next and parent in currentBranch.commits
            newCommit.next = parent          // Link to parent
            newCommit.fileState != parent.fileState  // Files must change
        }
        
        // Update branch commits
        currentBranch.commits = pre.currentBranch.commits + newCommit
        
        // Temporal frame conditions
        post.user = pre.user
        post.mainBranch = pre.mainBranch
        unchangedBranches[pre, post, currentBranch]
    }
    
    // Maintain commit uniqueness
    all c: CommitNode | c.commitID != newCommit.commitID
}
// Helper predicate for unchanged branches
pred unchangedBranches[pre, post: Repo, changedBranch: Branch] {
    all b: pre.branches | 
        b != changedBranch implies {
            b.commits = pre.b.commits
            b.root = pre.b.root
            b.prev = pre.b.prev
        }
}


pred commitOp[pre, post: Repo] {
    some newCommit: CommitNode, modifiedFiles: set Int |
        commit[pre, post, newCommit, modifiedFiles]
}
fact WellFormedCommits {
    // Initial commit exists
    one c: CommitNode | c = Root
    
    // All commits except Root have a parent
    all c: CommitNode - Root | one c.next
    
    // No commit cycles
    no c: CommitNode | c in c.^next
    
    // File states form a DAG
    no c: CommitNode | c.fileState in c.^next.fileState
}
test expect {
    commitIncrementsTotalCommits: {
        all pre, post: Repo | 
            commitOp[pre, post] implies #post.totalCommits = #pre.totalCommits + 1
    } is theorem
    
    commitChangesCurrentBranch: {
        all pre, post: Repo, newCommit: CommitNode |
            commit[pre, post, newCommit, some Int] implies
                newCommit in post.currentBranch.commits and
                newCommit not in pre.currentBranch.commits
    } is theorem
    
    commitPreservesOtherBranches: {
        all pre, post: Repo, b: Branch |
            commitOp[pre, post] and b != post.currentBranch implies
                b.commits.post = b.commits.pre
    } is theorem
}
-- Commit action: extend a branch by one new node
pred Commit[repo: Repo, b: Branch, newC: CommitNode] {
    WellformedRepo
    -- select an existing tip of branch b
    one tip: CommitNode | tip.next = none and tip in b.commits
    -- newC was not in repo before
    newC not in repo.totalCommits
    -- link the new commit
    tip.next = newC
    newC.next = none
    newC.currentBranch = b
    -- branch’s commits and repo’s totalCommits both grow by exactly newC
    b.commits' = b.commits + newC
    repo.totalCommits' = repo.totalCommits + newC
}

-- Example run: check that Init yields a well-formed repository
run CheckInit {
    Init and WellformedRepo
}

// design check: where do we call branching in the predicates when we run