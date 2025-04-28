#lang forge/temporal
open "sigs.frg"

-- Initial repository: a single user, one main branch with only its root commit
fact Init {
    some repo: Repo |
        -- user exists
        repo.user != none
        -- main branch is registered in repository
        repo.mainBranch in repo.branches
        -- main branch has only its root commit
        repo.mainBranch.commits = repo.mainBranch.root
        -- totalCommits tracks exactly that root commit
        repo.totalCommits = repo.mainBranch.commits
        -- root has no successor
        repo.mainBranch.root.next = none
        -- root knows its branch
        repo.mainBranch.root.currentBranch = repo.mainBranch
        -- mainBranch has no parent
        repo.mainBranch.prev = none
}

-- No cycles in the commit graph
pred Acyclic {
    no c: CommitNode | c in c.^next
}

-- A branch is well-formed when its commits form a linear, acyclic chain from its root
pred WellformedBranch[b: Branch] {
    -- root must belong to commits
    b.root in b.commits
    -- commits are all reachable via next from root
    b.commits = b.root.*next
    -- no cycles
    Acyclic
    -- every commit knows its branch
    all c: b.commits | c.currentBranch = b
}

-- A repository is well-formed when every branch is well-formed and totalCommits aggregates all commits
pred WellformedRepo {
    some repo: Repo |
        -- every branch in repo.branches plus the main branch is well-formed
        all b: repo.branches + repo.mainBranch | WellformedBranch[b]
        -- totalCommits equals the union of all branch commits
        repo.totalCommits = (repo.branches + repo.mainBranch).commits
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
