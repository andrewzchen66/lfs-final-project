#lang forge/temporal

open "sigs.frg"

-- constrain Root so that there is no branching (initial state)

-- constrain valid repo: has user, 

-- valid commit: 
-- 1) deletion: keep track of set of files, if missing a file (size of set), then commit is valid
-- 2) creation: keep track of set of files, if an additional file (size of set compared to prev commit (next)), then commit is valid
-- 3) modification: if there exists a file in set of files where state is dirty, then we can commit, then change state of file back to clean

-- valid merge:
-- same # of files and within that, same file ids


pred Init {
    // Size of main branch 
}


pred WellformedRepo {
    all b: Branch | {
        b in Repo.branches
    }
    all c: CommitNode | {
        c in Repo.totalCommits
    }

    // DAG constraints at Repo level
    // - All branch is reachable from main branch

    all b: Branch | {
    }
    WellfornedBranch[Repo.mainBranch]

    all c: CommitNode | {
        -- c is reachable from the mainBranch.root
    }
}

pred WellformedBranch[b: Branch] {
    // DAG 
}

pred validCommit {
    WellformedBranch[c.currBranch]
    -- previous commits remain unchanged (fix syntax)
    all c: CommitNode | {
        -- to define a valid commit, there must be a change in file state
        c.fileState' != c.fileState

        
        c in c.currentBranch.commits implies c' in c.currentBranch.commits

        -- add only one commit

    }

    // New Commit
    some c: CommitNode | {
        
    }

    all c: CommitNode | {
        c = c.
    }
}

-- single commit
// TODO: concurrent commiting-- add set Branches
pred Commit[branch: Branch] | {
    Wellformed
    one c: CommitNode | {
        c' not in branch.commits
    }
    

    // Only one new commit
    branch.commits in branch.commits'
    #{branch.commits'} = #{branch.commits} + 1

    // The new commit is
}

pred Branch[branchId] {

    Commit[b1, b2: Branch]
}

pred Merge[featureBranch, destinationBranch: Int] {

}

pred Revert[commitId: Int] {

}


run {
    Init
    Commit[]
}