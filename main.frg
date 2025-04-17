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
