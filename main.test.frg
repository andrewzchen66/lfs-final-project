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
    example pos_Init is {Init} for {
        User = `u
        Branch = `b
        CommitNode = `c1 + `c2
        Int = `i0 + `i1 + `i2
        Root = `root
        Repo = `r
        `r.mainBranch = `b
    }
}

// pred testOneCommit {
//   Init
//   some b: Branch | b = Repo.mainBranch and Commit[b]
//   WellformedRepo
//   Acyclic
// }
// run testOneCommit for exactly 1 Branch, exactly 1 User, 2 CommitNode, 3 Int

// test suite for OneCommit {
//     example pos_OneCommit is {testOneCommit} for {
//         User = `u
//         Branch = `b
//         CommitNode = `c1 + `c2
//         Int = `i0 + `i1 + `i2
//         Root = `root
//         Repo = `r
//         `r.mainBranch = `b
//     }
// }

// test suite for TwoCommits {
//     example pos_TwoCommits is {testTwoCommits} for {
//         User = `u
//         Branch = `b
//         CommitNode = `c1 + `c2 + `c3
//         Int = `i0 + `i1 + `i2 + `i3
//         Repo.mainBranch = `b
//     }
// }

// test suite for Branching {
//     example pos_Branching is {testBranching} for {
//         User = `u
//         Branch = `main + `feature
//         CommitNode = `c1 + `c2
//         Int = `i0 + `i1 + `i2 + `i3
//         Repo.mainBranch = `main
//     }
// }

// test suite for BranchThenCommit {
//     example pos_BranchThenCommit is {testBranchThenCommit} for {
//         User = `u
//         Branch = `main + `feature
//         CommitNode = `c1 + `c2 + `c3
//         Int = `i0 + `i1 + `i2 + `i3 + `i4
//         Repo.mainBranch = `main
//     }
// }

// test suite for UniqueCommitIDs {
//     example pos_UniqueCommitIDs is {testUniqueCommitIDs} for {
//         User = `u
//         Branch = `main
//         CommitNode = `c1 + `c2 + `c3
//         Int = `i0 + `i1 + `i2 + `i3 + `i4
//         Repo.mainBranch = `main
//     }
// }

// test suite for RevertAfterCommit {
//     example pos_RevertAfterCommit is {testRevertAfterCommit} for {
//         User = `u
//         Branch = `main
//         CommitNode = `c1 + `c2
//         Int = `i0 + `i1 + `i2 + `i3
//         Repo.mainBranch = `main
//     }
// }

// test suite for MergeFeatureIntoMain {
//     example pos_MergeFeatureIntoMain is {testMergeFeatureIntoMain} for {
//         User = `u
//         Branch = `main + `feature
//         CommitNode = `c1 + `c2 + `c3 + `c4
//         Int = `i0 + `i1 + `i2 + `i3 + `i4
//         Repo.mainBranch = `main
//     }
// }

// test suite for ConcurrentCommits {
//     example pos_ConcurrentCommits is {testConcurrentCommits} for {
//         User = `u
//         Branch = `main + `feature
//         CommitNode = `c1 + `c2 + `c3 + `c4
//         Int = `i0 + `i1 + `i2 + `i3 + `i4
//         Repo.mainBranch = `main
//     }
// }


// pred testInit {
//   Init
//   WellformedRepo
//   validCommitIDs
//   validBranchIDs
// }
// run testInit for exactly 1 Branch, exactly 1 User, 1 CommitNode, 2 Int



// pred testTwoCommits {
//   Init
//   some b: Branch | b = Repo.mainBranch and Commit[b]
//   next some b: Branch | b = Repo.mainBranch and Commit[b]
//   always WellformedRepo
//   always Acyclic
// }
// run testTwoCommits for exactly 1 Branch, exactly 1 User, 3 CommitNode, 4 Int

// pred testBranching {
//   Init
//   some b: Branch, from: Branch | from = Repo.mainBranch and Branching[b, from]
//   WellformedRepo
//   Acyclic
// }
// run testBranching for exactly 2 Branch, exactly 1 User, 2 CommitNode, 4 Int

// pred testBranchThenCommit {
//   Init
//   some b: Branch, from: Branch | from = Repo.mainBranch and Branching[b, from]
//   next some b2: Branch | Commit[b2]
//   always WellformedRepo
//   always Acyclic
// }
// run testBranchThenCommit for exactly 2 Branch, exactly 1 User, 3 CommitNode, 5 Int

// pred testUniqueCommitIDs {
//   Init
//   some b: Branch | Commit[b]
//   next some b: Branch | Commit[b]
//   validCommitIDs
// }
// run testUniqueCommitIDs for exactly 1 Branch, exactly 1 User, 3 CommitNode, 5 Int

// pred testRevertAfterCommit {
//   Init
//   some b: Branch | b = Repo.mainBranch and Commit[b]
//   next some b: Branch | Revert[b]
//   always WellformedRepo
//   always Acyclic
// }
// run testRevertAfterCommit for exactly 1 Branch, exactly 1 User, 2 CommitNode, 4 Int

// pred testMergeFeatureIntoMain {
//   Init
//   some f: Branch, m: Branch | {
//     m = Repo.mainBranch
//     Branching[f, m]
//   }
//   next some f: Branch | Commit[f]
//   next some m: Branch | Commit[m]
//   next some f, m: Branch | Merge[f, m]
//   always WellformedRepo
//   always Acyclic
// }
// run testMergeFeatureIntoMain for exactly 2 Branch, exactly 1 User, 4 CommitNode, 5 Int

// pred testConcurrentCommits {
//   Init
//   some f: Branch, m: Branch | {
//     m = Repo.mainBranch
//     Branching[f, m]
//   }

//   // Interleaved commits
//   next some f: Branch | Commit[f]
//   next some m: Branch | Commit[m]
//   next some f: Branch | Commit[f]

//   always WellformedRepo
//   always Acyclic
//   validCommitIDs
// }
// run testConcurrentCommits for exactly 2 Branch, exactly 1 User, 4 CommitNode, 5 Int

