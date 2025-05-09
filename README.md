# Temporal Forge Model of Git-like Version Control System

## Overview

Welcome to our **Temporal Forge** model simulating the core operations of a Git-like version control system. This includes committing, branching, merging, and reverting within a repository. While real-world version control systems offer a wide array of features, our model focuses on these four to ensure and demonstrate key properties:

- **Correctness** of system transitions over time
- **Structural consistency**
- **History integrity**

## Structure and Design Decisions

Each of the primary operations—**Commit**, **Branch**, **Merge**, and **Revert**—is defined as a predicate that transforms the state of the repository (`Repo`) while preserving key invariants:

- Commit uniqueness
- Chain connectivity
- Immutability of past history

We intentionally **excluded file modification tracking** (such as dirty vs. clean files) to keep the model tractable. Instead, each `CommitNode` includes a `fileState` field—an integer used to distinguish content between commits.

### Core Components

The repository is structured using the following **signatures (`sig`) and fields**:

- **`CommitNode`**: Represents a commit
  - `next: lone CommitNode` – Enforces sequential commit structure
  - `outgoingBranches: set Root` – Allows multiple branches from a commit
  - `fileState: Int` – Identifies commit content

- **`Root`**: Represents branch heads; extends `CommitNode`
  - `firstRoot: one Root` – First root created in the repository

- **`totalCommits: set CommitNode`** – Tracks active commits
- **`Unused`**: Distinguishes `CommitNode`s not yet in use
- **`unusedCommits`**: Pool of `CommitNode`s to be added to the repository

### Test Suites

Our implementation includes three test files:

- **`prop-testing.frg`**: Validates core invariants and behavior
- **`unit-testing.frg`**: Tests individual operations
- **`traces.frg`**: Simulates full repository workflows

## Tradeoffs and Alternatives Considered

### Merge Semantics

- If two parent commits have **the same `fileState`**, the merged commit retains that `fileState`.
- If they differ, a **new unique `fileState`** is created.
- We considered letting one branch override the other’s `fileState`, but this would misrepresent merge conflict resolution.

Instead of relying solely on `fileState` to verify Merge correctness, we ensure the **newly created commit is reachable from both parent branches**.

### Single `next` Field

Although we debated separate `next` fields for `Commit` vs. `Merge`, we chose a single `next` pointer, as branching and committing **never occur simultaneously** in our model.

### Branch Behavior

Branch creation consumes a timestep and **copies the `fileState`** of the commit it's branched from. This avoids implying that a change occurred at branch time.

## Assumptions and Scope

To ensure tractability, we made the following assumptions:

- **Fixed number of commit nodes**, recycled from an `Unused` pool
- **One new commit per operation**
- **Linear chains**, with branching and merging explicitly modeled
- **No concurrent operations**; all actions occur sequentially
- **No deletions, force-pushes, or history rewrites**

## Key Results and Proofs

- **Integrity of version control**: All commit `fileState`s are retained and retrievable via revert (within the same branch)
- **Idempotent `fileState`**: Repeating branch and merge operations results in a `fileState` consistent with pre-branch state; repeated reverts yield consistent `fileState`s

## Interpreting the Model

The test files (`prop-testing.frg`, `unit-testing.frg`, `traces.frg`) generate visualizable repository instances.

- Use the **Cope-and-Drag YAML visualization tool** for temporal stepping
- Visualization is also compatible with **Sterling**

---

*This model is designed to explore correctness and verifiability in version control operations through the lens of Temporal Forge.*
