#lang forge/temporal

open "main.frg"


// Property-based testing:
// ______________________________________________________
// The following should hold before and after every operation:
// Unique and Immutable identifiers-- Branch IDs and CommitIDs are same
// DAG properties-- entire tree is Acyclic
// Every node is Reachable from Commitnode
// Initial Commit has no parents
// ______________________________________________________

// Unit Tests?
// Idempotence for Revert


