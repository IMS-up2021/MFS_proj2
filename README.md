# MFS Project 2 – Verified File Utilities in Dafny

## Group Elements

* up202205038 – Miguel Lopes Guerrinha
* up202206205 – Gonçalo Cunha Marques
* up202108852 – Inês Martin Soares

---

## Introduction

The goal of this project was to develop verified file-manipulation utilities using Dafny and its I/O extensions provided in `Io.dfy` and `IoNative.cs`. The project focuses on the specification, implementation, and formal verification of programs that interact with files while maintaining functional correctness through preconditions, postconditions, invariants, and auxiliary lemmas.

The project consists of two challenges:

1. A verified file line-reversal utility (`reverse.dfy`).
2. A verified implementation of the `grep` utility (`grep.dfy`), using the Knuth-Morris-Pratt (KMP) string matching algorithm.

---

## Challenge 1 – Verified File Reverse Utility

### Objective

Implement a command-line utility:

```text
./reverse <source> <destination>
```

that copies the contents of the source file into the destination file while reversing the order of its lines, provided that the destination file does not already exist.

### Design

The implementation is based on the following functions:

* `IndexOf` – finds the position of the newline character in a byte sequence;
* `SplitLines` – decomposes a file into a sequence of lines;
* `JoinLines` – reconstructs file contents from a sequence of lines;
* `ReverseSeq` – reverses a sequence;
* `ReverseFileContent` – combines the previous functions to produce the reversed file.

### Verification

Several auxiliary lemmas were required:

* `JoinLinesAppendNonEmptyLast`
* `ReverseFileContentLenLE`

These lemmas establish properties about sequence concatenation and prove that the size of the generated file never exceeds the size of the original file.

The implementation also includes verified `ReadFile` and `WriteFile` procedures with specifications guaranteeing:

* successful reads return exactly the file contents;
* successful writes create the destination file with the intended contents;
* the environment remains in a consistent state after file operations.

---

## Challenge 2 – Verified Grep Utility

### Objective

Implement a command-line utility:

```text
./grep <word> <file>
```

which outputs:

```text
YES: n
```

if the first occurrence of `word` appears at position `n`, and

```text
NO
```

otherwise.

### Design Decisions

The assignment suggests beginning with a naive quadratic-time algorithm and implementing the Knuth-Morris-Pratt (KMP) algorithm for full marks.

Our implementation follows this approach:

1. A naive search algorithm (`NaiveSearch`) is specified and used as the functional specification of the expected behaviour.
2. The executable implementation uses the Knuth-Morris-Pratt algorithm.

The implementation includes:

* `WordToBytes` – converts command-line input into byte sequences;
* `NaiveSearch` and `NaiveSearchFrom` – formal specifications of pattern matching behaviour;
* `ComputePrefix` – constructs the prefix table required by KMP;
* `KMPSearch` – performs efficient pattern matching in linear time.

### Verification

The implementation required:

* loop invariants to maintain correctness during prefix table construction and pattern matching;
* proofs of index bounds and memory safety;
* auxiliary lemmas, such as `SeqExtendLemma`, to establish properties of the prefix table.

The verified implementation guarantees that:

* all sequence accesses are within bounds;
* the computed indices are valid;
* the search result is correct with respect to the specified behaviour.

---

## Algorithms Used

### Line Reversal

The reverse utility follows the pipeline:

```text
File contents
    ↓
SplitLines
    ↓
ReverseSeq
    ↓
JoinLines
    ↓
Reversed file contents
```

### String Matching

The grep utility uses the Knuth-Morris-Pratt algorithm:

```text
Pattern
    ↓
ComputePrefix
    ↓
KMPSearch
    ↓
Position of first occurrence (or -1)
```

KMP was chosen because it improves the worst-case complexity from the quadratic complexity of the naive approach to linear complexity:

* Naive search: O(nm)
* KMP search: O(n + m)

where `n` is the size of the text and `m` is the size of the pattern.

---

## Verification Techniques Used

Throughout the project, we made extensive use of Dafny's verification mechanisms:

* preconditions (`requires`);
* postconditions (`ensures`);
* loop invariants (`invariant`);
* termination arguments (`decreases`);
* auxiliary lemmas and assertions;
* ghost variables for reasoning about file states.

These techniques allowed us to formally prove the functional correctness and safety properties of both programs.

---

## Conclusion

This project provided practical experience in the development of verified software systems using Dafny. We implemented two file-processing utilities and formally proved their correctness. In particular, the project highlighted the distinction between specification and implementation, as demonstrated by specifying pattern matching with a naive algorithm while implementing an efficient solution using Knuth-Morris-Pratt.
