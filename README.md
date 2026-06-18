# MFS Project 2 – Verified File Utilities in Dafny

## Group Elements

* up202205038 – Miguel Lopes Guerrinha
* up202206205 – Gonçalo Cunha Marques
* up202108852 – Inês Martin Soares

---

## Introduction

The goal of this project was to develop verified file-manipulation utilities using Dafny and its I/O extensions provided in `Io.dfy` and `IoNative.cs`. The project focuses on the specification, implementation, and formal verification of programs that interact with files while maintaining functional correctness through preconditions, postconditions, invariants, and auxiliary lemmas.


---

## Challenge 1 – Verified File Reverse Utility

### Objective

To implement a utility that accepts a source file and a destination file as command-line arguments. The program safely reads the source file, reverses the sequence of its lines, and writes the resulting output to the new destination file, handling all necessary file existence and I/O safety checks along the way.

### Design

Rather than attempting an in-place array swap—which introduces highly complex swapping invariants—the `ReverseLines` algorithm allocates a secondary buffer of the exact same length as the input. It iterates backward from the end of the input buffer, using pointers to isolate individual lines (delimited by the newline byte `10`), and securely copies those specific chunks forward into the output buffer. Furthermore, exact typecasting (e.g., `nat32`, `int32`) was utilized to seamlessly bridge Dafny's unbounded integers with the strict C# native memory types defined in `IoNative.cs`.

### Verification

The core verification challenge was proving memory safety during the array transcriptions. This was solved by linking the read and write pointers algebraically with a "magic" invariant: `invariant out_idx == input.Length - line_end`. This guarantees to the Dafny verifier that the output index mathematically cannot exceed the remaining buffer space. Additionally, we enforced strict I/O state-machine integrity by explicitly validating the success of `.Read()` and `.Write()` operations before executing `.Close()`, ensuring the environment (`env.ok.ok()`) never entered an illegal state.

---

## Challenge 2 – Verified Grep Utility

### Objective
To develop a verified string-matching utility that searches for a specified word within a file. The project includes two distinct implementations: a baseline naive algorithm (enhanced to support UNIX-style matching line output for bonus points) and an optimized linear-time Knuth-Morris-Pratt (KMP) algorithm.

### Design Decisions

* **Naive Algorithm (UNIX-Style Output):** To achieve the bonus points of printing entire matching lines rather than a simple boolean output, the architecture was modularized. It decouples the logic into `GrepLines` (a scanner that isolates line boundaries) and `ContainsWord` (a bounded string-matcher). This separation of concerns prevents the combinatorial explosion of invariants that would occur if line-tracking and pattern-matching were handled in a single massive loop. 
* **KMP Algorithm:** The architecture is split into a preprocessing phase (`ComputeLPS`) to map the pattern's jump table, and a search phase (`KMPSearch`). 
* Both utilities implement safe character-to-byte conversion protocols for the command-line arguments to prevent overflow crashes when scanning non-ASCII text.

### Verification

State-machine verifiers like Dafny natively struggle with pointers that occasionally jump backward or branch unexpectedly. 
* **Naive Validation:** The modular design allowed for clean memory constraints. The matcher uses the invariant `txtStart + i + j <= txtEnd` to mathematically guarantee the search head will never read past the designated line chunk boundary.
* **KMP Validation:** Relied heavily on complex termination metrics to prove the loops would not run infinitely. We used weighted sums, such as `decreases 2 * (N - i) + j`. This proved that even when the search pointer `j` jumps backward via the LPS array, the dominant forward progress of `i` enforces a strict overall downward trend. We also bounded the LPS array (`0 <= lps[k] <= k`) to prove the backward jumps would never cause an `IndexOutOfBounds` exception.

---

## Algorithms Used

1. **Chunk-Based Line Reversal:** An $O(N)$ transcription algorithm that scans data backward and copies isolated byte chunks forward to construct a reversed line sequence without risking in-place data corruption.
2. **Naive String Matching:** A straightforward nested-loop approach with an $O(N \times M)$ complexity. It was adapted to run within strict mathematical boundary subsets for safe line-by-line scanning.
3. **Knuth-Morris-Pratt (KMP):** An advanced linear-time ($O(N + M)$) pattern matching algorithm utilizing a Longest Proper Prefix which is also Suffix (LPS) array. The LPS acts as a jump table to bypass redundant character comparisons upon encountering a mismatch.

---

## Verification Techniques Used

Throughout the project, we made extensive use of Dafny's verification mechanisms:

* preconditions (`requires`);
* postconditions (`ensures`);
* loop invariants (`invariant`);
* termination arguments (`decreases`);

These techniques allowed us to formally prove the functional correctness and safety properties of the programs.

---

## Conclusion

This project provided practical experience in the development of verified software systems using Dafny. We implemented three file-processing utilities and formally proved their correctness. In particular, the project highlighted the distinction between specification and implementation, as demonstrated by specifying pattern matching with a naive algorithm while implementing an efficient solution using Knuth-Morris-Pratt.
