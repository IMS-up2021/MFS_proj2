### Challenge 2: Verified Grep Utility (Knuth-Morris-Pratt Algorithm)

## 1. Overview
This directory contains the verified implementation of the `grep` utility using the Knuth-Morris-Pratt (KMP) string-matching algorithm, written in Dafny. This implementation successfully satisfies the requirement for a verified linear-time pattern matching utility. 

The program takes a search word and a file name as command-line arguments. It safely processes the file system I/O and outputs `YES: n` (where `n` is the starting byte index of the match) or `NO` if the word is not found or an I/O error occurs.

## 2. Building and Execution

### Compilation
The project relies on `IoNative.cs` to bridge Dafny's trusted axiomatic interface with concrete C# file system operations. Compile the program using the provided `Makefile` or the Dafny CLI:

```bash
# Using the Makefile:
make compile DFY=grep.dfy

# Or using the Dafny CLI directly:
Dafny.exe build .\grep.dfy .\IoNative.cs

```

### Execution

```bash
# Windows (.exe):
.\grep.exe "SearchTerm" target_file.txt

# Cross-platform (.dll):
dotnet grep.dll "SearchTerm" target_file.txt

```

---

## 3. Algorithm Description

To achieve the full marks designated for Challenge 2, this solution implements the Knuth-Morris-Pratt string searching algorithm. This avoids the quadratic time complexity of the naive approach, resolving the search in $O(N + M)$ time.

The algorithm is split into two verified phases:

1. **`ComputeLPS` (Preprocessing Phase):** Analyzes the search pattern to build an array tracking the Longest Proper Prefix which is also a Suffix (LPS). This array acts as a jump table.
2. **`KMPSearch` (Search Phase):** Iterates through the file buffer. When a mismatch occurs, instead of resetting the search pointer to the beginning of the pattern, it uses the LPS array to bypass previously matched characters, preventing redundant comparisons.

---

## 4. Verification and Design Decisions

Verifying KMP in Dafny presents unique challenges regarding array indexing and loop termination. State-machine verifiers inherently struggle with pointers that occasionally jump backward (like the LPS index `j`).

### Loop Termination Metrics (`decreases`)

To mathematically prove to Dafny that the `while` loops will not run infinitely, complex weighted sum termination metrics were required:

* **LPS Computation:** The clause `decreases 2 * (pat.Length - i) + len` ensures that even when the `len` tracker drops (jumping backward in the pattern), the dominant factor `(pat.Length - i)` enforces a strict downward trend over the lifespan of the loop.
* **Search Execution:** The clause `decreases 2 * (N - i) + j` operates on the same principle. When a mismatch occurs, `j` decreases while `i` remains static. The weighted multiplier proves that forward progress (`i`) easily absorbs any backward adjustments (`j`), guaranteeing termination.

### Memory Safety and Bounds Checking (`invariant`)

* **LPS Bounding:** To prove that jumping backward via `j := lps[j - 1]` will never throw an `IndexOutOfBounds` exception, `ComputeLPS` enforces the invariant `forall k :: 0 <= k < lps.Length ==> 0 <= lps[k] <= k`. This guarantees the jump value is always within the known bounds.
* **Non-Negative Matching:** `KMPSearch` uses `invariant j <= i` to prove that `i - j` (the starting index of a successful match) will always be $\ge 0$.

### I/O Environment Integrity

Per the `Io.dfy` specification, any failure in `Read` or `Write` invalidates the environment state (`env.ok.ok()`). The `Main` method explicitly checks the boolean return values of all I/O operations and immediately aborts upon failure, ensuring that illegal operations (such as calling `.Close()` on a failed stream) are mathematically impossible.
