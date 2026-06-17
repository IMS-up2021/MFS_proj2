
### Challenge 2: Verified Grep Utility (Naive Algorithm)

## 1. Overview
This directory contains the verified implementation of the `grep` utility using a naive string-matching algorithm, written in Dafny. The program accepts a search word and a file name as command-line arguments. It safely reads the file, searches for the first occurrence of the provided word, and outputs `YES: n` (where `n` is the starting index of the match) or `NO` if the word is not found or an I/O error occurs.

## 2. Building and Execution

### Compilation
The project relies on a custom C# environment implementation (`IoNative.cs`) to handle file system side effects. To compile the program, use the provided `Makefile` or run the Dafny compiler directly:

```bash
# Using the Makefile:
make compile DFY=grep.dfy

# Or using the Dafny CLI directly:
Dafny.exe build .\grep.dfy .\IoNative.cs

```

### Execution

Run the compiled executable with the search word and the target file:

```bash
# Windows (.exe):
.\grep.exe "SearchTerm" target_file.txt

# Cross-platform (.dll):
dotnet grep.dll "SearchTerm" target_file.txt

```

---

## 3. Algorithm Description

The core of this utility is the `NaiveSearch` method. It operates in $O(N \times M)$ time complexity, where $N$ is the length of the text buffer and $M$ is the length of the search pattern.

1. **Outer Loop:** Iterates through the text array using an index `i`. It stops at `N - M` because any index beyond that point does not have enough remaining characters to fit the pattern.
2. **Inner Loop:** Iterates through the pattern array using an index `j`, comparing `pat[j]` with `txt[i + j]`.
3. **Control Flow:** If a mismatch is detected, the inner loop utilizes a `break` statement to immediately halt comparison, increment `i`, and start the next alignment. If the inner loop finishes without breaking, a match has been found.

Additionally, to ensure strict byte-bounds safety when mapping command-line arguments (`array<char>`) to file contents (`array<byte>`), characters outside the standard byte range (0-255) are safely converted to a placeholder byte (63, representing `?`).

---

## 4. Verification and Design Decisions

The implementation is mathematically verified for memory safety, absence of out-of-bounds array access, and guaranteed termination.

### Loop Termination Metrics (`decreases`)

Dafny requires proof that loops will not run infinitely.

* **Outer Loop:** Uses the clause `decreases N - i`. As `i` increments toward the boundary `N - M`, the remaining distance strictly decreases.
* **Inner Loop:** Uses the clause `decreases M - j`. Because the `break` statement explicitly exits the loop on a mismatch, the only path that continues the loop is when a character matches, which guarantees `j` increments and `M - j` decreases.

### Memory Safety and Bounds Checking (`invariant`)

To satisfy Dafny's strict array bounds checker, specific algebraic relationships were established between the pointers:

* `invariant 0 <= i <= N - M + 1` mathematically limits the starting index.
* `invariant i + j <= N` is the crucial safety constraint for the inner loop. Because the maximum value of `i` is `N - M` and the maximum value of `j` is `M`, the highest possible access `txt[i + j]` equates to `txt[(N - M) + M]`, which simplifies perfectly to `txt[N]`. This proves an `IndexOutOfBounds` exception is impossible.

### I/O Preconditions

To satisfy the rigid `Io.dfy` state-machine contracts, explicit boolean status checks were implemented. The environment state (`env.ok.ok()`) mandates that operations like `.Close()` can only be invoked if the preceding `.Read()` or `.Write()` was successful. The code accounts for this by aborting early upon any failed read operation.

## 5. Bonus Implementation: UNIX-Style Output
To achieve the bonus points, the utility was refactored to mimic the default behavior of the UNIX `grep` command, where it prints the entirety of any line containing a matching string, rather than simply returning a boolean `YES/NO` output.

### Architectural Decisions
Implementing this directly in a single `while` loop would require tracking `line_start`, `current_index`, and `pattern_index` concurrently. In a state-machine verifier like Dafny, this leads to complex, intertwined invariants that are difficult to prove and maintain. 

To ensure clean verification, the logic was decoupled into modular, isolated methods:
1. **`GrepLines` (The Scanner):** Iterates over the raw byte buffer, keeping track of a `line_start` pointer. Whenever it encounters a newline byte (`10`) or the End of File (EOF), it identifies a definitive line boundary and passes those bounds `[line_start..i]` to the matching function.
2. **`ContainsWord` (The Bounded Matcher):** Receives the buffer alongside explicit start and end constraints. It executes the standard naive matching algorithm but is mathematically restricted from scanning past the provided `txtEnd`.
3. **`PrintBufferSegment` (The Output):** If `ContainsWord` evaluates to `true`, this helper method prints the characters from `line_start` up to the newline.

### Verification Design
The separation of concerns made bounds checking mathematically straightforward. 
* In `GrepLines`, the invariant `0 <= line_start <= i + 1` mathematically proves that the start of the line will never surpass the current read head, effectively bounding the chunks.
* In `ContainsWord`, the invariant `txtStart + i + j <= txtEnd` serves as the core memory safety constraint. Because the string matching logic is strictly bounded by `txtEnd` rather than the total buffer length, Dafny easily proves that array accesses will never bleed into adjacent lines or trigger an out-of-bounds crash.