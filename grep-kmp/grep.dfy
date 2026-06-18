/*  
 * This is the skeleton for the grep utility.
 * In this folder you should include a grep utility based
 * on the Knuth-Morris-Pratt algorithm.
 *
 */

include "Io.dfy"

// LPS (Longest Proper Prefix which is also Suffix) Array Computation
method ComputeLPS(pat: array<byte>) returns (lps: array<int>)
    // Precondition: KMP requires a non-empty pattern to establish the LPS array.
    requires pat.Length > 0

    // Postcondition: The resulting jump table must perfectly map to the pattern's length.
    ensures lps.Length == pat.Length

    // Postcondition (Crucial Memory Safety): This mathematically guarantees that the value stored 
    // in the LPS array at any given index `k` is never larger than `k` itself. 
    // When the KMP search algorithm jumps backward using `j := lps[j-1]`, this proof 
    // tells Dafny that the new `j` will never be out of bounds or skip forward illegally.
    ensures forall k :: 0 <= k < lps.Length ==> 0 <= lps[k] <= k
{
    lps := new int[pat.Length];
    lps[0] := 0;
    var len := 0;
    var i := 1;
    
    while i < pat.Length
        // Termination Metric: Proves the loop will eventually stop.
        // During KMP, `len` sometimes decreases (when jumping backward in the pattern). 
        // If we just used `decreases pat.Length - i`, Dafny would complain on the `else` branch.
        // By using a weighted sum, even if `len` drops, the eventual increment of `i` 
        // (which is multiplied by 2) enforces a strict overall downward mathematical trend.        
        decreases 2 * (pat.Length - i) + len

        // Loop Invariant (Bounds): `i` scans forward but never exceeds the pattern length.
        invariant 1 <= i <= pat.Length

        // Loop Invariant (Bounds): The length of the current matching prefix (`len`) 
        // must always be strictly less than the current read head (`i`). This proves 
        // that `pat[len]` will never throw an IndexOutOfBounds exception.
        invariant 0 <= len < i

        // Loop Invariant (State): Maintains the mathematical guarantee of the LPS array 
        // being bounded by its own indices on every single iteration of the loop.
        invariant forall k :: 0 <= k < i ==> 0 <= lps[k] <= k
    {
        if pat[i] == pat[len] {
            len := len + 1;
            lps[i] := len;
            i := i + 1;
        } else {
            if len != 0 {
                len := lps[len - 1]; 
            } else {
                lps[i] := 0;
                i := i + 1;
            }
        }
    }
}

// The KMP Search Logic
method KMPSearch(txt: array<byte>, pat: array<byte>) returns (found: bool, index: int)
    // Precondition: Cannot search for an empty string.
    requires pat.Length > 0

    // Postcondition: If a match is found, the returned starting index must be a valid 
    // positive number, and it must leave enough room in the text array for the entire pattern.
    ensures found ==> 0 <= index <= txt.Length - pat.Length
{
    var M := pat.Length;
    var N := txt.Length;
    var lps := ComputeLPS(pat);
    var i := 0;
    var j := 0;

    while i < N
        // When a character matches, `i` and `j` both increase. The `(N - i)` term shrinks twice 
        // as fast as `j` grows, causing the total value to drop. 
        // When a mismatch occurs, `j` decreases (via the LPS jump table) and `i` stays the same, 
        // so the total value also drops.
        decreases 2 * (N - i) + j

        // Loop Invariant (Bounds): The text read head stays within the text file bounds.
        invariant 0 <= i <= N

        // Loop Invariant (Bounds): The pattern read head stays within the pattern bounds.
        invariant 0 <= j < M

        // Loop Invariant (Logic Safety): The pattern index (`j`) can never outpace the 
        // text index (`i`). This is the critical proof required by Dafny to ensure that 
        // returning `i - j` upon a successful match will not yield a negative index.
        invariant j <= i
    {
        if pat[j] == txt[i] {
            j := j + 1;
            i := i + 1;
        }

        if j == M {
            // Match found! `i` is at the end of the match, so the start is `i - j`.
            return true, i - j;
        } else if i < N && pat[j] != txt[i] {
            if j != 0 {
                // Mismatch after some matches. Jump j backward using the verified LPS table.
                j := lps[j - 1];
            } else {
                // Mismatch on the very first character. Just advance the text pointer.
                i := i + 1;
            }
        }
    }
    return false, -1;
}

// The Main Executable
method {:main} Main(ghost env: HostEnvironment?)
    // Precondition (I/O State): The program can only start if the host environment is 
    // initialized, valid, and the internal file system state hasn't crashed.
    requires env != null && env.Valid() && env.ok.ok()

    // Modification Framing: Explicitly tells the verifier this method is allowed 
    // to alter the success state (`env.ok`) and the file system trackers (`env.files`).
    modifies env.ok
    modifies env.files
{
    var numArgs := HostConstants.NumCommandLineArgs(env);
    if numArgs != 3 {
        print "Usage: ./grep <Word> <File>\n";
        return;
    }

    var wordArg := HostConstants.GetCommandLineArg(1, env);
    var fileArg := HostConstants.GetCommandLineArg(2, env);

    if wordArg.Length == 0 {
        print "Error: Search word cannot be empty.\n";
        return;
    }

    var fileExists := FileStream.FileExists(fileArg, env);
    if !fileExists {
        print "NO\n";
        return;
    }

    var success, len := FileStream.FileLength(fileArg, env);
    if !success || len < 0 {
        print "NO\n";
        return;
    }

    var ok, f := FileStream.Open(fileArg, env);
    if !ok {
        print "NO\n";
        return;
    }

    var buffer := new byte[len];
    ok := f.Read(0 as nat32, buffer, 0 as int32, len);
    if !ok {
        print "NO\n";
        return; 
    }
    var closeOk := f.Close();

    // Safe Char-to-Byte Conversion
    // Command line args are chars, but file contents are bytes. 
    // Safely map them without violating Dafny's strict byte bounds (0-255).
    var wordBytes := new byte[wordArg.Length];
    var k := 0;
    while k < wordArg.Length
        // Loop Invariant (Bounds): Standard bounds proof for iterating over the argument string.
        invariant 0 <= k <= wordArg.Length
    {
        var charVal := wordArg[k] as int;
        // If the character is outside standard ASCII/Byte range, replace with a placeholder
        wordBytes[k] := if 0 <= charVal < 256 then charVal as byte else 63; 
        k := k + 1;
    }

    // Execution & Output formatting
    var found, idx := KMPSearch(buffer, wordBytes);

    if found {
        print "YES: ";
        print idx;
        print "\n";
    } else {
        print "NO\n";
    }
}