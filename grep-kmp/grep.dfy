/*  
 * This is the skeleton for the grep utility.
 * In this folder you should include a grep utility based
 * on the Knuth-Morris-Pratt algorithm.
 *
 */

include "Io.dfy"

// 1. LPS (Longest Proper Prefix which is also Suffix) Array Computation
method ComputeLPS(pat: array<byte>) returns (lps: array<int>)
    requires pat.Length > 0
    ensures lps.Length == pat.Length
    // The LPS value can never exceed the current index.
    // This mathematically proves that j := lps[j-1] will never go out of bounds.
    ensures forall k :: 0 <= k < lps.Length ==> 0 <= lps[k] <= k
{
    lps := new int[pat.Length];
    lps[0] := 0;
    var len := 0;
    var i := 1;
    
    while i < pat.Length
        // The termination metric: a weighted sum that always goes down, 
        // even when 'len' drops via the LPS array.
        decreases 2 * (pat.Length - i) + len
        invariant 1 <= i <= pat.Length
        invariant 0 <= len < i
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

// 2. The KMP Search Logic
method KMPSearch(txt: array<byte>, pat: array<byte>) returns (found: bool, index: int)
    requires pat.Length > 0
    ensures found ==> 0 <= index <= txt.Length - pat.Length
{
    var M := pat.Length;
    var N := txt.Length;
    var lps := ComputeLPS(pat);
    var i := 0;
    var j := 0;

    while i < N
        // The magic KMP termination metric.
        decreases 2 * (N - i) + j
        invariant 0 <= i <= N
        invariant 0 <= j < M
        invariant j <= i // Proves that if we find a match, i - j is never negative
    {
        if pat[j] == txt[i] {
            j := j + 1;
            i := i + 1;
        }

        if j == M {
            return true, i - j;
        } else if i < N && pat[j] != txt[i] {
            if j != 0 {
                j := lps[j - 1]; // Safe because lps[j-1] < j
            } else {
                i := i + 1;
            }
        }
    }
    return false, -1;
}

// 3. The Main Executable
method {:main} Main(ghost env: HostEnvironment?)
    requires env != null && env.Valid() && env.ok.ok()
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
        print "NO\n"; // Standard grep fails silently or prints nothing, but adhering to the project YES/NO theme.
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

    // 4. Safe Char-to-Byte Conversion
    // Command line args are chars, but file contents are bytes. 
    // We must safely map them without violating Dafny's strict byte bounds (0-255).
    var wordBytes := new byte[wordArg.Length];
    var k := 0;
    while k < wordArg.Length
        invariant 0 <= k <= wordArg.Length
    {
        var charVal := wordArg[k] as int;
        // If the character is outside standard ASCII/Byte range, replace with a placeholder
        wordBytes[k] := if 0 <= charVal < 256 then charVal as byte else 63; 
        k := k + 1;
    }

    // 5. Execution & Output formatting
    var found, idx := KMPSearch(buffer, wordBytes);

    if found {
        print "YES: ";
        print idx;
        print "\n";
    } else {
        print "NO\n";
    }
}