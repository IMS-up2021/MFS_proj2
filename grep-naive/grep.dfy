/*  
 * This is the skeleton for the grep utility.
 * In this folder you should include a grep utility based
 * on the "naive" string matching algorithm.
 *
 */

include "Io.dfy"

// 1. Naive String Matching Algorithm
method NaiveSearch(txt: array<byte>, pat: array<byte>) returns (found: bool, index: int)
    requires pat.Length > 0
    ensures found ==> 0 <= index <= txt.Length - pat.Length
{
    var N := txt.Length;
    var M := pat.Length;

    // If the text is shorter than the pattern, it's impossible to find a match.
    if N < M {
        return false, -1;
    }

    var i := 0;
    // Outer loop: Iterate through the text, stopping when there isn't enough room left for the pattern.
    while i <= N - M
        decreases N - i
        invariant 0 <= i <= N - M + 1
    {
        var j := 0;
        var matchFound := true;
        
        // Inner loop: Check characters one by one.
        while j < M
            decreases M - j
            invariant 0 <= j <= M
            invariant i + j <= N // Crucial invariant to prove memory safety
        {
            if txt[i + j] != pat[j] {
                matchFound := false;
                break; // Explicitly exit, satisfying the decreases clause
            } 
            
            j := j + 1;
        }

        // If the inner loop finished and matchFound is still true, we found the word.
        if matchFound {
            return true, i;
        }
        
        i := i + 1;
    }
    
    return false, -1;
}

// 2. The Main Executable
method {:main} Main(ghost env: HostEnvironment?)
    requires env != null && env.Valid() && env.ok.ok()
    modifies env.ok
    modifies env.files
{
    // Validate arguments
    var numArgs := HostConstants.NumCommandLineArgs(env);
    if numArgs != 3 {
        print "Usage: ./grep-naive <Word> <File>\n";
        return;
    }

    var wordArg := HostConstants.GetCommandLineArg(1, env);
    var fileArg := HostConstants.GetCommandLineArg(2, env);

    if wordArg.Length == 0 {
        print "Error: Search word cannot be empty.\n";
        return;
    }

    // Verify file existence
    var fileExists := FileStream.FileExists(fileArg, env);
    if !fileExists {
        print "NO\n"; 
        return;
    }

    // Retrieve file length safely
    var success, len := FileStream.FileLength(fileArg, env);
    if !success || len < 0 {
        print "NO\n";
        return;
    }

    // Open file
    var ok, f := FileStream.Open(fileArg, env);
    if !ok {
        print "NO\n";
        return;
    }

    // Read file contents into a buffer
    var buffer := new byte[len];
    ok := f.Read(0 as nat32, buffer, 0 as int32, len);
    if !ok {
        print "NO\n";
        return; 
    }
    
    // Close file before proceeding with the search
    var closeOk := f.Close();

    // Convert the search word (array<char>) to byte array (array<byte>)
    var wordBytes := new byte[wordArg.Length];
    var k := 0;
    while k < wordArg.Length
        invariant 0 <= k <= wordArg.Length
    {
        var charVal := wordArg[k] as int;
        // Standardize non-byte characters if present to prevent crash
        wordBytes[k] := if 0 <= charVal < 256 then charVal as byte else 63; 
        k := k + 1;
    }

    // Execute the naive search
    var found, idx := NaiveSearch(buffer, wordBytes);

    if found {
        print "YES: ";
        print idx;
        print "\n";
    } else {
        print "NO\n";
    }
}