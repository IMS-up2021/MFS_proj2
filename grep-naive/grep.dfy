include "Io.dfy"

// 1. Bounded Naive String Matching
// Searches for a pattern exclusively within a specified segment of the text array.
method ContainsWord(txt: array<byte>, txtStart: int, txtEnd: int, pat: array<byte>) returns (found: bool)
    requires pat.Length > 0
    requires 0 <= txtStart <= txtEnd <= txt.Length
{
    var len := txtEnd - txtStart;
    var M := pat.Length;

    if len < M { 
        return false; 
    }

    var i := 0;
    while i <= len - M
        decreases len - i
        invariant 0 <= i <= len - M + 1
    {
        var j := 0;
        while j < M
            decreases M - j
            invariant 0 <= j <= M
            invariant txtStart + i + j <= txtEnd // Ensures we never read past the designated line end
        {
            if txt[txtStart + i + j] != pat[j] {
                break;
            }
            j := j + 1;
        }

        if j == M {
            return true;
        }
        i := i + 1;
    }
    return false;
}

// 2. Output Helper
// Safely converts bytes to a string sequence to avoid literal character printing.
method PrintBufferSegment(buffer: array<byte>, start: int, end: int)
    requires 0 <= start <= end <= buffer.Length
{
    var s: string := [];
    var k := start;
    while k < end
        decreases end - k
        invariant start <= k <= end
    {
        // Ignore the carriage return byte (13) to clean up Windows line endings
        if buffer[k] != 13 {
            s := s + [buffer[k] as char];
        }
        k := k + 1;
    }
    print s;
    print "\n";
}

// 3. Line Parsing and Execution
// Scans the file for newlines and processes each line individually.
method GrepLines(buffer: array<byte>, pat: array<byte>)
    requires pat.Length > 0
{
    var i := 0;
    var line_start := 0;

    while i < buffer.Length
        decreases buffer.Length - i
        invariant 0 <= i <= buffer.Length
        invariant 0 <= line_start <= i + 1
    {
        // When we hit a newline byte (10)
        if buffer[i] == 10 {
            if line_start <= i {
                var found := ContainsWord(buffer, line_start, i, pat);
                if found {
                    PrintBufferSegment(buffer, line_start, i);
                }
            }
            line_start := i + 1;
        }
        i := i + 1;
    }

    // Process the final chunk of the file if it doesn't end with a trailing newline
    if line_start <= buffer.Length {
        var found := ContainsWord(buffer, line_start, buffer.Length, pat);
        if found {
            PrintBufferSegment(buffer, line_start, buffer.Length);
        }
    }
}

// 4. The Main Executable
method {:main} Main(ghost env: HostEnvironment?)
    requires env != null && env.Valid() && env.ok.ok()
    modifies env.ok
    modifies env.files
{
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

    var fileExists := FileStream.FileExists(fileArg, env);
    if !fileExists { return; } // UNIX grep fails silently if file doesn't exist

    var success, len := FileStream.FileLength(fileArg, env);
    if !success || len < 0 { return; }

    var ok, f := FileStream.Open(fileArg, env);
    if !ok { return; }

    var buffer := new byte[len];
    ok := f.Read(0 as nat32, buffer, 0 as int32, len);
    if !ok { return; }
    
    var closeOk := f.Close();

    var wordBytes := new byte[wordArg.Length];
    var k := 0;
    while k < wordArg.Length
        invariant 0 <= k <= wordArg.Length
    {
        var charVal := wordArg[k] as int;
        wordBytes[k] := if 0 <= charVal < 256 then charVal as byte else 63; 
        k := k + 1;
    }

    // Execute the UNIX-style line matching
    GrepLines(buffer, wordBytes);
}