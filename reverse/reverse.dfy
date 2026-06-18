/*
 * This is the skeleton for your line reverse utility.
 *
 */
include "Io.dfy"

method ReverseLines(input: array<byte>) returns (output: array<byte>)
  // Postcondition (Memory Safety): Guarantees that the new array generated to hold 
  // the reversed file is the exact same size as the original file. This allows Dafny 
  // to implicitly trust the bounds of the output array later in the program.
  ensures output.Length == input.Length
{
  output := new byte[input.Length];
  if input.Length == 0 {
    return;
  }

  var i := input.Length - 1;
  var out_idx := 0;
  var line_end := input.Length;

  // Outer Loop: Scans the file backward from the end to the beginning.
  while i >= 0
    // Termination Metric: `i` starts at the end of the array and strictly decreases by 1 
    // each iteration until it drops below 0.
    decreases i

    // Loop Invariant (Bounds): `i` safely traverses down the array and is allowed to hit 
    // -1 at the very end to trigger loop termination.
    invariant -1 <= i < input.Length

    // Loop Invariant (Bounds): Tracks the end of the current line being processed, 
    // ensuring it never exceeds the total bounds of the file.
    invariant 0 <= line_end <= input.Length

    // Loop Invariant (Logic Safety): The current read head (`i`) is always strictly 
    // behind the end of the line it is currently scanning.
    invariant i < line_end

    // Loop Invariant (The "Magic" Link): This is the most crucial mathematical proof. 
    // Because we are copying exact chunks from the back to the front, the amount of data 
    // we have written so far (`out_idx`) must always exactly equal the total file length 
    // minus the remaining data left to scan (`line_end`). This algebraic link prevents 
    // Dafny from throwing an out-of-bounds error on the write head.
    invariant out_idx == input.Length - line_end
  {
    // When we hit a newline byte (10) or the very start of the file
    if input[i] == 10 || i == 0 {
      var start := if input[i] == 10 then i + 1 else 0;
      var len := line_end - start;

      var k := 0;
      // Inner Loop: Copies the isolated line forward into the output array.
      while k < len
        // Termination Metric: `k` strictly approaches the length of the line chunk.
        decreases len - k

        // Loop Invariant (Bounds): `k` stays within the length of the line.
        invariant 0 <= k <= len

        // Loop Invariant (Memory Safety - Write): Proves that the current write position 
        // plus the current offset `k` will never exceed the total capacity of the output buffer.
        invariant out_idx + k <= output.Length

        // Loop Invariant (Memory Safety - Read): Proves that the starting index of the line 
        // plus the offset `k` will never read past the end of the original input file.
        invariant start + k <= input.Length
      {
        output[out_idx + k] := input[start + k];
        k := k + 1;
      }

      out_idx := out_idx + len;

      if input[i] == 10 {
        if out_idx < output.Length {
          output[out_idx] := 10;
          out_idx := out_idx + 1;
          line_end := i;
        }
      } else {
        // We reached the start of the file. Update line_end to 0 to maintain 
        // the `out_idx == input.Length - line_end` invariant on the final iteration.
        line_end := 0;
      }
    }
    i := i - 1;
  }
}

method {:main} Main(ghost env: HostEnvironment?)
  // Precondition (I/O State): The program requires the environment to be valid and 
  // not currently in a failed state (`env.ok.ok() == true`) to begin execution.
  requires env != null && env.Valid() && env.ok.ok()

  // Modification Framing: Explicitly tells the Dafny verifier that this method 
  // has permission to change the success state and file system trackers.
  modifies env.ok
  modifies env.files
{
  // Argument Validation
  var numArgs := HostConstants.NumCommandLineArgs(env);
  if (numArgs != 3) {
    print "Usage: ./reverse <source> <dest>\n";
    return;
  }

  var srcName := HostConstants.GetCommandLineArg(1, env);
  var dstName := HostConstants.GetCommandLineArg(2, env);

  // Check File Existence
  var srcExists := FileStream.FileExists(srcName, env);
  var dstExists := FileStream.FileExists(dstName, env);

  if (!srcExists) {
    print "Error: Source file does not exist.\n";
    return;
  }
  if (dstExists) {
    print "Error: Destination file already exists.\n";
    return;
  }

  // Read Source File
  var success, len := FileStream.FileLength(srcName, env);
  if (!success || len < 0) {
    print "Error: Could not determine source file length.\n";
    return;
  }

  var ok, srcFile := FileStream.Open(srcName, env);
  if (!ok) {
    print "Error: Could not open source file.\n";
    return;
  }

  var buffer := new byte[len];
  ok := srcFile.Read(0 as nat32, buffer, 0 as int32, len);
  if (!ok) {
    print "Error: Failed to read source file.\n";
    return;
  }
  var closeOk := srcFile.Close();

  if (!ok) {
    print "Error: Failed to read source file.\n";
    return;
  }
  if (!closeOk) {
    print "Error: Could not close source file.\n";
    return;
  }

  // Reverse the Lines
  var outBuffer := ReverseLines(buffer);

  // Write to Destination File
  var okDst, dstFile := FileStream.Open(dstName, env);
  if (!okDst) {
    print "Error: Could not open destination file.\n";
    return;
  }

  okDst := dstFile.Write(0 as nat32, outBuffer, 0 as int32, outBuffer.Length as int32);
  if (!okDst) {
    print "Error: Failed to write to destination file.\n";
    return;
  }
  var closeDstOk := dstFile.Close();

  if (!closeDstOk) {
    print "Error: Could not close destination file.\n";
    return;
  }

  if okDst {
    print "File reversed successfully.\n";
  } else {
    print "Error: Failed to write to destination file.\n";
  }
}