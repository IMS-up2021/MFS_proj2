/*
 * This is the skeleton for your line reverse utility.
 *
 */
include "Io.dfy"

method ReverseLines(input: array<byte>) returns (output: array<byte>)
  ensures output.Length == input.Length
{
  output := new byte[input.Length];
  if input.Length == 0 {
    return;
  }

  var i := input.Length - 1;
  var out_idx := 0;
  var line_end := input.Length;

  while i >= 0
    decreases i
    invariant -1 <= i < input.Length
    invariant 0 <= line_end <= input.Length
    invariant i < line_end
    invariant out_idx == input.Length - line_end
  {
    if input[i] == 10 || i == 0 {
      var start := if input[i] == 10 then i + 1 else 0;
      var len := line_end - start;

      var k := 0;
      while k < len
        decreases len - k
        invariant 0 <= k <= len
        invariant out_idx + k <= output.Length
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
        line_end := 0;
      }
    }
    i := i - 1;
  }
}

method {:main} Main(ghost env: HostEnvironment?)
  requires env != null && env.Valid() && env.ok.ok()
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

  // 4. Reverse the Lines
  var outBuffer := ReverseLines(buffer);

  // 5. Write to Destination File
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