// ------------------------------------------------------------
// reverse.dfy
//
// Verified implementation of a line-reversal utility.
//
// Usage:
//     ./reverse <source> <destination>
//
// Creates the destination file containing all lines from the
// source file in reverse order.
//
// The executable implementation uses a straightforward approach of
// reading the entire file into memory, reversing it, and writing
// it back out. The expected behaviour is specified using a functional
// specification of the reversal operation.
// ------------------------------------------------------------




include "Io.dfy"

const NEWLINE := 0x0A as byte

// ---------- Functional specification ----------

function IndexOf(s: seq<byte>, b: byte): int
  ensures -1 <= IndexOf(s, b) < |s|
{
  if s == [] then -1
  else if s[0] == b then 0
  else var i := IndexOf(s[1..], b); if i == -1 then -1 else 1 + i
}

function SplitLines(s: seq<byte>): seq<seq<byte>>
  decreases |s|
{
  if s == [] then []
  else
    var i := IndexOf(s, NEWLINE);
    if i == -1 then [s]
    else [s[..i]] + SplitLines(s[i+1..])
}

function JoinLines(lines: seq<seq<byte>>): seq<byte>
  decreases |lines|
{
  if lines == [] then []
  else if |lines| == 1 then lines[0]
  else lines[0] + [NEWLINE] + JoinLines(lines[1..])
}

function ReverseSeq<T>(s: seq<T>): seq<T>
  decreases |s|
{
  if s == [] then []
  else ReverseSeq(s[1..]) + [s[0]]
}

function ReverseFileContent(s: seq<byte>): seq<byte>
{
  JoinLines(ReverseSeq(SplitLines(s)))
}

// ---------- Lemmas ----------

lemma JoinLinesAppendNonEmptyLast(ls: seq<seq<byte>>, last: seq<byte>)
  requires ls != []
  ensures JoinLines(ls + [last]) == JoinLines(ls) + [NEWLINE] + last
  decreases |ls|
{
  if |ls| == 1 {
    calc {
      JoinLines(ls + [last]);
      (ls + [last])[0] + [NEWLINE] + JoinLines((ls + [last])[1..]);
      ls[0] + [NEWLINE] + JoinLines([last]);
      ls[0] + [NEWLINE] + last;
      JoinLines(ls) + [NEWLINE] + last;
    }
  } else {
    var l := ls[0];
    var tail := ls[1..];
    var lines := ls + [last];
    assert |lines| >= 3;
    assert lines[0] == l;
    assert lines[1..] == tail + [last];
    assert lines[0] == (ls + [last])[0];
    assert JoinLines(lines) == lines[0] + [NEWLINE] + JoinLines(lines[1..]);
    assert JoinLines(ls + [last]) == l + [NEWLINE] + JoinLines(tail + [last]);
    JoinLinesAppendNonEmptyLast(tail, last);
    calc {
      JoinLines(ls + [last]);
      l + [NEWLINE] + JoinLines(tail + [last]);
      l + [NEWLINE] + (JoinLines(tail) + [NEWLINE] + last);
      (l + [NEWLINE] + JoinLines(tail)) + [NEWLINE] + last;
      JoinLines(ls) + [NEWLINE] + last;
    }
  }
}

lemma ReverseFileContentLenLE(s: seq<byte>)
  ensures |ReverseFileContent(s)| <= |s|
  decreases |s|
{
  if s == [] {
  } else {
    var i := IndexOf(s, NEWLINE);
    if i == -1 {
      calc {
        ReverseFileContent(s);
        JoinLines(ReverseSeq(SplitLines(s)));
        JoinLines(ReverseSeq([s]));
        JoinLines([s]);
        s;
      }
    } else {
      var prefix := s[..i];
      var rest := s[i+1..];
      ReverseFileContentLenLE(rest);
      var revRestLines := ReverseSeq(SplitLines(rest));
      if revRestLines == [] {
      } else {
        JoinLinesAppendNonEmptyLast(revRestLines, prefix);
        calc {
          |ReverseFileContent(s)|;
          |JoinLines(revRestLines + [prefix])|;
          |JoinLines(revRestLines) + [NEWLINE] + prefix|;
          |JoinLines(revRestLines)| + 1 + |prefix|;
          |ReverseFileContent(rest)| + 1 + |prefix|;
        }
      }
    }
  }
}

// ---------- Helper methods ----------

method ReadFile(ghost env: HostEnvironment, name: array<char>) returns (data: seq<byte>, ok: bool)
  requires env.Valid() && env.ok.ok()
  requires name[..] in env.files.state()
  modifies env.ok
  modifies env.files
  ensures ok ==> data == old(env.files.state())[name[..]]
  ensures ok ==> |data| < 0x80000000 as int
  ensures env.ok.ok() == ok
{
  data := [];

  var lenOk, len := FileStream.FileLength(name, env);
  if !lenOk {
    ok := false;
    return;
  }

  var fOk, f := FileStream.Open(name, env);
  if !fOk {
    ok := false;
    return;
  }

  if len == 0 {
    data := [];
    ghost var afterOpen := env.files.state();
    var closeOk := f.Close();
    ok := closeOk;
    if ok {
      assert env.files.state() == afterOpen;
    }
    return;
  }

  var buffer := new byte[len as int];
  var readOk := f.Read(0 as nat32, buffer, 0 as int32, len);
  if !readOk {
    ok := false;
    return;
  }

  data := buffer[..];
  ghost var preClose := env.files.state();
  var closeOk := f.Close();
  ok := closeOk;
  if ok {
    assert env.files.state() == preClose;
  }
}

method WriteFile(ghost env: HostEnvironment, name: array<char>, data: seq<byte>) returns (ok: bool)
  requires env.Valid() && env.ok.ok()
  requires |data| < 0x80000000 as int
  requires name[..] !in env.files.state()
  modifies env.ok
  modifies env.files
  ensures ok ==> name[..] in env.files.state()
  ensures ok ==> env.files.state()[name[..]] == data
  ensures env.ok.ok() == ok
{
  var fOk, f := FileStream.Open(name, env);
  if !fOk {
    ok := false;
    return;
  }
  assert f.Name() == name[..];

  if |data| > 0 {
    var buffer := new byte[|data|](i requires 0 <= i < |data| => data[i]);
    var numBytes: int32 := |data| as int32;
    var writeOk := f.Write(0 as nat32, buffer, 0 as int32, numBytes);
    if !writeOk {
      ok := false;
      return;
    }
  }

  ghost var preCloseState := env.files.state();
  var closeOk := f.Close();
  ok := closeOk;
  if ok {
    assert env.files.state() == preCloseState;
  }
}

// ---------- Main ----------

method {:main} Main(ghost env: HostEnvironment?)
  requires env != null && env.Valid() && env.ok.ok()
  modifies env.ok
  modifies env.files
{
  var numArgs := HostConstants.NumCommandLineArgs(env);

  if numArgs < 3 {
    print "Usage: ./reverse <source> <destination>\n";
    return;
  }

  var srcName := HostConstants.GetCommandLineArg(1, env);
  var dstName := HostConstants.GetCommandLineArg(2, env);

  var dstExists := FileStream.FileExists(dstName, env);
  if dstExists {
    print "Destination file already exists\n";
    return;
  }

  var srcExists := FileStream.FileExists(srcName, env);
  if !srcExists {
    print "Source file does not exist\n";
    return;
  }

  var data, ok := ReadFile(env, srcName);
  if !ok {
    print "Error reading source file\n";
    return;
  }

  var reversed := ReverseFileContent(data);
  ReverseFileContentLenLE(data);
  assert |reversed| < 0x80000000 as int;

  var dstExistsAgain := FileStream.FileExists(dstName, env);
  if dstExistsAgain {
    print "Destination file was created during processing\n";
    return;
  }

  ok := WriteFile(env, dstName, reversed);
  if !ok {
    print "Error writing destination file\n";
    return;
  }
}
