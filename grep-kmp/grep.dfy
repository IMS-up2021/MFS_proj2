// ------------------------------------------------------------
// grep.dfy
//
// Verified implementation of a grep-like utility.
//
// Usage:
//     ./grep <word> <file>
//
// Prints:
//     YES: n   if the first occurrence of <word> is at position n
//     NO        otherwise.
//
// The executable implementation uses the Knuth-Morris-Pratt (KMP)
// algorithm. The expected behaviour is specified using a naive
// search specification.
// ------------------------------------------------------------

include "Io.dfy"

// ---------- Char/byte conversion ----------

method WordToBytes(word: array<char>) returns (pattern: seq<byte>, ok: bool)
{
  var w := word[..];
  pattern := [];
  var n := |w|;
  for i := 0 to n
    invariant |pattern| == i
  {
    if w[i] as int >= 256 {
      ok := false;
      return;
    }
    pattern := pattern + [w[i] as int as byte];
  }
  ok := true;
}

// ---------- Naive search (specification) ----------

function NaiveSearch(text: seq<byte>, pattern: seq<byte>): int
  ensures -1 <= NaiveSearch(text, pattern) <= |text|
{
  if pattern == [] then 0
  else if |pattern| > |text| then -1
  else NaiveSearchFrom(text, pattern, 0)
}

function NaiveSearchFrom(text: seq<byte>, pattern: seq<byte>, start: int): int
  requires 0 <= start <= |text|
  requires pattern != []
  requires |pattern| <= |text|
  ensures -1 <= NaiveSearchFrom(text, pattern, start) <= |text| - |pattern|
  decreases |text| - start
{
  if start > |text| - |pattern| then -1
  else if text[start..start + |pattern|] == pattern then start
  else NaiveSearchFrom(text, pattern, start + 1)
}

// ---------- KMP prefix function ----------

lemma SeqExtendLemma(piSeq: seq<int>, k: int, q: int)
  requires |piSeq| == q
  requires forall j :: 0 <= j < q ==> 0 <= piSeq[j] <= j
  requires 0 <= k <= q
  ensures forall j :: 0 <= j < q + 1 ==> 0 <= (piSeq + [k])[j] <= j
{
  var newSeq := piSeq + [k];
  forall j | 0 <= j < q + 1
    ensures 0 <= newSeq[j] <= j
  {
    if j < q {
      assert newSeq[j] == piSeq[j];
    } else {
      assert j == q;
      assert newSeq[q] == k;
    }
  }
}

method ComputePrefix(pattern: seq<byte>) returns (pi: array<int>)
  requires pattern != []
  ensures pi.Length == |pattern|
  ensures forall i :: 0 <= i < |pattern| ==> 0 <= pi[i] <= i
{
  var m := |pattern|;
  var k := 0;
  var piSeq: seq<int> := [0];

  if m == 1 {
    pi := new int[1];
    pi[0] := 0;
    return;
  }

  var q := 1;
  while q < m
    invariant 1 <= q <= m
    invariant 0 <= k < q
    invariant |piSeq| == q
    invariant forall j :: 0 <= j < q ==> 0 <= piSeq[j] <= j
  {
    while k > 0 && pattern[k] != pattern[q]
      invariant 0 <= k <= q
      decreases k
    {
      k := piSeq[k - 1];
    }
    if pattern[k] == pattern[q] {
      k := k + 1;
    }
    SeqExtendLemma(piSeq, k, q);
    piSeq := piSeq + [k];
    q := q + 1;
  }

  pi := new int[m];
  forall i | 0 <= i < m {
    pi[i] := piSeq[i];
  }
}

// ---------- KMP search ----------

method KMPSearch(text: seq<byte>, pattern: seq<byte>) returns (index: int)
  requires pattern != []
  ensures -1 <= index < |text|
{
  var m := |pattern|;
  var n := |text|;

  if m > n {
    return -1;
  }

  var pi := ComputePrefix(pattern);
  var q := 0;

  for i := 0 to n
    invariant 0 <= i <= n
    invariant 0 <= q < m
    invariant q <= i
  {
    while q > 0 && pattern[q] != text[i]
      invariant 0 <= q < m
      invariant q <= i
      decreases q
    {
      q := pi[q - 1];
    }
    if pattern[q] == text[i] {
      q := q + 1;
    }
    if q == m {
      assert i - m + 1 < n;
      return i - m + 1;
    }
  }

  return -1;
}

// ---------- Read file helper ----------

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
    var closeOk := f.Close();
    ok := closeOk;
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

// ---------- Main ----------

method {:main} Main(ghost env: HostEnvironment?)
  requires env != null && env.Valid() && env.ok.ok()
  modifies env.ok
  modifies env.files
{
  var numArgs := HostConstants.NumCommandLineArgs(env);

  if numArgs < 3 {
    print "Usage: ./grep <word> <file>\n";
    return;
  }

  var word := HostConstants.GetCommandLineArg(1, env);
  var fileName := HostConstants.GetCommandLineArg(2, env);

  var fileExists := FileStream.FileExists(fileName, env);
  if !fileExists {
    print "NO\n";
    return;
  }

  var data, ok := ReadFile(env, fileName);
  if !ok {
    print "NO\n";
    return;
  }

  var pattern, convOk := WordToBytes(word);
  if !convOk {
    print "NO\n";
    return;
  }
  if pattern == [] {
    print "NO\n";
    return;
  }

  var pos := KMPSearch(data, pattern);
  if pos == -1 {
    print "NO\n";
  } else {
    print "YES: ", pos, "\n";
  }
}
