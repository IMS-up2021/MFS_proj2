# Reverse Utility (Dafny)

This folder contains a verified line-reversal utility implemented in Dafny.

The program reads a source file and writes a destination file where the order of lines is reversed.
It keeps each line content intact and preserves the total output length.

## What is verified

In [reverse.dfy](reverse.dfy), the core method `ReverseLines` is specified and verified with loop invariants and termination arguments.

Main guarantees covered by the implementation:

- It validates command-line arguments.
- It checks that the source exists.
- It refuses to overwrite an existing destination.
- It reads source bytes, reverses line order, and writes output.
- It checks open/read/write/close results and reports errors.

## Files

- [reverse.dfy](reverse.dfy): Dafny implementation and verified logic.
- [Io.dfy](Io.dfy): I/O interface contracts used by verification.
- [IoNative.cs](IoNative.cs): C# runtime bindings for file/args operations.
- [Makefile](Makefile): Build/compile helper.

## Build and run

### 1. Go to this folder

```bash
cd reverse
```

### 2. Compile

Option A (with `make`):

```bash
make compile
```

Option B (direct Dafny command):

```bash
dafny reverse.dfy IoNative.cs
```

If `make compile` returns exit code `127`, your shell likely cannot find the Dafny executable configured in [Makefile](Makefile). In that case, run the direct Dafny command with the full Dafny path.

### 3. Execute

Windows PowerShell example:

```powershell
./reverse.exe .\input.txt .\output.txt
```

Expected usage:

```text
./reverse <source> <dest>
```

## Quick test

Create a test file and run:

```powershell
Set-Content -Path .\input.txt -Value @(
"line1"
"line2"
"line3"
) -NoNewline

./reverse.exe .\input.txt .\output.txt
Get-Content .\output.txt
```

Expected output order:

```text
line3
line2
line1
```

## Error messages you may see

- `Usage: ./reverse <source> <dest>`
- `Error: Source file does not exist.`
- `Error: Destination file already exists.`
- `Error: Could not open/read/write/close ...`

