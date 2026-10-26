/-
  Command line front end for the TOML subset parser, used by the
  tests. Reads one request per line and prints one answer per line.

  A request holds a document as character codes:

    parse 116 105 116 108 101 ...

  The answer is the codes of the canonical reprint, one line, or
  `none` when the document is rejected. A malformed request prints
  `error`. An empty document reprints as an empty line. A line may
  end in LF or CR LF.

  The line handling is covered by the tests, not by a proof.
-/

import Toml

def parseCode (s : String) : Option Nat :=
  if s.isEmpty then none
  else if s.toList.all (fun c => decide ('0' ≤ c && c ≤ '9')) then
    some (s.toList.foldl (fun acc c => acc * 10 + (c.toNat - 48)) 0)
  else none

def runRequest (line : String) : String :=
  match line.splitOn " " with
  | "parse" :: tokens =>
    match tokens.mapM parseCode with
    | none => "error"
    | some codes =>
      if codes.any (fun n => 1114111 < n || (55296 ≤ n && n ≤ 57343)) then
        "error"
      else
        let doc := String.ofList (codes.map Char.ofNat)
        match Toml.parseDoc doc with
        | none => "none"
        | some entries =>
          let printed := Toml.printDoc entries
          String.intercalate " " (printed.toList.map (fun c => toString c.toNat))
  | _ => "error"

def stripCR (line : String) : String :=
  if line.endsWith "\r" then (line.take (line.length - 1)).toString else line

def main (args : List String) : IO UInt32 := do
  match args with
  | [file] => do
    let content ← IO.FS.readFile file
    let mut out := ""
    for line in content.splitOn "\n" do
      let line := stripCR line
      if line = "" then continue
      out := out ++ runRequest line ++ "\n"
    IO.print out
    pure 0
  | _ => do
    IO.eprintln "usage: toml <file>"
    pure 1
