/-
  The TOML subset parser. Everything reads `List Char`, so concrete
  cases compute in the kernel. Recursive descent uses an explicit
  fuel argument (decreased on every recursive call) because the
  recursive calls run on parser remainders, which are not structural
  subterms of the input. Top level fuel is generous relative to the
  input length, so fuel never binds on a real document.

  Grammar notes, all checked against Python `tomllib` while writing:
  - bare keys are ASCII letters, digits, `_`, `-`; quoted keys use
    the string rules below.
  - integers are signed 64-bit for decimal, and unsigned base
    integers must also fit in signed 64-bit; a sign on a base
    integer is rejected, as is a leading zero on a decimal part.
  - underscores sit only between digits, in every digit run.
  - floats print canonically with an exponent; `inf` and `nan`
    keep their sign.
  - datetimes: year 0000 to 9999, month 01 to 12, day valid for
    the month (leap rule included), time 00 to 23, 00 to 59,
    00 to 59, fraction digits only, offset `Z` or `±HH:MM`.
    The date/time separator is `T`, `t`, or one space.
  - multiline strings are outside the slice and are rejected:
    a `"""` value parses as an empty string followed by junk,
    which fails the statement end check.
  - inline tables forbid newlines and trailing commas; arrays
    allow both, plus comments.
-/

import Toml.Value

namespace Toml

def isDigitChar (c : Char) : Bool :=
  decide ('0' ≤ c && c ≤ '9')

def digitVal (c : Char) : Nat :=
  c.toNat - 48

def isHexChar (c : Char) : Bool :=
  decide (('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f') ||
    ('A' ≤ c && c ≤ 'F'))

def hexVal (c : Char) : Option Nat :=
  let n := c.toNat
  if 48 ≤ n && n ≤ 57 then some (n - 48)
  else if 97 ≤ n && n ≤ 102 then some (10 + n - 97)
  else if 65 ≤ n && n ≤ 70 then some (10 + n - 65)
  else none

def hexValTotal (c : Char) : Nat :=
  (hexVal c).getD 0

def foldDigitsBase (base : Nat) (ds : List Nat) : Nat :=
  ds.foldl (fun acc d => acc * base + d) 0

def skipWS : List Char -> List Char
  | [] => []
  | ' ' :: rest => skipWS rest
  | '\t' :: rest => skipWS rest
  | cs => cs

def skipToEOL : List Char -> List Char
  | [] => []
  | '\n' :: rest => '\n' :: rest
  | _ :: rest => skipToEOL rest

def skipWSNL : Nat -> List Char -> List Char
  | 0, cs => cs
  | _, [] => []
  | f + 1, ' ' :: rest => skipWSNL f rest
  | f + 1, '\t' :: rest => skipWSNL f rest
  | f + 1, '\n' :: rest => skipWSNL f rest
  | f + 1, '\r' :: '\n' :: rest => skipWSNL f rest
  | f + 1, '#' :: rest => skipWSNL f (skipToEOL rest)
  | _, cs => cs

def collectRun (p : Char -> Bool) : List Char -> List Char × List Char
  | [] => ([], [])
  | c :: rest =>
    if p c then
      let (a, b) := collectRun p rest
      (c :: a, b)
    else ([], c :: rest)

def noDoubleUnderscore : List Char -> Bool
  | [] => true
  | [_] => true
  | '_' :: '_' :: _ => false
  | _ :: rest => noDoubleUnderscore rest

def validDigitRun (pred : Char -> Bool) (run : List Char) : Bool :=
  match run with
  | [] => false
  | c :: _ =>
    pred c && run.all (fun ch => pred ch || ch = '_') &&
      noDoubleUnderscore run &&
      match run.getLast? with
      | some last => pred last
      | none => false

def runDigits (val : Char -> Nat) (run : List Char) : List Nat :=
  (run.filter (fun c => c != '_')).map val

def takeNDigits : Nat -> List Char -> Option (List Nat × List Char)
  | 0, cs => some ([], cs)
  | _, [] => none
  | n + 1, c :: cs =>
    if isDigitChar c then
      match takeNDigits n cs with
      | some (ds, rest) => some (digitVal c :: ds, rest)
      | none => none
    else none

def takeNHex : Nat -> List Char -> Option (List Nat × List Char)
  | 0, cs => some ([], cs)
  | _, [] => none
  | n + 1, c :: cs =>
    match hexVal c with
    | none => none
    | some v =>
      match takeNHex n cs with
      | some (vs, rest) => some (v :: vs, rest)
      | none => none

def parseUnicodeChar (n : Nat) (cs : List Char) :
    Option (Char × List Char) :=
  match takeNHex n cs with
  | none => none
  | some (vs, rest) =>
    let code := foldDigitsBase 16 vs
    if code < 55296 || (57343 < code && code ≤ 1114111) then
      some (Char.ofNat code, rest)
    else none

def parseBasicContent : Nat -> List Char -> Option (String × List Char)
  | 0, _ => none
  | _, [] => none
  | _f + 1, '"' :: rest => some ("", rest)
  | f + 1, '\\' :: rest =>
    match rest with
    | [] => none
    | 'b' :: r =>
      match parseBasicContent f r with
      | some (s, r2) => some (String.ofList [Char.ofNat 8] ++ s, r2)
      | none => none
    | 't' :: r =>
      match parseBasicContent f r with
      | some (s, r2) => some ("\t" ++ s, r2)
      | none => none
    | 'n' :: r =>
      match parseBasicContent f r with
      | some (s, r2) => some ("\n" ++ s, r2)
      | none => none
    | 'f' :: r =>
      match parseBasicContent f r with
      | some (s, r2) => some (String.ofList [Char.ofNat 12] ++ s, r2)
      | none => none
    | 'r' :: r =>
      match parseBasicContent f r with
      | some (s, r2) => some ("\r" ++ s, r2)
      | none => none
    | '"' :: r =>
      match parseBasicContent f r with
      | some (s, r2) => some ("\"" ++ s, r2)
      | none => none
    | '\\' :: r =>
      match parseBasicContent f r with
      | some (s, r2) => some ("\\" ++ s, r2)
      | none => none
    | 'u' :: r =>
      match parseUnicodeChar 4 r with
      | some (ch, r2) =>
        match parseBasicContent f r2 with
        | some (s, r3) => some (String.ofList [ch] ++ s, r3)
        | none => none
      | none => none
    | 'U' :: r =>
      match parseUnicodeChar 8 r with
      | some (ch, r2) =>
        match parseBasicContent f r2 with
        | some (s, r3) => some (String.ofList [ch] ++ s, r3)
        | none => none
      | none => none
    | _ => none
  | f + 1, c :: rest =>
    if c = '\n' || (c.toNat < 32 && c != '\t') || c.toNat = 127 then none
    else
      match parseBasicContent f rest with
      | some (s, r) => some (String.ofList [c] ++ s, r)
      | none => none

def parseLiteralContent : Nat -> List Char -> Option (String × List Char)
  | 0, _ => none
  | _, [] => none
  | _f + 1, '\'' :: rest => some ("", rest)
  | f + 1, c :: rest =>
    if c = '\n' || (c.toNat < 32 && c != '\t') || c.toNat = 127 then none
    else
      match parseLiteralContent f rest with
      | some (s, r) => some (String.ofList [c] ++ s, r)
      | none => none

def parseKeyPart : Nat -> List Char -> Option (String × List Char)
  | 0, _ => none
  | f + 1, '"' :: rest => parseBasicContent f rest
  | f + 1, '\'' :: rest => parseLiteralContent f rest
  | _, cs =>
    let (run, rest) := collectRun isBareChar cs
    if run.isEmpty then none else some (String.ofList run, rest)

def parseKeyPath : Nat -> List Char -> Option (List String × List Char)
  | 0, _ => none
  | f + 1, cs =>
    let cs := skipWS cs
    match parseKeyPart f cs with
    | none => none
    | some (k, rest) =>
      let rest := skipWS rest
      match rest with
      | '.' :: rest2 =>
        match parseKeyPath f (skipWS rest2) with
        | some (ks, r) => some (k :: ks, r)
        | none => none
      | _ => some ([k], rest)

def startsWithChars : List Char -> List Char -> Bool
  | [], _ => true
  | _ :: _, [] => false
  | p :: ps, c :: cs => p = c && startsWithChars ps cs

def dropPrefix (pat : List Char) (cs : List Char) : Option (List Char) :=
  if startsWithChars pat cs then some (cs.drop pat.length) else none

def parseSign (cs : List Char) : Bool × List Char :=
  match cs with
  | '+' :: rest => (false, rest)
  | '-' :: rest => (true, rest)
  | _ => (false, cs)

def parseBaseInt (base : Nat) (pred : Char -> Bool) (val : Char -> Nat)
    (cs : List Char) : Option (Value × List Char) :=
  let (run, rest) := collectRun (fun c => pred c || c = '_') cs
  if !validDigitRun pred run then none
  else
    let v := foldDigitsBase base (runDigits val run)
    if v ≤ 9223372036854775807 then some (.int (v : Int), rest) else none

def parseExp (cs : List Char) : Option (Int × List Char) :=
  match cs with
  | 'e' :: rest => parseExpBody rest
  | 'E' :: rest => parseExpBody rest
  | _ => none
where
  parseExpBody (rest : List Char) : Option (Int × List Char) :=
    let (neg, rest2) := parseSign rest
    let (run, rest3) := collectRun (fun c => isDigitChar c || c = '_') rest2
    if !validDigitRun isDigitChar run then none
    else
      let v := foldDigitsBase 10 (runDigits digitVal run)
      some ((if neg then -(v : Int) else (v : Int)), rest3)

def parseDecNumber (neg : Bool) (cs : List Char) :
    Option (Value × List Char) :=
  let (run, rest) := collectRun (fun c => isDigitChar c || c = '_') cs
  if run.isEmpty || !validDigitRun isDigitChar run then none
  else
    let leadingZero :=
      match run with
      | c :: _ => run.length > 1 && c = '0'
      | [] => false
    if leadingZero then none
    else
      let intDs := runDigits digitVal run
      match rest with
      | '.' :: rest2 =>
        let (frun, rest3) :=
          collectRun (fun c => isDigitChar c || c = '_') rest2
        if frun.isEmpty || !validDigitRun isDigitChar frun then none
        else
          let fracDs := runDigits digitVal frun
          match parseExp rest3 with
          | some (e, rest4) => some (.flt (.fin neg intDs fracDs e), rest4)
          | none => some (.flt (.fin neg intDs fracDs 0), rest3)
      | _ =>
        match parseExp rest with
        | some (e, rest2) => some (.flt (.fin neg intDs [] e), rest2)
        | none =>
          let v := foldDigitsBase 10 intDs
          if neg then
            if v ≤ 9223372036854775808 then some (.int (-(v : Int)), rest)
            else none
          else
            if v ≤ 9223372036854775807 then some (.int (v : Int), rest)
            else none

def parseNumber (neg : Bool) (cs : List Char) :
    Option (Value × List Char) :=
  match cs with
  | '0' :: 'x' :: rest => if neg then none else parseBaseInt 16 isHexChar hexValTotal rest
  | '0' :: 'o' :: rest =>
    if neg then none
    else parseBaseInt 8 (fun c => decide ('0' ≤ c && c ≤ '7')) digitVal rest
  | '0' :: 'b' :: rest =>
    if neg then none
    else parseBaseInt 2 (fun c => c = '0' || c = '1') digitVal rest
  | _ => parseDecNumber neg cs

/-- A signed number: a sign on a base integer is rejected, since
    the sign was already consumed by the caller. -/
def parseNumberSigned (neg : Bool) (cs : List Char) :
    Option (Value × List Char) :=
  match cs with
  | '0' :: 'x' :: _ => none
  | '0' :: 'o' :: _ => none
  | '0' :: 'b' :: _ => none
  | _ => parseNumber neg cs


def parseDateParts (cs : List Char) : Option (TDate × List Char) :=
  match takeNDigits 4 cs with
  | none => none
  | some (y, r1) =>
    match r1 with
    | '-' :: r2 =>
      match takeNDigits 2 r2 with
      | none => none
      | some (m, r3) =>
        match r3 with
        | '-' :: r4 =>
          match takeNDigits 2 r4 with
          | none => none
          | some (d, r5) =>
            some (⟨foldDigitsBase 10 y, foldDigitsBase 10 m,
              foldDigitsBase 10 d⟩, r5)
        | _ => none
    | _ => none

def parseTimeParts (cs : List Char) : Option (TTime × List Char) :=
  match takeNDigits 2 cs with
  | none => none
  | some (h, r1) =>
    match r1 with
    | ':' :: r2 =>
      match takeNDigits 2 r2 with
      | none => none
      | some (mi, r3) =>
        match r3 with
        | ':' :: r4 =>
          match takeNDigits 2 r4 with
          | none => none
          | some (s, r5) =>
            match r5 with
            | '.' :: r6 =>
              let (frun, r7) := collectRun isDigitChar r6
              if frun.isEmpty then none
              else
                some (⟨foldDigitsBase 10 h, foldDigitsBase 10 mi,
                  foldDigitsBase 10 s, runDigits digitVal frun⟩, r7)
            | _ =>
              some (⟨foldDigitsBase 10 h, foldDigitsBase 10 mi,
                foldDigitsBase 10 s, []⟩, r5)
        | _ => none
    | _ => none

def parseOffset (cs : List Char) : Option (TOffset × List Char) :=
  match cs with
  | 'Z' :: rest => some (.z, rest)
  | 'z' :: rest => some (.z, rest)
  | '+' :: rest => parseOffsetBody true rest
  | '-' :: rest => parseOffsetBody false rest
  | _ => none
where
  parseOffsetBody (pos : Bool) (rest : List Char) :
      Option (TOffset × List Char) :=
    match takeNDigits 2 rest with
    | none => none
    | some (h, r1) =>
      match r1 with
      | ':' :: r2 =>
        match takeNDigits 2 r2 with
        | none => none
        | some (mi, r3) =>
          let o := if pos then .plus (foldDigitsBase 10 h)
              (foldDigitsBase 10 mi)
            else .minus (foldDigitsBase 10 h) (foldDigitsBase 10 mi)
          some (o, r3)
      | _ => none

def parseTimeAndOffset (d : TDate) (cs : List Char) :
    Option (Value × List Char) :=
  match parseTimeParts cs with
  | none => none
  | some (t, rest) =>
    match rest with
    | 'Z' :: r | 'z' :: r =>
      let dt := .offsetDT d t .z
      if validDateTime dt then some (.dt dt, r) else none
    | '+' :: _ | '-' :: _ =>
      match parseOffset rest with
      | none => none
      | some (o, r) =>
        let dt := .offsetDT d t o
        if validDateTime dt then some (.dt dt, r) else none
    | _ =>
      let dt := .localDT d t
      if validDateTime dt then some (.dt dt, rest) else none

def parseDateTimeValue (cs : List Char) : Option (Value × List Char) :=
  match parseDateParts cs with
  | none => none
  | some (d, rest) =>
    match rest with
    | 'T' :: r => parseTimeAndOffset d r
    | 't' :: r => parseTimeAndOffset d r
    | ' ' :: r2 =>
      match r2 with
      | a :: b :: ':' :: _ =>
        if isDigitChar a && isDigitChar b then parseTimeAndOffset d r2
        else
          let dt := .localDate d
          if validDateTime dt then some (.dt dt, rest) else none
      | _ =>
        let dt := .localDate d
        if validDateTime dt then some (.dt dt, rest) else none
    | _ =>
      let dt := .localDate d
      if validDateTime dt then some (.dt dt, rest) else none

def parseTimeValue (cs : List Char) : Option (Value × List Char) :=
  match parseTimeParts cs with
  | none => none
  | some (t, rest) =>
    let dt := .localTime t
    if validDateTime dt then some (.dt dt, rest) else none

def looksLikeDate (cs : List Char) : Bool :=
  match cs with
  | a :: b :: c :: d :: '-' :: _ =>
    isDigitChar a && isDigitChar b && isDigitChar c && isDigitChar d
  | _ => false

def looksLikeTime (cs : List Char) : Bool :=
  match cs with
  | a :: b :: ':' :: _ => isDigitChar a && isDigitChar b
  | _ => false

def listPrefix : List String -> List String -> Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a = b && listPrefix as bs

def pathsConflict (p q : List String) : Bool :=
  listPrefix p q || listPrefix q p

def lookupNode : List (String × Node) -> String -> Option Node
  | [], _ => none
  | (k, n) :: rest, key => if k == key then some n else lookupNode rest key

def replaceEntry (entries : List (String × Node)) (key : String)
    (node : Node) : List (String × Node) :=
  entries.map (fun (k, n) => if k == key then (key, node) else (k, n))

def descend (entries : List (String × Node)) (key : String) :
    Option (List (String × Node)) :=
  match lookupNode entries key with
  | some (.table _ es) => some es
  | some (.arrTab tabs) => tabs.getLast?
  | _ => none

def resolveContext : List (String × Node) -> List String ->
    Option (List (String × Node))
  | entries, [] => some entries
  | entries, k :: rest =>
    match descend entries k with
    | some es => resolveContext es rest
    | none => none

def setContext : List (String × Node) -> List String ->
    List (String × Node) -> Option (List (String × Node))
  | _, [], newEs => some newEs
  | entries, k :: rest, newEs =>
    match lookupNode entries k with
    | some (.table st es) =>
      match setContext es rest newEs with
      | some es' => some (replaceEntry entries k (.table st es'))
      | none => none
    | some (.arrTab tabs) =>
      match tabs.getLast? with
      | some es =>
        match setContext es rest newEs with
        | some es' =>
          some (replaceEntry entries k (.arrTab (tabs.dropLast ++ [es'])))
        | none => none
      | none => none
    | _ => none

def insertPath : List (String × Node) -> List String -> Value ->
    Option (List (String × Node))
  | _, [], _ => none
  | entries, [k], v =>
    match lookupNode entries k with
    | some _ => none
    | none => some (entries ++ [(k, .leaf v)])
  | entries, k :: rest, v =>
    match lookupNode entries k with
    | none =>
      match insertPath [] rest v with
      | some es' => some (entries ++ [(k, .table .dotted es')])
      | none => none
    | some (.table st es) =>
      match insertPath es rest v with
      | some es' => some (replaceEntry entries k (.table st es'))
      | none => none
    | some _ => none

def insertKV (entries : List (String × Node)) (ctx : List String)
    (path : List String) (v : Value) : Option (List (String × Node)) :=
  match resolveContext entries ctx with
  | some es =>
    match insertPath es path v with
    | some es' => setContext entries ctx es'
    | none => none
  | none => none

def defineAt : List (String × Node) -> List String -> Bool ->
    Option (List (String × Node))
  | _, [], _ => none
  | entries, [k], false =>
    match lookupNode entries k with
    | none => some (entries ++ [(k, .table .explicit [])])
    | some (.table .implicit es) =>
      some (replaceEntry entries k (.table .explicit es))
    | some _ => none
  | entries, [k], true =>
    match lookupNode entries k with
    | none => some (entries ++ [(k, .arrTab [[]])])
    | some (.arrTab tabs) =>
      some (replaceEntry entries k (.arrTab (tabs ++ [[]])))
    | some _ => none
  | entries, k :: rest, isArr =>
    match lookupNode entries k with
    | none =>
      match defineAt [] rest isArr with
      | some es' => some (entries ++ [(k, .table .implicit es')])
      | none => none
    | some (.table st es) =>
      match defineAt es rest isArr with
      | some es' => some (replaceEntry entries k (.table st es'))
      | none => none
    | some (.arrTab tabs) =>
      match tabs.getLast? with
      | some es =>
        match defineAt es rest isArr with
        | some es' =>
          some (replaceEntry entries k (.arrTab (tabs.dropLast ++ [es'])))
        | none => none
      | none => none
    | some _ => none

def parseHeader : Nat -> List Char ->
    Option ((List String × Bool) × List Char)
  | _, cs =>
    match cs with
    | '[' :: rest =>
      match parseKeyPath 1000000 rest with
      | none => none
      | some (path, r) =>
        let r1 := skipWS r
        match r1 with
        | ']' :: ']' :: r2 => some ((path, true), r2)
        | _ => none
    | _ =>
      match parseKeyPath 1000000 cs with
      | none => none
      | some (path, r) =>
        let r1 := skipWS r
        match r1 with
        | ']' :: r2 => some ((path, false), r2)
        | _ => none

def expectLineEnd (cs : List Char) : Option (List Char) :=
  let cs1 := skipWS cs
  match cs1 with
  | [] => some []
  | '\n' :: rest => some rest
  | '\r' :: '\n' :: rest => some rest
  | '#' :: rest => some (skipToEOL rest)
  | _ => none

mutual
def parseValue : Nat -> List Char -> Option (Value × List Char)
  | 0, _ => none
  | f + 1, '"' :: rest =>
    match parseBasicContent f rest with
    | some (s, r) => some (.str s, r)
    | none => none
  | f + 1, '\'' :: rest =>
    match parseLiteralContent f rest with
    | some (s, r) => some (.str s, r)
    | none => none
  | f + 1, '[' :: rest =>
    let cs1 := skipWSNL f rest
    match cs1 with
    | ']' :: r => some (.arr [], r)
    | _ =>
      match parseArrayElems f [] cs1 with
      | some (vs, r) => some (.arr vs, r)
      | none => none
  | f + 1, '{' :: rest =>
    let cs1 := skipWS rest
    match cs1 with
    | '}' :: r => some (.inl [], r)
    | _ =>
      match parseInlineElems f [] cs1 with
      | some (es, r) => some (.inl es, r)
      | none => none
  | _f + 1, cs =>
    if startsWithChars "true".toList cs then
      match dropPrefix "true".toList cs with
      | some r => some (.bool true, r)
      | none => none
    else if startsWithChars "false".toList cs then
      match dropPrefix "false".toList cs with
      | some r => some (.bool false, r)
      | none => none
    else if startsWithChars "inf".toList cs then
      match dropPrefix "inf".toList cs with
      | some r => some (.flt (.inf false), r)
      | none => none
    else if startsWithChars "nan".toList cs then
      match dropPrefix "nan".toList cs with
      | some r => some (.flt (.nan false), r)
      | none => none
    else
      match cs with
      | '+' :: rest =>
        if startsWithChars "inf".toList rest then
          match dropPrefix "inf".toList rest with
          | some r => some (.flt (.inf false), r)
          | none => none
        else if startsWithChars "nan".toList rest then
          match dropPrefix "nan".toList rest with
          | some r => some (.flt (.nan false), r)
          | none => none
        else parseNumberSigned false rest
      | '-' :: rest =>
        if startsWithChars "inf".toList rest then
          match dropPrefix "inf".toList rest with
          | some r => some (.flt (.inf true), r)
          | none => none
        else if startsWithChars "nan".toList rest then
          match dropPrefix "nan".toList rest with
          | some r => some (.flt (.nan true), r)
          | none => none
        else parseNumberSigned true rest
      | _ =>
        if looksLikeDate cs then parseDateTimeValue cs
        else if looksLikeTime cs then parseTimeValue cs
        else parseNumber false cs

def parseArrayElems : Nat -> List Value -> List Char ->
    Option (List Value × List Char)
  | 0, _, _ => none
  | f + 1, acc, cs =>
    match parseValue f cs with
    | none => none
    | some (v, rest) =>
      let rest1 := skipWSNL f rest
      match rest1 with
      | ',' :: rest2 =>
        let rest3 := skipWSNL f rest2
        match rest3 with
        | ']' :: rest4 => some (acc ++ [v], rest4)
        | _ => parseArrayElems f (acc ++ [v]) rest3
      | ']' :: rest2 => some (acc ++ [v], rest2)
      | _ => none

def parseInlineElems : Nat -> List (List String × Value) -> List Char ->
    Option (List (List String × Value) × List Char)
  | 0, _, _ => none
  | f + 1, acc, cs =>
    match parseKeyPath f cs with
    | none => none
    | some (path, rest) =>
      let rest1 := skipWS rest
      match rest1 with
      | '=' :: rest2 =>
        let rest3 := skipWS rest2
        match parseValue f rest3 with
        | none => none
        | some (v, rest4) =>
          if acc.any (fun (p, _) => pathsConflict p path) then none
          else
            let rest5 := skipWS rest4
            match rest5 with
            | ',' :: rest6 =>
              let rest7 := skipWS rest6
              match rest7 with
              | '}' :: _ => none
              | _ => parseInlineElems f (acc ++ [(path, v)]) rest7
            | '}' :: rest6 => some (acc ++ [(path, v)], rest6)
            | _ => none
      | _ => none

def parseStatements : Nat -> List (String × Node) -> List String ->
    List Char -> Option (List (String × Node))
  | 0, _, _, _ => none
  | f + 1, entries, ctx, cs =>
    let cs1 := skipWSNL (f + 1) cs
    match cs1 with
    | [] => some entries
    | '[' :: rest =>
      match parseHeader f rest with
      | none => none
      | some ((path, isArr), rest2) =>
        match defineAt entries path isArr with
        | none => none
        | some entries' =>
          match expectLineEnd rest2 with
          | some rest3 => parseStatements f entries' path rest3
          | none => none
    | _ =>
      match parseKeyPath f cs1 with
      | none => none
      | some (path, rest) =>
        let rest1 := skipWS rest
        match rest1 with
        | '=' :: rest2 =>
          let rest3 := skipWS rest2
          match parseValue f rest3 with
          | none => none
          | some (v, rest4) =>
            match insertKV entries ctx path v with
            | none => none
            | some entries' =>
              match expectLineEnd rest4 with
              | some rest5 => parseStatements f entries' ctx rest5
              | none => none
        | _ => none
end

/-- Parse a whole document. Fuel is generous relative to length. -/
def parseDoc (s : String) : Option (List (String × Node)) :=
  parseStatements (s.toList.length * 8 + 100) [] [] s.toList

/-- Parse one value with nothing left over but spaces. -/
def parseValueFull (s : String) : Option Value :=
  match parseValue (s.toList.length * 8 + 100) (skipWS s.toList) with
  | some (v, rest) => if (skipWS rest).isEmpty then some v else none
  | none => none


end Toml
