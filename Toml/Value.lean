/- Value types, validity, and the canonical printer for the TOML
   subset first slice. The printer is structural recursion over the
   value and document trees. -/

namespace Toml

/-- A float kept as parsed parts, so printing is exact. `fin` holds
    the sign, the integer digits, the fraction digits, and the
    exponent (zero when no exponent was written). -/
inductive Flt where
  | fin : Bool -> List Nat -> List Nat -> Int -> Flt
  | inf : Bool -> Flt
  | nan : Bool -> Flt
deriving DecidableEq, Repr

structure TDate where
  year : Nat
  month : Nat
  day : Nat
deriving DecidableEq, Repr

structure TTime where
  hour : Nat
  minute : Nat
  second : Nat
  frac : List Nat
deriving DecidableEq, Repr

inductive TOffset where
  | z : TOffset
  | plus : Nat -> Nat -> TOffset
  | minus : Nat -> Nat -> TOffset
deriving DecidableEq, Repr

inductive DateTime where
  | offsetDT : TDate -> TTime -> TOffset -> DateTime
  | localDT : TDate -> TTime -> DateTime
  | localDate : TDate -> DateTime
  | localTime : TTime -> DateTime
deriving DecidableEq, Repr

/-- A value. Inline tables hold dotted key paths with their values;
    a regular table is a `Node`, not a value, because only inline
    tables may appear as values. -/
inductive Value where
  | str : String -> Value
  | int : Int -> Value
  | flt : Flt -> Value
  | bool : Bool -> Value
  | dt : DateTime -> Value
  | arr : List Value -> Value
  | inl : List (List String × Value) -> Value
deriving Repr

inductive TableStatus where
  | implicit : TableStatus
  | explicit : TableStatus
  | dotted : TableStatus
deriving DecidableEq, Repr

/-- A document node. `table` carries its status: implicit (created
    only as a parent), explicit (given a header), or dotted
    (created by dotted keys). `arrTab` is an array of tables. -/
inductive Node where
  | leaf : Value -> Node
  | table : TableStatus -> List (String × Node) -> Node
  | arrTab : List (List (String × Node)) -> Node
deriving Repr

def isLeapYear (y : Nat) : Bool :=
  (y % 4 == 0 && y % 100 != 0) || y % 400 == 0

def daysInMonth (y m : Nat) : Nat :=
  match m with
  | 2 => if isLeapYear y then 29 else 28
  | 4 => 30
  | 6 => 30
  | 9 => 30
  | 11 => 30
  | _ => 31

def validDate (d : TDate) : Bool :=
  1 ≤ d.month && d.month ≤ 12 && 1 ≤ d.day &&
    d.day ≤ daysInMonth d.year d.month

def validTime (t : TTime) : Bool :=
  t.hour ≤ 23 && t.minute ≤ 59 && t.second ≤ 59

def validOffset : TOffset -> Bool
  | .z => true
  | .plus h mi => h ≤ 23 && mi ≤ 59
  | .minus h mi => h ≤ 23 && mi ≤ 59

def validDateTime : DateTime -> Bool
  | .offsetDT d t o => validDate d && validTime t && validOffset o
  | .localDT d t => validDate d && validTime t
  | .localDate d => validDate d
  | .localTime t => validTime t

def digitsToString (ds : List Nat) : String :=
  String.ofList (ds.map (fun d => Char.ofNat (d + 48)))

def padLeft (c : Char) (w : Nat) (s : String) : String :=
  let n := s.length
  if n ≥ w then s else String.ofList (List.replicate (w - n) c) ++ s

def padNat (w : Nat) (n : Nat) : String :=
  padLeft '0' w (toString n)

def hexDigit (d : Nat) : Char :=
  if d < 10 then Char.ofNat (d + 48) else Char.ofNat (d + 87)

def hex4 (n : Nat) : String :=
  String.ofList [hexDigit (n / 4096 % 16), hexDigit (n / 256 % 16),
    hexDigit (n / 16 % 16), hexDigit (n % 16)]

def escapeChar (c : Char) : String :=
  if c = '"' then "\\\""
  else if c = '\\' then "\\\\"
  else if c.toNat = 8 then "\\b"
  else if c = '\t' then "\\t"
  else if c = '\n' then "\\n"
  else if c.toNat = 12 then "\\f"
  else if c = '\r' then "\\r"
  else if c.toNat < 32 || c.toNat = 127 then "\\u" ++ hex4 c.toNat
  else String.ofList [c]

def escapeString (s : String) : String :=
  String.ofList (s.toList.flatMap (fun c => (escapeChar c).toList))

def printFlt : Flt -> String
  | .fin neg intDs fracDs exp =>
    (if neg then "-" else "") ++ digitsToString intDs ++ "." ++
    digitsToString (if fracDs.isEmpty then [0] else fracDs) ++ "e" ++
    (if exp < 0 then "-" else "") ++ toString exp.natAbs
  | .inf neg => if neg then "-inf" else "inf"
  | .nan neg => if neg then "-nan" else "nan"

def printDate (d : TDate) : String :=
  padNat 4 d.year ++ "-" ++ padNat 2 d.month ++ "-" ++ padNat 2 d.day

def printTime (t : TTime) : String :=
  padNat 2 t.hour ++ ":" ++ padNat 2 t.minute ++ ":" ++
  padNat 2 t.second ++
  (if t.frac.isEmpty then "" else "." ++ digitsToString t.frac)

def printOffset : TOffset -> String
  | .z => "Z"
  | .plus h mi => "+" ++ padNat 2 h ++ ":" ++ padNat 2 mi
  | .minus h mi => "-" ++ padNat 2 h ++ ":" ++ padNat 2 mi

def printDateTime : DateTime -> String
  | .offsetDT d t o => printDate d ++ "T" ++ printTime t ++ printOffset o
  | .localDT d t => printDate d ++ "T" ++ printTime t
  | .localDate d => printDate d
  | .localTime t => printTime t

def isBareChar (c : Char) : Bool :=
  ('A' ≤ c && c ≤ 'Z') || ('a' ≤ c && c ≤ 'z') ||
  ('0' ≤ c && c ≤ '9') || c = '_' || c = '-'

def printKeyPart (k : String) : String :=
  if !k.isEmpty && k.toList.all isBareChar then k
  else "\"" ++ escapeString k ++ "\""

def printKeyPath (path : List String) : String :=
  String.intercalate "." (path.map printKeyPart)

/-- Printing with explicit fuel, like the parser: every nesting
    level consumes one unit, so termination is structural on fuel.
    `printValue` and `printDoc` use a large constant fuel that no
    real document reaches. -/
def printValueD : Nat -> Value -> String
  | 0, _ => ""
  | _ + 1, .str s => "\"" ++ escapeString s ++ "\""
  | _ + 1, .int i => toString i
  | _ + 1, .flt f => printFlt f
  | _ + 1, .bool b => if b then "true" else "false"
  | _ + 1, .dt d => printDateTime d
  | f + 1, .arr vs => "[" ++
      String.intercalate ", " (vs.map (printValueD f)) ++ "]"
  | f + 1, .inl es => "{" ++
      String.intercalate ", "
        (es.map (fun (p, v) => printKeyPath p ++ " = " ++ printValueD f v)) ++
      "}"

def printValue (v : Value) : String :=
  printValueD 1000000 v

def printHeader (path : List String) (isArray : Bool) : String :=
  if isArray then "[[" ++ printKeyPath path ++ "]]"
  else "[" ++ printKeyPath path ++ "]"

/-- Print one table level: its leaf entries first, then each
    subtable and array of tables as sections. Leaves always come
    before sections, which is what a reparse needs. -/
def printEntriesD : Nat -> List (String × Node) -> List String ->
    List String
  | 0, _, _ => []
  | f + 1, entries, path =>
    let leaves := entries.filterMap fun (k, n) =>
      match n with
      | .leaf v => some (printKeyPart k ++ " = " ++ printValueD f v)
      | _ => none
    let sections := entries.flatMap fun (k, n) =>
      match n with
      | .table _ es =>
        printHeader (path ++ [k]) false :: printEntriesD f es (path ++ [k])
      | .arrTab tabs =>
        tabs.flatMap fun es =>
          printHeader (path ++ [k]) true :: printEntriesD f es (path ++ [k])
      | _ => []
    leaves ++ sections

def printEntries (entries : List (String × Node)) (path : List String) :
    List String :=
  printEntriesD 1000000 entries path

def printDoc (entries : List (String × Node)) : String :=
  let lines := printEntries entries []
  if lines.isEmpty then "" else String.intercalate "\n" lines ++ "\n"

end Toml
