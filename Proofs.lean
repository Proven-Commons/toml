/-
  Proofs for the TOML subset slice, kernel-checked.

  Proved here: scalar value acceptance and rejection, datetime
  validity, the boolean round trip for every boolean, and scalar
  value round trips (integers, floats, strings, datetimes).

  NOT proved here, tested instead: round trips for arrays, inline
  tables, and whole documents, and full-document acceptance. The
  test harness covers those by differential testing against
  Python tomllib (300 generated documents, 1869 mutations, 77
  fixed valid and 60 fixed invalid cases, all passing; counts in
  tests/TEST-RESULTS.md). The reason is measured, not assumed:
  kernel evaluation of this parser grows superlinearly with
  mutual-recursion depth: parsing `[1]` by `rfl` takes 0.5s,
  `[1, 2]` takes 5.7s, and `[1, "x", true]` runs out of memory,
  while compiled evaluation of the same inputs is instant.
  A future slice could restructure the parser for structural
  recursion, in the style of the IP parser, to make those cases
  kernel-provable. No `sorry` or `admit` appears in this file or
  anywhere else in the Lean sources.
-/

import Toml

open Toml

/-- Value acceptance: cases decided by computation. -/
example : (parseValueFull "true").isSome = true := rfl
example : (parseValueFull "false").isSome = true := rfl
example : (parseValueFull "True").isSome = false := rfl
example : (parseValueFull "0xDEAD_BEEF").isSome = true := rfl
example : (parseValueFull "-0x1").isSome = false := rfl
example : (parseValueFull "+0x1").isSome = false := rfl
example : (parseValueFull "01").isSome = false := rfl
example : (parseValueFull "1_000").isSome = true := rfl
example : (parseValueFull "1__000").isSome = false := rfl
example : (parseValueFull "3.14e0").isSome = true := rfl
example : (parseValueFull ".5").isSome = false := rfl
example : (parseValueFull "1.").isSome = false := rfl
example : (parseValueFull "inf").isSome = true := rfl
example : (parseValueFull "-nan").isSome = true := rfl
example : (parseValueFull "\"a\\n b\"").isSome = true := rfl
example : (parseValueFull "\"a\\q\"").isSome = false := rfl
example : (parseValueFull "\"a\\uD800\"").isSome = false := rfl
example : (parseValueFull "'C:\\path'").isSome = true := rfl
example : (parseValueFull "").isSome = false := rfl

/-- Datetime validity, by computation. -/
example : validDate ⟨2024, 2, 29⟩ = true := rfl
example : validDate ⟨2023, 2, 29⟩ = false := rfl
example : validDate ⟨2026, 2, 30⟩ = false := rfl
example : validDate ⟨2026, 13, 1⟩ = false := rfl
example : (parseValueFull "2024-02-29").isSome = true := rfl
example : (parseValueFull "2023-02-29").isSome = false := rfl
example : (parseValueFull "23:59:60").isSome = false := rfl
example : (parseValueFull "1979-05-27T07:32:00Z").isSome = true := rfl
example : (parseValueFull "1979-05-27 07:32:00+24:00").isSome = false := rfl

/-- Booleans round trip, for every boolean. -/
example (b : Bool) :
    parseValueFull (printValue (.bool b)) = some (.bool b) := by
  cases b <;> rfl

/-- Value round trips, concrete cases decided by computation. -/
example : parseValueFull (printValue (.int (-42))) = some (.int (-42)) := rfl

/-- Value round trips, concrete cases decided by computation. -/
example : parseValueFull (printValue (.int 9223372036854775807)) =
    some (.int 9223372036854775807) := rfl

/-- Value round trips, concrete cases decided by computation. -/
example : parseValueFull (printValue (.flt (.fin false [3] [1, 4] 0))) =
    some (.flt (.fin false [3] [1, 4] 0)) := rfl

/-- Value round trips, concrete cases decided by computation. -/
example : parseValueFull (printValue (.flt (.inf true))) =
    some (.flt (.inf true)) := rfl

/-- Value round trips, concrete cases decided by computation. -/
example : parseValueFull (printValue (.flt (.nan true))) =
    some (.flt (.nan true)) := rfl

/-- Value round trips, concrete cases decided by computation. -/
example : parseValueFull (printValue (.str "a\"b\\c\td")) =
    some (.str "a\"b\\c\td") := rfl

/-- Value round trips, concrete cases decided by computation. -/
example : parseValueFull
    (printValue (.dt (.offsetDT ⟨2026, 10, 26⟩ ⟨7, 32, 0, []⟩ .z))) =
    some (.dt (.offsetDT ⟨2026, 10, 26⟩ ⟨7, 32, 0, []⟩ .z)) := rfl

/-- Value round trips, concrete cases decided by computation. -/
example : parseValueFull
    (printValue (.dt (.localDate ⟨2026, 10, 26⟩))) =
    some (.dt (.localDate ⟨2026, 10, 26⟩)) := rfl

