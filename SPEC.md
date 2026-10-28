# Specification: toml

A Lean parser and printer for TOML v1.0.0, subset first. A reviewer
who did not write this specification approves it, together with any
statement file a reviewer adds later. No such file exists yet, so
nothing here counts toward the verified bar yet.

Text is `String`, read as a list of characters. The parser never
does a lookup of any kind: parsing is purely syntactic.

## Values

- `str`: a single line basic string or literal string.
- `int`: a signed 64-bit integer.
- `flt`: a float kept as sign, integer digits, fraction digits,
  and exponent, plus signed `inf` and signed `nan`.
- `bool`: `true` or `false`.
- `dt`: an offset datetime, a local datetime, a local date, or a
  local time.
- `arr`: a list of values, nested.
- `inl`: an inline table, held as dotted key paths with values.

A regular table is not a value. It is a document node, because
only inline tables may appear as values.

## Documents

A document is a list of entries. Each entry is a key with a node:
a leaf value, a table, or an array of tables. A table carries a
status: implicit (created only as a parent), explicit (given a
header), or dotted (created by dotted keys).

## Keys

A key is a dotted list of key parts. A part is bare, basic quoted,
or literal quoted. Bare parts use ASCII letters, digits, `_`, and
`-`. A quoted part may be empty and may contain dots. Spaces and
tabs may surround dots and the equals sign.

## Strings

Basic strings use escapes `\b \t \n \f \r \" \\ \uXXXX
\UXXXXXXXX`. A unicode escape must name a scalar value: surrogates
and values above U+10FFFF are rejected. Raw control characters
other than tab are rejected, as is raw DEL. Literal strings have
no escapes. A backslash is an ordinary character. A raw newline
ends neither kind of string: both are single line only.
Multiline strings are outside the slice and are rejected.

## Integers

Decimal integers take an optional sign. Hexadecimal (`0x`),
octal (`0o`), and binary (`0b`) integers take no sign. Digits
may use underscores, but only between digits: a leading,
trailing, or doubled underscore is rejected. A decimal part with
a leading zero is rejected unless it is exactly `0`. Every
integer must fit in signed 64-bit range; a larger value is
rejected.

## Floats

A float is an integer part, an optional fraction, and an optional
exponent. The integer part follows the integer rules above,
including the leading zero rule. The fraction and exponent use
the underscore rule above. The exponent marker is `e` or `E`,
with an optional sign, and its digits may have leading zeros.
`inf` and `nan` take an optional sign.

## Datetimes

A date is four digit year, two digit month, two digit day, with
month 01 to 12 and a day valid for the month, leap rule included.
Year 0000 to 9999 is accepted. A time is two digit hour, minute,
and second, with hour 00 to 23, minute 00 to 59, second 00 to 59,
and optional fraction digits (no underscores). A datetime joins
a date and a time with `T`, `t`, or one space, and takes an
optional offset: `Z` or `z`, or `±HH:MM` with hour 00 to 23 and
minute 00 to 59. A date alone is a local date. A time alone is a
local time. A date and time without an offset is a local
datetime.

## Arrays and inline tables

Arrays hold values of mixed types, may span lines, may carry
comments, and may end with a trailing comma. Inline tables hold
key/value pairs on one line: no newlines, no trailing comma, and
no comment inside the braces. An inline table may hold dotted
keys, and two of its keys may not overlap: one may not equal
another or be a prefix of another. Arrays inside inline tables
may still span lines, as the array rule allows.

## Tables and arrays of tables

A header `[a.b]` defines a table. A header `[[a.b]]` appends an
element to an array of tables. The path is resolved from the
root, descending into the last element of any array of tables on
the way.

- Defining a table twice is rejected.
- Defining a table that dotted keys already created is rejected.
- Defining a table or array under a leaf or inline table is
  rejected.
- A dotted key may not overwrite a value, a table, or an array.
- A dotted key may traverse a table of any status, but not a
  leaf or an array of tables.
- A table created only as a parent may later gain a header.
  A table created only as a parent may not become an array.

After a header, key/value pairs belong to that table until the
next header. Comments and blank lines are allowed between
statements. Line endings are LF or CRLF. A byte order mark is
rejected.

## Canonical printer

The printer writes leaves first, then sections, at every table
level. Floats always carry an exponent, for example `25.5e0`.
Positive `inf` prints as `inf`, negative as `-inf`; `nan`
likewise. Datetimes print with `T` and `Z`. Keys print bare
when possible, quoted otherwise. Inline tables print with
`, ` between pairs. Arrays print with `, ` between values.
Every table, including a dotted one, prints as a header. That
means a reparse changes dotted tables to explicit ones. The
keys, values, and array order stay the same; only the status
changes.

## Command line

One request per line: `parse` followed by the document text as
decimal character codes, separated by spaces. The answer is the
codes of the canonical reprint, one line, or `none` when the
document is rejected, or `error` for a malformed request. An
empty document reprints as an empty line.

## Proved

Kernel-checked cases in `Toml/Proofs.lean`, with no sorry:

- Scalar acceptance and rejection: booleans, integers in all
  bases, floats, strings, escapes, and malformed values.
- Datetime validity: leap years, February 30, month 13, and
  the corresponding parse cases.
- The boolean round trip, for every boolean.
- Scalar round trips: integers, floats, strings, datetimes.

## Tested, not proved

General round trips for arrays, inline tables, and whole documents, and
full-document acceptance, are covered by differential testing
against Python `tomllib` in `tests/run_tests.py`, not by kernel
proof. The reason is measured: kernel evaluation of this parser
grows superlinearly with mutual-recursion depth (parsing `[1]`
by computation takes 0.5s, `[1, 2]` takes 5.7s, and a
three-element mixed array runs out of memory), while compiled
evaluation of the same inputs is instant. A future slice could
restructure the parser for structural recursion, in the style
of the IP parser, to make those cases kernel-provable.

## Known differences from Python tomllib

- Stricter: integers outside signed 64-bit range are rejected,
  including base integers. Python `tomllib` accepts them.
- Stricter: multiline strings are rejected. They sit outside
  this slice.
- Looser: year 0000 is accepted. The TOML grammar allows it;
  Python cannot represent it as a date.

## Limits

- No `Toml/Spec.lean` statements or bar files in this slice. A
  reviewer adds them, as in the other repos.
- No conversion to a host language value type beyond the
  printed form above.
- The parser fuel is eight times the input length plus 100.
  The printer fuel is 1000000 nesting levels. Neither binds on
  a real document.

## Collection proof work in progress

`Toml.singleton_int_array_roundtrip` proves that `[1]` prints and parses
back to the same array. `Toml.empty_collections_roundtrip` proves the
empty array and inline table cases. These run the actual parser and
printer in the kernel. They do not prove arbitrary collection values.

The remaining theorem must restrict values to the supported subset,
ensure sufficient printer and parser fuel, and account for canonical
float parts and unique inline-table keys. The desired array and inline
table statements preserve every valid element and key path. Document
round trips must compare semantic entries rather than table construction
status, because printed headers may make implicit tables explicit.
Those general statements and proofs remain in progress.
