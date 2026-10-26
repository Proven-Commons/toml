# toml

A Lean parser and printer for TOML v1.0.0, subset first. See
`SPEC.md` for the grammar, the canonical printer, and what is
proved versus tested.

## Build

Lean 4.35.0, no dependencies:

```
lake build
```

## Test

```
python3 tests/run_tests.py
```

The harness runs the CLI over fixed cases, generated documents,
and mutated documents, and compares every result against Python
`tomllib`. Counts and the seed go to `tests/TEST-RESULTS.md`.

## Command line

One request per line. A request holds a document as decimal
character codes. The answer is the codes of the canonical
reprint, or `none` when the document is rejected:

```
parse 97 32 61 32 49
```

That request is the document `a = 1`. The answer is the codes
of `a = 1` followed by a newline.
