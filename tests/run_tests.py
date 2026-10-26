#!/usr/bin/env python3
"""Test harness for the TOML subset slice.

Runs the Lean CLI once over every case (one `parse <codes>` request
per document), then compares against Python tomllib.

Categories:
  valid         Lean accepts, tomllib accepts, reprint parses to the
                same value as the original (semantic equality).
  invalid       Lean rejects and tomllib rejects.
  lean_stricter Lean rejects, tomllib accepts. Documented deviations
                only: 64-bit integer range, multiline strings
                (outside the slice).
  lean_looser   Lean accepts, tomllib rejects. Documented deviation
                only: year 0000, which TOML grammar allows but
                Python datetime cannot represent.
  mutation      a generated valid document with one fault applied.
                Lean must reject; tomllib agreement is recorded and
                any disagreement fails the run, so it cannot be
                ignored.

Usage: python3 tests/run_tests.py [--bin PATH] [--valid N]
       [--seed N]
"""

import argparse
import math
import os
import random
import re
import subprocess
import sys
import tomllib

HERE = os.path.dirname(os.path.abspath(__file__))
DEFAULT_BIN = os.path.join(os.path.dirname(HERE), ".lake", "build", "bin", "toml")
SEED = 20261026

# ---------------------------------------------------------------- fixed cases
# (name, document, category)

VALID = [
    ("empty document", "", "valid"),
    ("only comments", "# hello\n# world\n", "valid"),
    ("single key", 'title = "TOML Example"\n', "valid"),
    ("crlf endings", "a = 1\r\nb = 2\r\n", "valid"),
    ("trailing spaces", "a = 1   \n", "valid"),
    ("comment after value", "a = 1 # hi\n", "valid"),
    ("quoted dotted key", '"a.b" = 1\n', "valid"),
    ("empty quoted key", '"" = 1\n', "valid"),
    ("digits only key", "1234 = 1\n", "valid"),
    ("key spaces around dot", "a . b = 1\n", "valid"),
    ("header spaces", "[ a . b ]\nx = 1\n", "valid"),
    ("quoted header", '["a"."b"]\nx = 1\n', "valid"),
    ("no spaces around equals", "a=1\n", "valid"),
    ("tab separators", "a\t=\t1\n", "valid"),
    ("int zero", "a = 0\n", "valid"),
    ("int negative zero", "a = -0\n", "valid"),
    ("int plus", "a = +99\n", "valid"),
    ("int underscores", "a = 1_000_000\n", "valid"),
    ("int hex", "a = 0xDEAD_BEEF\n", "valid"),
    ("int octal", "a = 0o777\n", "valid"),
    ("int binary", "a = 0b1010\n", "valid"),
    ("int max", "a = 9223372036854775807\n", "valid"),
    ("int min", "a = -9223372036854775808\n", "valid"),
    ("float plain", "a = 3.14\n", "valid"),
    ("float exponent", "a = 5e+22\n", "valid"),
    ("float exponent leading zero", "a = 1e06\n", "valid"),
    ("float exponent underscores", "a = 1e1_0\n", "valid"),
    ("float underscores", "a = 1_000.5\n", "valid"),
    ("float frac underscores", "a = 1.0_1\n", "valid"),
    ("float inf", "a = inf\n", "valid"),
    ("float neg inf", "a = -inf\n", "valid"),
    ("float plus inf", "a = +inf\n", "valid"),
    ("float nan", "a = nan\n", "valid"),
    ("float neg nan", "a = -nan\n", "valid"),
    ("float neg zero", "a = -0.0\n", "valid"),
    ("bool true", "a = true\n", "valid"),
    ("bool false", "a = false\n", "valid"),
    ("basic string escapes", 'a = "tab\\there newline\\nhere quote\\"here"\n', "valid"),
    ("basic string unicode escape", 'a = "\\u00e9\\U0001F600"\n', "valid"),
    ("basic string unicode raw", 'a = "héllo 😀"\n', "valid"),
    ("literal backslash", "a = 'C:\\path\\to'\n", "valid"),
    ("literal double quote", 'a = \'say "hi"\'\n', "valid"),
    ("basic single quote", 'a = "it\'s"\n', "valid"),
    ("local date", "a = 2026-10-26\n", "valid"),
    ("local time", "a = 07:32:00\n", "valid"),
    ("time fraction", "a = 00:00:00.5\n", "valid"),
    ("offset datetime Z", "a = 1979-05-27T07:32:00Z\n", "valid"),
    ("offset datetime lower", "a = 1979-05-27t07:32:00z\n", "valid"),
    ("offset datetime space", "a = 1979-05-27 07:32:00Z\n", "valid"),
    ("offset datetime plus", "a = 1979-05-27T07:32:00+02:30\n", "valid"),
    ("offset datetime minus", "a = 1979-05-27T07:32:00-07:00\n", "valid"),
    ("local datetime", "a = 1979-05-27T07:32:00\n", "valid"),
    ("local datetime fraction", "a = 1979-05-27 07:32:00.123456789\n", "valid"),
    ("leap day", "a = 2024-02-29\n", "valid"),
    ("year 9999", "a = 9999-12-31\n", "valid"),
    ("time max", "a = 23:59:59\n", "valid"),
    ("array empty", "a = []\n", "valid"),
    ("array mixed", "a = [1, 'x', true, 2.5]\n", "valid"),
    ("array trailing comma", "a = [1, 2,]\n", "valid"),
    ("array multiline", "a = [1,\n2,\n3]\n", "valid"),
    ("array comment", "a = [1, # hi\n2]\n", "valid"),
    ("array nested", "a = [[1, 2], ['x']]\n", "valid"),
    ("inline empty", "a = {}\n", "valid"),
    ("inline dotted", "a = {b.c = 1, d = 2}\n", "valid"),
    ("inline nested", "a = {b = {c = 1}}\n", "valid"),
    ("inline in array", "a = [{b = 1, c = 2}]\n", "valid"),
    ("array newline in inline", "a = {b = [1,\n2]}\n", "valid"),
    ("table", "[a]\nx = 1\n", "valid"),
    ("table then subtable", "[a]\nx = 1\n[a.b]\ny = 2\n", "valid"),
    ("implicit parent then header", "[a.b]\nx = 1\n[a]\ny = 2\n", "valid"),
    ("dotted then subtable header", "[fruit]\napple.color = 'red'\n[fruit.apple.texture]\nsmooth = true\n", "valid"),
    ("dotted keys in table", "[a]\nb.c = 1\nb.d = 2\n", "valid"),
    ("array of tables", "[[a]]\nx = 1\n[[a]]\nx = 2\n", "valid"),
    ("array of tables dotted", "[[a.b]]\nx = 1\n[[a.b]]\nx = 2\n", "valid"),
    ("table under array element", "[[a]]\nx = 1\n[a.b]\ny = 2\n", "valid"),
    ("second element subtable", "[[a]]\nx = 1\n[a.b]\ny = 2\n[[a]]\nx = 3\n", "valid"),
    ("spec style example",
     'title = "TOML Example"\n\n[owner]\nname = "Tom Jones"\n'
     'dob = 1979-05-27T07:32:00Z\n\n[database]\nports = [8000, 8001, 8002]\n'
     'temp = 25.5\n\n[servers.alpha]\nip = "10.0.0.1"\ndc = "eqdc10"\n\n'
     '[servers.beta]\nip = "10.0.0.2"\ndc = "eqdc10"\n', "valid"),
]

INVALID = [
    ("duplicate key", "a = 1\na = 2\n", "invalid"),
    ("duplicate dotted key", "a.b = 1\na = 2\n", "invalid"),
    ("duplicate dotted leaf", "[a]\nb.c = 1\nb.c = 2\n", "invalid"),
    ("redefine table", "[a]\nx = 1\n[a]\ny = 2\n", "invalid"),
    ("header after dotted", "[fruit]\napple.color = 'red'\n[fruit.apple]\n", "invalid"),
    ("header after inline", "a = {b = 1}\n[a]\n", "invalid"),
    ("inline then dotted", "a = {b = 1}\na.b = 2\n", "invalid"),
    ("inline duplicate", "a = {b = 1, b = 2}\n", "invalid"),
    ("inline dotted conflict", "a = {b.c = 1, b = 2}\n", "invalid"),
    ("inline trailing comma", "a = {b = 1,}\n", "invalid"),
    ("inline newline", "a = {b = 1,\nc = 2}\n", "invalid"),
    ("inline comment", "a = {b = 1 # hi\n}\n", "invalid"),
    ("nested inline newline", "a = {b = {c = 1,\nd = 2}}\n", "invalid"),
    ("inline newline in array", "a = [{b = 1,\nc = 2}]\n", "invalid"),
    ("array of tables conflict", "[[a]]\nb = 1\n[[a.b]]\nc = 2\n", "invalid"),
    ("key after subtable header", "[a]\nb = 1\n[a.c]\nd = 2\n[a]\ne = 3\n", "invalid"),
    ("int leading zero", "a = 01\n", "invalid"),
    ("float leading zero", "a = 01.0\n", "invalid"),
    ("int underscore lead", "a = _100\n", "invalid"),
    ("int underscore trail", "a = 100_\n", "invalid"),
    ("int underscore double", "a = 1__000\n", "invalid"),
    ("hex underscore lead", "a = 0x_1\n", "invalid"),
    ("hex sign plus", "a = +0x1\n", "invalid"),
    ("hex sign minus", "a = -0x1\n", "invalid"),
    ("exp underscore lead", "a = 1e_10\n", "invalid"),
    ("exp underscore trail", "a = 1e10_\n", "invalid"),
    ("datetime frac underscore", "a = 2026-01-01T00:00:00.1_2\n", "invalid"),
    ("bad escape", 'a = "\\q"\n', "invalid"),
    ("bad slash escape", 'a = "\\/ "\n', "invalid"),
    ("surrogate escape", 'a = "\\uD800"\n', "invalid"),
    ("escape too large", 'a = "\\U00110000"\n', "invalid"),
    ("raw del in string", 'a = "x\x7fy"\n', "invalid"),
    ("raw newline in string", 'a = "x\ny"\n', "invalid"),
    ("literal escaped quote", "a = 'it\\'s'\n", "invalid"),
    ("string then junk", 'a = "x""\n', "invalid"),
    ("feb 30", "a = 2026-02-30\n", "invalid"),
    ("feb 29 non leap", "a = 2023-02-29\n", "invalid"),
    ("month zero", "a = 2026-00-01\n", "invalid"),
    ("day zero", "a = 2026-01-00\n", "invalid"),
    ("hour 24", "a = 24:00:00\n", "invalid"),
    ("leap second", "a = 23:59:60\n", "invalid"),
    ("offset hour 24", "a = 2026-01-01T00:00:00+24:00\n", "invalid"),
    ("offset minute 60", "a = 2026-01-01T00:00:00+00:60\n", "invalid"),
    ("offset no colon", "a = 2026-01-01T00:00:00+0000\n", "invalid"),
    ("time no seconds", "a = 12:30\n", "invalid"),
    ("date time sep tab", "a = 2026-01-01\t00:00:00\n", "invalid"),
    ("date only with T", "a = 2026-01-01T\n", "invalid"),
    ("float no int part", "a = .5\n", "invalid"),
    ("float no frac digits", "a = 1.\n", "invalid"),
    ("bool caps", "a = True\n", "invalid"),
    ("empty header", "[]\n", "invalid"),
    ("header dot only", "[.]\n", "invalid"),
    ("key empty dotted", "a. = 1\n", "invalid"),
    ("value missing", "a =\n", "invalid"),
    ("array value newline after equals", "a =\n[1]\n", "invalid"),
    ("array comma only", "a = [,]\n", "invalid"),
    ("garbage after value", "a = 1 garbage\n", "invalid"),
    ("semicolon", "a = 1;\n", "invalid"),
    ("bom", "\ufeffa = 1\n", "invalid"),
    ("bare unicode key", "café = 1\n", "invalid"),
]

DEVIATIONS = [
    ("int decimal overflow", "a = 9223372036854775808\n", "lean_stricter"),
    ("int hex overflow", "a = 0x8000000000000000\n", "lean_stricter"),
    ("multiline basic string", 'a = """x"""\n', "lean_stricter"),
    ("multiline literal string", "a = '''x'''\n", "lean_stricter"),
    ("year zero", "a = 0000-01-01\n", "lean_looser"),
]

FIXED = VALID + INVALID + DEVIATIONS

# ---------------------------------------------------------------- CLI plumbing

def encode_request(doc):
    return "parse " + " ".join(str(ord(c)) for c in doc) if doc else "parse"


def decode_response(line):
    if line == "none" or line == "error":
        return line
    if line == "":
        return ""
    return "".join(chr(int(x)) for x in line.split(" "))


def run_cli(binary, requests):
    req_text = "\n".join(requests) + "\n"
    proc = subprocess.run([binary, "/dev/stdin"], input=req_text,
                          capture_output=True, text=True, timeout=600)
    if proc.returncode != 0:
        raise RuntimeError(f"CLI failed: {proc.stderr[:500]}")
    out = proc.stdout
    if out.endswith("\n"):
        out = out[:-1]
    lines = out.split("\n") if out != "" else []
    if len(lines) != len(requests):
        raise RuntimeError(
            f"response count {len(lines)} != request count {len(requests)}")
    return lines


# ---------------------------------------------------------------- semantic equality

def sem_eq(a, b):
    if isinstance(a, float) or isinstance(b, float):
        if type(a) is not float or type(b) is not float:
            return False
        if math.isnan(a) and math.isnan(b):
            return math.copysign(1, a) == math.copysign(1, b)
        return a == b
    if type(a) is not type(b):
        return False
    if isinstance(a, dict):
        return a.keys() == b.keys() and all(sem_eq(a[k], b[k]) for k in a)
    if isinstance(a, list):
        return len(a) == len(b) and all(sem_eq(x, y) for x, y in zip(a, b))
    return a == b


def tomllib_parse(doc):
    try:
        return ("ok", tomllib.loads(doc))
    except Exception as e:
        return ("err", str(e)[:120])


# ---------------------------------------------------------------- generator

WORDS = ["alpha", "beta", "gamma", "delta", "name", "title", "count",
         "port", "host", "path", "mode", "size", "rate", "flag", "key"]
SAFE_CHARS = "abc XYZ 012 _-./:;+@%()"


def gen_string(rng):
    kind = rng.choice(["basic", "basic", "literal", "plain"])
    n = rng.randint(0, 12)
    chars = []
    for _ in range(n):
        r = rng.random()
        if r < 0.6:
            chars.append(rng.choice(SAFE_CHARS))
        elif r < 0.7:
            chars.append(rng.choice("éü😀"))
        elif r < 0.8:
            chars.append("\t")
        elif r < 0.9:
            chars.append("\n")
        else:
            chars.append(rng.choice(['"', "\\", "'"]))
    s = "".join(chars)
    if kind == "literal":
        # literal strings: no quote, no newline, no carriage return,
        # no control characters other than tab.
        s = s.replace("'", "_").replace("\n", " ").replace("\r", " ")
        return "'" + s + "'"
    out = []
    for c in s:
        if c == '"':
            out.append('\\"')
        elif c == "\\":
            out.append("\\\\")
        elif c == "\n":
            out.append("\\n")
        elif c == "\r":
            out.append("\\r")
        elif c == "\t":
            out.append("\\t")
        elif ord(c) < 32:
            out.append("\\u%04x" % ord(c))
        else:
            out.append(c)
    return '"' + "".join(out) + '"'


def underscore_digits(rng, digits):
    if len(digits) < 4 or rng.random() < 0.6:
        return digits
    out = []
    for i, d in enumerate(digits):
        out.append(d)
        if i < len(digits) - 1 and rng.random() < 0.4:
            out.append("_")
    # never end with an underscore, never double one
    text = "".join(out).replace("__", "_")
    return text.rstrip("_") or digits


def gen_int(rng):
    form = rng.random()
    if form < 0.55:
        v = rng.choice([0, 1, 42, 1000, 123456, 9223372036854775807,
                        -9223372036854775808, -7, 99])
        if rng.random() < 0.3:
            v = rng.randint(-10 ** 9, 10 ** 9)
        sign = "-" if v < 0 else ("+" if rng.random() < 0.15 else "")
        return sign + underscore_digits(rng, str(abs(v)))
    if form < 0.7:
        v = rng.randint(0, 2 ** 31)
        return "0x" + underscore_digits(rng, format(v, "X"))
    if form < 0.85:
        v = rng.randint(0, 511)
        return "0o" + underscore_digits(rng, format(v, "o"))
    v = rng.randint(0, 255)
    return "0b" + underscore_digits(rng, format(v, "b"))


def gen_float(rng):
    form = rng.random()
    if form < 0.15:
        return rng.choice(["inf", "-inf", "+inf", "nan", "-nan", "+nan"])
    ip = str(rng.randint(0, 9999))
    fp = str(rng.randint(0, 99999))
    if rng.random() < 0.4:
        ip = underscore_digits(rng, ip)
    if rng.random() < 0.3:
        fp = underscore_digits(rng, fp)
    sign = "-" if rng.random() < 0.2 else ""
    base = sign + ip + "." + fp
    if rng.random() < 0.45:
        exp = rng.randint(-30, 30)
        esign = "+" if exp >= 0 and rng.random() < 0.4 else ""
        etext = str(abs(exp))
        if rng.random() < 0.25:
            etext = underscore_digits(rng, etext)
        base += "e" + esign + etext
    return base


def gen_datetime(rng):
    year = rng.randint(1, 9999)
    month = rng.randint(1, 12)
    mdays = [31, 29 if (year % 4 == 0 and (year % 100 != 0 or year % 400 == 0))
             else 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31][month - 1]
    day = rng.randint(1, mdays)
    date = "%04d-%02d-%02d" % (year, month, day)
    kind = rng.random()
    if kind < 0.25:
        return date
    hh = rng.randint(0, 23)
    mm = rng.randint(0, 59)
    ss = rng.randint(0, 59)
    time = "%02d:%02d:%02d" % (hh, mm, ss)
    if rng.random() < 0.3:
        time += "." + "".join(rng.choice("0123456789")
                               for _ in range(rng.randint(1, 6)))
    if kind < 0.45:
        return time
    sep = rng.choice(["T", "t", " "])
    base = date + sep + time
    if kind < 0.75:
        off = rng.choice(["Z", "z"])
        if rng.random() < 0.6:
            oh = rng.randint(0, 23)
            om = rng.randint(0, 59)
            off = "%s%02d:%02d" % (rng.choice(["+", "-"]), oh, om)
        return base + off
    return base


def gen_scalar(rng, depth):
    r = rng.random()
    if r < 0.22:
        return gen_int(rng)
    if r < 0.38:
        return gen_float(rng)
    if r < 0.48:
        return rng.choice(["true", "false"])
    if r < 0.68:
        return gen_string(rng)
    if r < 0.88:
        return gen_datetime(rng)
    if depth < 2:
        return gen_array(rng, depth + 1)
    return gen_int(rng)


def gen_array(rng, depth):
    n = rng.randint(0, 4)
    items = [gen_scalar(rng, depth) for _ in range(n)]
    if n == 0:
        return "[]"
    if rng.random() < 0.3 and n > 1:
        body = ",\n".join(items)
        return "[\n" + body + ",\n]"
    return "[" + ", ".join(items) + "]"


def gen_inline(rng, depth):
    n = rng.randint(0, 3)
    parts = []
    for i in range(n):
        key = rng.choice(WORDS) + str(i)
        if rng.random() < 0.25:
            key = key + "." + rng.choice(WORDS)
        if depth < 1 and rng.random() < 0.2:
            val = gen_inline(rng, depth + 1)
        else:
            val = gen_scalar(rng, depth)
        parts.append(key + " = " + val)
    return "{" + ", ".join(parts) + "}"


def gen_value(rng, depth):
    if rng.random() < 0.18:
        return gen_inline(rng, depth)
    return gen_scalar(rng, depth)


def render_key(rng, key):
    if rng.random() < 0.12:
        return '"%s.%s"' % (key, rng.choice(WORDS))
    if rng.random() < 0.05:
        return '"%s"' % key
    return key


class Table(dict):
    pass


class ArrTab(list):
    pass


def gen_table(rng, depth, used):
    entries = Table()
    n = rng.randint(1, 4)
    for _ in range(n):
        key = rng.choice(WORDS)
        while key in entries:
            key = rng.choice(WORDS) + str(rng.randint(0, 99))
        r = rng.random()
        if depth < 2 and r < 0.35:
            entries[key] = gen_table(rng, depth + 1, used)
        elif depth < 2 and r < 0.55:
            elems = [gen_table(rng, depth + 1, used)
                     for _ in range(rng.randint(1, 2))]
            entries[key] = ArrTab(elems)
        else:
            entries[key] = gen_value(rng, depth)
    return entries


def render_entries(rng, entries, path, lines):
    # Three phases, in order, all inside this table's context:
    # leaves, dotted-rendered child tables, then section headers.
    # Dotted lines must come before any section header, or they
    # would land inside that section instead of this table.
    for key, node in entries.items():
        if isinstance(node, (Table, ArrTab)):
            continue
        lines.append("%s = %s" % (render_key(rng, key), node))
    dotted = {}
    for key, node in entries.items():
        if isinstance(node, Table) and all(
                not isinstance(v, (Table, ArrTab))
                for v in node.values()) and rng.random() < 0.35:
            dotted[key] = node
    for key, node in dotted.items():
        for ck, cv in node.items():
            lines.append("%s.%s = %s" % (
                render_key(rng, key), render_key(rng, ck), cv))
    for key, node in entries.items():
        if isinstance(node, Table):
            if key in dotted:
                continue
            header = ".".join(path + [key])
            lines.append("[%s]" % header)
            render_entries(rng, node, path + [key], lines)
        elif isinstance(node, ArrTab):
            for elem in node:
                header = ".".join(path + [key])
                lines.append("[[%s]]" % header)
                render_entries(rng, elem, path + [key], lines)


def gen_doc(rng):
    root = gen_table(rng, 0, set())
    lines = []
    render_entries(rng, root, [], lines)
    doc = ""
    for line in lines:
        if rng.random() < 0.12:
            doc += "# note\n"
        if rng.random() < 0.08:
            doc += "\n"
        doc += line + "\n"
    if rng.random() < 0.12:
        doc = doc.replace("\n", "\r\n")
    return doc


# ---------------------------------------------------------------- mutations

def scan_depths(doc):
    """Return, for each line, the bracket depth at its start, tracking
    strings so brackets inside strings do not count."""
    depths = []
    depth = 0
    in_basic = False
    in_literal = False
    esc = False
    for line in doc.split("\n"):
        depths.append(depth)
        for c in line:
            if in_basic:
                if esc:
                    esc = False
                elif c == "\\":
                    esc = True
                elif c == '"':
                    in_basic = False
            elif in_literal:
                if c == "'":
                    in_literal = False
            else:
                if c == '"':
                    in_basic = True
                elif c == "'":
                    in_literal = True
                elif c == "[":
                    depth += 1
                elif c == "]":
                    depth -= 1
    return depths


def mut_dup_line(doc):
    lines = doc.split("\n")
    depths = scan_depths(doc)
    for i, line in enumerate(lines):
        if depths[i] == 0 and "=" in line and not line.lstrip().startswith("#"):
            lines.insert(i + 1, line)
            return "\n".join(lines)
    return None


def mut_feb30(doc):
    new, n = re.subn(r"(\d{4})-02-\d\d", r"\1-02-30", doc, count=1)
    return new if n else None


def mut_leading_zero(doc):
    new, n = re.subn(r"=\s*([1-9][0-9]*)(?![0-9\-:])", r"= 0\1", doc, count=1)
    return new if n else None


def mut_redefine(doc):
    lines = doc.split("\n")
    array_paths = set()
    for line in lines:
        m = re.match(r"^\[\[([^\]]+)\]\]", line)
        if m:
            array_paths.add(m.group(1).strip())
    for line in lines:
        m = re.match(r"^\[([^\[\]]+)\]", line)
        if not m:
            continue
        segs = [s.strip().strip('"').strip("'")
                for s in m.group(1).split(".")]
        # Skip headers whose path crosses an array of tables: the
        # appended header would land in a different element, which
        # is a new table, not a redefinition.
        if any(".".join(segs[:k]) in array_paths
               for k in range(1, len(segs) + 1)):
            continue
        return doc + line + "\n"
    return None


def mut_true(doc):
    new, n = re.subn(r"=\s*true\b", "= True", doc, count=1)
    return new if n else None


def mut_hour24(doc):
    new, n = re.subn(r"([T ])(\d\d):(\d\d):(\d\d)", r"\g<1>24:\g<3>:\g<4>",
                     doc, count=1)
    return new if n else None


def mut_inline_comma(doc):
    idx = doc.find("}")
    if idx < 0:
        return None
    return doc[:idx] + ",}" + doc[idx + 1:]


def mut_unterminated(doc):
    return doc + '\nbroken = "abc'


def mut_garbage(doc):
    return doc + "\n@@@\n"


MUTATIONS = [
    ("dup_line", mut_dup_line),
    ("feb30", mut_feb30),
    ("leading_zero", mut_leading_zero),
    ("redefine_table", mut_redefine),
    ("true_to_True", mut_true),
    ("hour24", mut_hour24),
    ("inline_trailing_comma", mut_inline_comma),
    ("unterminated", mut_unterminated),
    ("garbage", mut_garbage),
]

# ---------------------------------------------------------------- main

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--bin", default=DEFAULT_BIN)
    ap.add_argument("--valid", type=int, default=300)
    ap.add_argument("--seed", type=int, default=SEED)
    args = ap.parse_args()
    binary = args.bin
    if not os.path.exists(binary):
        print(f"binary not found: {binary}", file=sys.stderr)
        return 2

    rng = random.Random(args.seed)
    cases = []  # (kind, name, doc, category)
    for name, doc, cat in FIXED:
        cases.append(("fixed", name, doc, cat))
    valid_docs = []
    for _ in range(args.valid):
        doc = gen_doc(rng)
        valid_docs.append(doc)
        cases.append(("valid", "generated", doc, "valid"))
    mut_cases = []
    for doc in valid_docs:
        for mname, fn in MUTATIONS:
            mutated = fn(doc)
            if mutated is not None:
                mut_cases.append((mname, doc, mutated))

    requests = [encode_request(c[2]) for c in cases]
    responses = run_cli(binary, requests)
    failures = []
    fixed_valid_ok = 0
    gen_valid_ok = 0
    counts = {"valid_ok": 0, "valid_fail": 0, "invalid_ok": 0,
              "invalid_fail": 0, "stricter_ok": 0, "looser_ok": 0,
              "mutation_ok": 0, "mutation_fail": 0,
              "mutation_tomllib_agree": 0, "mutation_tomllib_disagree": 0}

    for (kind, name, doc, cat), resp in zip(cases, responses):
        decoded = decode_response(resp)
        lean = "reject" if decoded in ("none", "error") else "accept"
        status, orig = tomllib_parse(doc)
        if cat == "valid":
            if status != "ok":
                failures.append((name, "generator produced invalid doc", doc))
                counts["valid_fail"] += 1
            elif lean != "accept":
                failures.append((name, "valid doc rejected by Lean", doc))
                counts["valid_fail"] += 1
            else:
                re_status, re_val = tomllib_parse(decoded)
                if re_status != "ok" or not sem_eq(orig, re_val):
                    failures.append((name, "reprint mismatch", doc))
                    counts["valid_fail"] += 1
                else:
                    counts["valid_ok"] += 1
                    if kind == "fixed":
                        fixed_valid_ok += 1
                    else:
                        gen_valid_ok += 1
        elif cat == "invalid":
            if lean != "reject" or status != "err":
                failures.append((name,
                                 f"expected reject, lean={lean} "
                                 f"tomllib={status}", doc))
                counts["invalid_fail"] += 1
            else:
                counts["invalid_ok"] += 1
        elif cat == "lean_stricter":
            if lean != "reject" or status != "ok":
                failures.append((name,
                                 f"expected lean reject/tomllib accept, "
                                 f"lean={lean} tomllib={status}", doc))
            else:
                counts["stricter_ok"] += 1
        elif cat == "lean_looser":
            if lean != "accept" or status != "err":
                failures.append((name,
                                 f"expected lean accept/tomllib reject, "
                                 f"lean={lean} tomllib={status}", doc))
            else:
                counts["looser_ok"] += 1

    mut_requests = [encode_request(m[2]) for m in mut_cases]
    mut_responses = run_cli(binary, mut_requests) if mut_requests else []
    mut_disagreements = []
    for (mname, orig, mutated), resp in zip(mut_cases, mut_responses):
        decoded = decode_response(resp)
        lean = "reject" if decoded in ("none", "error") else "accept"
        status, _ = tomllib_parse(mutated)
        if lean != "reject":
            failures.append((f"mutation {mname}",
                             "mutated doc accepted by Lean", mutated))
            counts["mutation_fail"] += 1
        else:
            counts["mutation_ok"] += 1
        if status == "err":
            counts["mutation_tomllib_agree"] += 1
        else:
            counts["mutation_tomllib_disagree"] += 1
            mut_disagreements.append((mname, mutated))

    malformed = ["bogus 1 2", "parse abc", "parse 99999999", "parse -1",
                 "parse 55296", "parse"]
    mal_expected = ["error", "error", "error", "error", "error", ""]
    mal_responses = run_cli(binary, malformed)
    mal_ok = True
    for req, got, want in zip(malformed, mal_responses, mal_expected):
        if got != want:
            mal_ok = False
            failures.append((f"malformed {req!r}",
                             f"expected {want!r} got {got!r}", req))

    total_fixed_valid = sum(1 for _, _, c in FIXED if c == "valid")
    total_fixed_invalid = sum(1 for _, _, c in FIXED if c == "invalid")
    report = []
    report.append("# TOML subset test results\n")
    report.append(f"Seed: {args.seed}\n")
    report.append(f"Binary: {binary}\n")
    report.append(f"Fixed valid passed: {fixed_valid_ok} "
                  f"out of {total_fixed_valid}.\n")
    report.append(f"Generated valid passed: {gen_valid_ok} "
                  f"out of {args.valid}.\n")
    report.append(f"Valid failed: {counts['valid_fail']}.\n")
    report.append(f"Fixed invalid passed: {counts['invalid_ok']} "
                  f"out of {total_fixed_invalid}, "
                  f"failed: {counts['invalid_fail']}.\n")
    report.append(f"Lean stricter (documented): {counts['stricter_ok']} "
                  f"out of 4.\n")
    report.append(f"Lean looser (documented): {counts['looser_ok']} "
                  f"out of 1.\n")
    report.append(f"Mutations rejected by Lean: {counts['mutation_ok']} "
                  f"out of {len(mut_cases)}, failed: "
                  f"{counts['mutation_fail']}.\n")
    report.append(f"Mutations where tomllib also rejects: "
                  f"{counts['mutation_tomllib_agree']}, where tomllib "
                  f"accepts (disagreement): "
                  f"{counts['mutation_tomllib_disagree']}.\n")
    report.append(f"Malformed requests: {'pass' if mal_ok else 'FAIL'}.\n")
    report.append(f"Failures: {len(failures)}.\n")
    if failures:
        report.append("\n## Failures\n")
        for name, why, doc in failures[:40]:
            report.append(f"\n### {name}: {why}\n```toml\n{doc}```\n")
    if mut_disagreements:
        report.append("\n## Mutation disagreements (tomllib accepts, "
                      "Lean rejects)\n")
        for mname, doc in mut_disagreements[:20]:
            report.append(f"\n### {mname}\n```toml\n{doc}```\n")
    out_path = os.path.join(HERE, "TEST-RESULTS.md")
    with open(out_path, "w") as f:
        f.write("".join(report))
    print("".join(report))
    if failures or mut_disagreements:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
