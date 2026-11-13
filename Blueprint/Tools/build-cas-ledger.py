#!/usr/bin/env python3
"""Generate the Blueprint computation ledger.

Every `cas`, `cega` and `#cas` call site under `PDE/` is recorded with its
library, module, line, enclosing declaration, tactic form and the statement that
the declaration proves. The result is written as a JSON string literal in
`Blueprint/Generated/CasLedgerData.lean`, which the Blueprint package decodes at
elaboration time. `Blueprint/Tools/build.sh` runs this script before
`lake build Blueprint`; `--check` reports whether the committed copy is stale
without rewriting it, and `--json PATH` also writes the JSON on its own.

The scan works on the source text with comments, string and character literals
and syntax quotations blanked out, so docstring examples and the tactic
implementation's own `` `(tactic| cas ...) `` patterns are not counted. A
tactic keyword only counts when it is followed by a tactic-shaped continuation
(end of line, `[`, a configuration group, `using`, `at`, `;`, `<;>`, a closing
bracket), so that ordinary functions named `cas` are skipped. Configuration
groups between the keyword and the mode bracket, such as
`cega (prec := 40) [enclose ...]` or `#cas (depth := 3) [...]`, are part of the
recorded form and appear in the tactic label as `(prec)` or `(depth)`.

The script replaces an earlier JavaScript generator and writes the same ledger.
JavaScript strings are sequences of UTF-16 code units, and that generator's
columns, slices and the 160-unit argument limit count those units. This script
keeps that arithmetic by working on strings whose characters outside the Basic
Multilingual Plane are split into surrogate pairs (`to_units`), and runs the
three Unicode-aware patterns (`IDENT_CHAR`, `TACTIC`, `NAME`) on the recombined
text. `\\s`, `\\b` and `.` are spelled out with JavaScript's meaning (`WS`, `B`,
`DOT`). The patterns need the `regex` package (`pip install regex`).
"""

from __future__ import annotations

import json
import os
import sys
from dataclasses import dataclass

import regex

# JavaScript's `\s`, `\b` (ASCII word characters) and `.` (no line terminators).
WS_CHARS = ("\t\n\v\f\r \u00a0\u1680\u2000\u2001\u2002\u2003\u2004\u2005\u2006"
            "\u2007\u2008\u2009\u200a\u2028\u2029\u202f\u205f\u3000\ufeff")
WS = "[\\t\\n\\v\\f\\r \\u00a0\\u1680\\u2000-\\u200a\\u2028\\u2029\\u202f\\u205f\\u3000\\ufeff]"
NWS = WS.replace("[", "[^", 1)
B = "(?:(?<=[A-Za-z0-9_])(?![A-Za-z0-9_])|(?<![A-Za-z0-9_])(?=[A-Za-z0-9_]))"
DOT = "[^\\n\\r\\u2028\\u2029]"

TACTIC_KEYWORDS = ["cas_nf", "cas?", "cas", "cega?", "cega"]
MODE_KEYWORDS = {"integrate", "ibp", "fast", "batch", "enclose"}
DECL_KEYWORDS = [
    "theorem", "lemma", "def", "example", "instance", "abbrev", "opaque", "axiom",
    "structure", "inductive", "class", "macro", "elab", "syntax", "macro_rules",
    "elab_rules", "notation", "infix", "infixl", "infixr", "prefix", "postfix",
]
MODIFIERS = [
    "public", "private", "protected", "meta", "noncomputable", "scoped", "local",
    "unsafe", "partial", "nonrec", "irreducible",
]

OPENERS = {"(": ")", "[": "]", "{": "}", "⦃": "⦄", "⟨": "⟩"}
CLOSERS = set(OPENERS.values())

IDENT_CHAR = regex.compile(r"[\p{L}\p{N}_'!?.«»]")
NAME = regex.compile(r"^[\p{L}_«][\p{L}\p{N}_'.«»!?]*\Z")
TACTIC = regex.compile(
    "(^|[^\\p{L}\\p{N}_.'`#])(" + "|".join(k.replace("?", "\\?") for k in TACTIC_KEYWORDS)
    + ")(?![\\p{L}\\p{N}_?])")
HEADER = regex.compile(
    f"^([ \\t]*)((?:@\\[[^\\]]*\\]{WS}*)*)((?:(?:{'|'.join(MODIFIERS)}){WS}+)*)"
    f"({'|'.join(DECL_KEYWORDS)}){B}({DOT}*)\\Z")
CHAR_LITERAL = regex.compile(f"^'(?:\\\\{DOT}|[^'\\\\\\n])'")
CONFIG_GROUP = regex.compile(f"^{WS}*\\({WS}*([A-Za-z_][A-Za-z0-9_]*){WS}*:={WS}*[^()]*\\)")
CONTINUATION = regex.compile(
    f"^{WS}*(?:\\Z|\\[|\\({WS}*[A-Za-z_][A-Za-z0-9_]*{WS}*:=|;|<;>|\\)|\\]|⟩|,|\\||"
    f"{B}using{B}|{B}at{B})")
NAMESPACE = regex.compile(f"^namespace{WS}+({NWS}+)")
SECTION = regex.compile(
    f"^(?:@\\[[^\\]]*\\]{WS}*)?(?:public{WS}+)?(?:noncomputable{WS}+)?(?:meta{WS}+)?"
    f"section(?:{WS}+({NWS}+))?{WS}*\\Z")
END = regex.compile(f"^end(?:{WS}+({NWS}+))?{WS}*\\Z")
END_LINE = regex.compile(f"^end(?:{WS}|\\Z)")
DECL_NAME = regex.compile(f"^{WS}*(?:\\(priority[^)]*\\){WS}*)?([^\\t\\n\\v\\f\\r \\u00a0\\u1680"
                          "\\u2000-\\u200a\\u2028\\u2029\\u202f\\u205f\\u3000\\ufeff:(\\[{⦃⟨]+)")
COMMAND = regex.compile(f"^{WS}*#cas{B}")
COMMAND_HEADER = regex.compile(
    f"^#cas((?:{WS}*\\({WS}*[A-Za-z_][A-Za-z0-9_]*{WS}*:={WS}*[^()]*\\))*){WS}*\\[{WS}*([A-Za-z_]+)")
COMMAND_OPTION = regex.compile(f"\\({WS}*([A-Za-z_][A-Za-z0-9_]*){WS}*:=")
WS_RUN = regex.compile(f"{WS}+")
LEADING_WS = regex.compile(f"^{WS}*")
BAR_LINE = regex.compile(f"^{WS}*\\|")
WHERE = regex.compile(f"{B}where{B}")
ONE_WS = regex.compile(WS)
PRIVATE = regex.compile(f"{B}private{B}")
ATTRS = regex.compile(f"^(?:@\\[[^\\]]*\\]{WS}*)*")
MODS = regex.compile(f"^(?:(?:{'|'.join(MODIFIERS)}){WS}+)*")
PRIORITY = regex.compile(f"^\\(priority[^)]*\\){WS}*")
BRACKET = regex.compile(f"^{WS}*\\[")
FIRST_WORD = regex.compile("^([A-Za-z_]+)")
USING_WORD = regex.compile(f"{B}using{B}")
USING_TAIL = regex.compile(f"^{WS}*(using|at){B}({DOT}*)\\Z")
STOP = regex.compile("<;>|(?<![;<]);(?![>;])")


def to_units(text: str) -> str:
    """Split every character outside the BMP into its UTF-16 surrogate pair."""
    if all(ord(ch) < 0x10000 for ch in text):
        return text
    out = []
    for ch in text:
        code = ord(ch)
        if code < 0x10000:
            out.append(ch)
        else:
            code -= 0x10000
            out.append(chr(0xD800 + (code >> 10)))
            out.append(chr(0xDC00 + (code & 0x3FF)))
    return "".join(out)


def from_units(text: str) -> str:
    """Recombine surrogate pairs; a lone surrogate stays as it is."""
    if all(ord(ch) < 0xD800 or ord(ch) > 0xDFFF for ch in text):
        return text
    return text.encode("utf-16-le", "surrogatepass").decode("utf-16-le", "surrogatepass")


def utf16_key(text: str) -> bytes:
    """Sort key of JavaScript's default string order (UTF-16 code units)."""
    return text.encode("utf-16-be", "surrogatepass")


def js_trim(text: str) -> str:
    return text.strip(WS_CHARS)


def collapse(text: str) -> str:
    return js_trim(WS_RUN.sub(" ", text))


def is_ident_char(ch: str) -> bool:
    return IDENT_CHAR.match(ch) is not None


def blank_non_code(source: str) -> str:
    """Replace comments, string and character literals and syntax quotations by
    spaces, keeping every newline so line numbers survive."""
    out: list[str] = []
    state = "code"
    depth = 0
    quote_depth = 0
    i = 0
    n = len(source)

    def emit(ch: str) -> None:
        out.append("\n" if ch == "\n" else " ")

    while i < n:
        ch = source[i]
        pair = source[i:i + 2]
        if state == "line":
            emit(ch)
            if ch == "\n":
                state = "code"
            i += 1
            continue
        if state == "block":
            if pair == "/-":
                depth += 1
                emit(" ")
                emit(" ")
                i += 2
            elif pair == "-/":
                depth -= 1
                emit(" ")
                emit(" ")
                i += 2
                if depth == 0:
                    state = "code"
            else:
                emit(ch)
                i += 1
            continue
        if state == "string":
            emit(ch)
            if ch == "\\" and i + 1 < n:
                emit(source[i + 1])
                i += 2
                continue
            if ch == "\"":
                state = "code"
            i += 1
            continue
        if pair == "--":
            state = "line"
            emit(" ")
            emit(" ")
            i += 2
            continue
        if pair == "/-":
            state = "block"
            depth = 1
            emit(" ")
            emit(" ")
            i += 2
            continue
        if ch == "\"":
            state = "string"
            emit(" ")
            i += 1
            continue
        if ch == "'" and (i == 0 or not is_ident_char(source[i - 1])):
            literal = CHAR_LITERAL.match(source[i:i + 6])
            if literal:
                for c in literal.group(0):
                    emit(c)
                i += len(literal.group(0))
                continue
        if ch == "`" and source[i + 1:i + 2] == "(":
            quote_depth += 1
            emit(" ")
            emit(" ")
            i += 2
            continue
        if quote_depth > 0:
            if ch == "(":
                quote_depth += 1
            if ch == ")":
                quote_depth -= 1
            emit(ch)
            i += 1
            continue
        out.append(ch)
        i += 1
    return "".join(out)


def keyword_at(line: str, column: int, keyword: str) -> bool:
    end = column + len(keyword)
    return (line.startswith(keyword, column)
            and (column == 0 or not is_ident_char(line[column - 1]))
            and (end == len(line) or not is_ident_char(line[end])))


def starts_equation_alternative(lines: list[str], start: int) -> bool:
    """A leading `|` can also open an absolute value in the stated type. An
    equation alternative has a top-level `=>` before the declaration's `:=`;
    arrows inside bracket groups or a following `fun`/`match` expression do not
    start its body."""
    depth = 0
    for index in range(start, len(lines)):
        line = lines[index]
        if index > start and HEADER.match(line):
            return False
        for j, ch in enumerate(line):
            if ch in OPENERS:
                depth += 1
            elif ch in CLOSERS:
                depth = max(0, depth - 1)
            elif depth == 0:
                if line.startswith(":=", j):
                    return False
                if line.startswith("=>", j):
                    return True
                if any(keyword_at(line, j, word) for word in ("fun", "match", "let", "have", "where")):
                    return False
    return False


def declaration_text(lines: list[str], start: int) -> tuple[str, bool]:
    """The header through the declaration delimiter, not through a fixed number
    of lines. Local assignments in a `let` type are part of the statement."""
    depth = 0
    pending_lets = 0
    preserve_layout = False
    collected: list[str] = []
    for index in range(start, len(lines)):
        line = lines[index]
        if index > start and (HEADER.match(line) or END_LINE.match(line)):
            break
        cut = -1
        for j, ch in enumerate(line):
            if ch in OPENERS:
                depth += 1
            elif ch in CLOSERS:
                depth = max(0, depth - 1)
            elif depth == 0:
                if keyword_at(line, j, "let"):
                    pending_lets += 1
                    preserve_layout = True
                if ch == ":" and line[j + 1:j + 2] == "=":
                    if pending_lets > 0:
                        pending_lets -= 1
                    else:
                        cut = j
                        break
                if (ch == "|" and BAR_LINE.match(line) and index > start
                        and starts_equation_alternative(lines, index)):
                    cut = 0
                    break
                if WHERE.search(line[j:j + 5]) and (j == 0 or ONE_WS.match(line[j - 1])):
                    cut = j
                    break
        if cut >= 0:
            collected.append(line[:cut])
            break
        collected.append(line)
    return js_trim("\n".join(collected)), preserve_layout


def split_type(header_text: str, keyword: str, name: str | None,
               preserve_layout: bool) -> tuple[str, str]:
    """Skip attributes, modifiers, the keyword and the name, then find the first
    colon at bracket depth zero: what follows is the stated type."""
    text = ATTRS.sub("", header_text, count=1)
    text = MODS.sub("", text, count=1)
    text = regex.sub(f"^{keyword}{B}{WS}*", "", text, count=1)
    if name:
        text = PRIORITY.sub("", text, count=1)[len(name):].lstrip(WS_CHARS)
    depth = 0
    for j, ch in enumerate(text):
        if ch in OPENERS:
            depth += 1
        elif ch in CLOSERS:
            depth = max(0, depth - 1)
        elif depth == 0 and ch == ":" and text[j + 1:j + 2] != "=":
            stated = text[j + 1:]
            # A newline separates a layout-style let RHS from its body.
            return collapse(text[:j]), js_trim(stated) if preserve_layout else collapse(stated)
    return collapse(text), ""


@dataclass
class Declaration:
    line: int
    kind: str
    name: str | None
    full_name: str | None
    is_private: bool
    binders: str
    type: str


def scan_declarations(lines: list[str]) -> list[Declaration]:
    declarations: list[Declaration] = []
    scope: list[tuple[str, str]] = []
    for index, line in enumerate(lines):
        m = NAMESPACE.match(line)
        if m:
            scope.append(("namespace", m.group(1)))
            continue
        m = SECTION.match(line)
        if m:
            scope.append(("section", m.group(1) or ""))
            continue
        m = END.match(line)
        if m:
            if scope:
                scope.pop()
            continue
        header = HEADER.match(line)
        if not header:
            continue
        keyword = header.group(4)
        rest = header.group(5)
        name = None
        name_match = DECL_NAME.match(rest)
        if name_match and keyword not in ("example", "macro_rules", "elab_rules"):
            name = name_match.group(1)
        namespaces = [entry for kind, entry in scope if kind == "namespace"]
        full_name = None
        if name and NAME.match(from_units(name)):
            stripped = name[len("_root_."):] if name.startswith("_root_.") else name
            full_name = (stripped if name.startswith("_root_.") or not namespaces
                         else ".".join(namespaces) + "." + stripped)
        text, preserve_layout = declaration_text(lines, index)
        binders, stated = split_type(text, keyword, name, preserve_layout)
        declarations.append(Declaration(
            line=index + 1, kind=keyword, name=name, full_name=full_name,
            is_private=PRIVATE.search(header.group(3)) is not None,
            binders=binders, type=stated))
    return declarations


def read_bracket_group(lines: list[str], line_index: int, column: int):
    """A balanced bracket group starting at `lines[line_index][column]`."""
    depth = 0
    parts: list[str] = []
    for index in range(line_index, min(len(lines), line_index + 12)):
        line = lines[index]
        start = column if index == line_index else 0
        for j in range(start, len(line)):
            ch = line[j]
            if ch == "[":
                depth += 1
            if ch == "]":
                depth -= 1
                if depth == 0:
                    parts.append(line[start:j + 1])
                    return " ".join(parts), index, j + 1
        parts.append(line[start:])
    return None


def command_statement(text: str) -> str:
    """The `#cas` statement: the text after the command keyword, its
    configuration groups and its balanced mode bracket."""
    cursor = len("#cas")
    while True:
        config = CONFIG_GROUP.match(text[cursor:])
        if config is None:
            break
        cursor += len(config.group(0))
    opening = text.find("[", cursor)
    if opening < 0 or js_trim(text[cursor:opening]) != "":
        return js_trim(text[cursor:])
    depth = 0
    for j in range(opening, len(text)):
        if text[j] == "[":
            depth += 1
        if text[j] == "]":
            depth -= 1
            if depth == 0:
                return js_trim(text[j + 1:])
    return js_trim(text[cursor:])


def tactic_label(keyword: str, options: list[str], mode: str) -> str:
    """The label used by the summary counts: the keyword, the names of any
    configuration options, and the mode, for example `cega (prec) [enclose]`."""
    label = keyword
    if options:
        label += f" ({', '.join(options)})"
    if mode:
        label += f" [{mode}]"
    return label


def read_tactic_argument(lines: list[str], line_index: int, first_part: str) -> str:
    """The rest of the line up to a tactic separator, with unbalanced
    parentheses closed on the following lines (bounded), and trailing
    parentheses that close an enclosing group removed."""
    text = first_part
    depth = 0

    def balance(chunk: str) -> None:
        nonlocal depth
        for ch in chunk:
            if ch in "([⟨":
                depth += 1
            if ch in ")]⟩":
                depth -= 1

    balance(text)
    following = line_index + 1
    while depth > 0 and following < min(len(lines), line_index + 12):
        text += " " + js_trim(lines[following])
        balance(lines[following])
        following += 1
    stop = STOP.search(text)
    if stop:
        text = text[:stop.start()]
    opened = 0
    cut = len(text)
    for j, ch in enumerate(text):
        if ch in "([⟨":
            opened += 1
        if ch in ")]⟩":
            if opened == 0:
                cut = j
                break
            opened -= 1
    text = collapse(text[:cut])
    return text[:157] + "..." if len(text) > 160 else text


def tactic_form_at(lines: list[str], line_index: int, column: int, keyword: str):
    line = lines[line_index]
    cursor = column + len(keyword)
    form = keyword
    mode = ""
    uses_using = False
    options: list[str] = []
    while True:
        config = CONFIG_GROUP.match(line[cursor:])
        if config is None:
            break
        options.append(config.group(1))
        form += " " + collapse(config.group(0))
        cursor += len(config.group(0))
    bracket = BRACKET.match(line[cursor:])
    if bracket:
        group = read_bracket_group(lines, line_index, cursor + len(bracket.group(0)) - 1)
        if group is None:
            return None
        group_text, end_line, end_column = group
        inner = js_trim(group_text[1:-1])
        first_word = FIRST_WORD.match(inner)
        mode = first_word.group(1) if first_word and first_word.group(1) in MODE_KEYWORDS \
            else "lemmas"
        uses_using = USING_WORD.search(inner) is not None
        form += " " + collapse(group_text)
        if end_line != line_index:
            return form, mode, uses_using, options
        cursor = end_column
    tail = USING_TAIL.match(line[cursor:])
    if tail:
        uses_using = uses_using or tail.group(1) == "using"
        form += " " + tail.group(1) + " " + read_tactic_argument(lines, line_index, tail.group(2))
    return collapse(form), mode, uses_using, options


@dataclass
class SourceRoot:
    """A directory to scan, the library label recorded on its rows, and the
    prefix removed from the path when forming module names."""
    dir: str
    library: str
    module_prefix: str = ""


SOURCE_ROOTS = [SourceRoot("PDE", "PDE")]
EXAMPLE_PREFIXES = ("PDE/Examples/",)
GENERATOR = "Blueprint/Tools/build-cas-ledger.py"


def walk(root: str) -> list[str]:
    files: list[str] = []
    pending = [root]
    while pending:
        current = pending.pop()
        with os.scandir(current) as entries:
            for entry in entries:
                if entry.name.startswith("."):
                    continue
                target = os.path.join(current, entry.name)
                if entry.is_dir(follow_symlinks=False):
                    pending.append(target)
                elif entry.is_file(follow_symlinks=False) and entry.name.endswith(".lean"):
                    files.append(target)
    return sorted(files, key=utf16_key)


def scan_file(relative_path: str, source: str, root: SourceRoot) -> list[dict]:
    code = blank_non_code(source)
    lines = code.split("\n")
    declarations = scan_declarations(lines)
    rows: list[dict] = []
    scope = "examples" if relative_path.startswith(EXAMPLE_PREFIXES) else "production"
    module = relative_path[len(root.module_prefix):]
    if module.endswith(".lean"):
        module = module[:-len(".lean")]
    module = ".".join(module.split("/"))
    library = root.library

    def enclosing(line_index: int) -> Declaration | None:
        found = None
        for decl in declarations:
            if decl.line - 1 <= line_index:
                found = decl
            else:
                break
        return found

    for index, line in enumerate(lines):
        if COMMAND.match(line):
            parts = [js_trim(line)]
            indent = len(LEADING_WS.match(line).group(0))
            for following in range(index + 1, len(lines)):
                candidate = lines[following]
                if js_trim(candidate) == "" or len(LEADING_WS.match(candidate).group(0)) <= indent:
                    break
                parts.append(js_trim(candidate))
            text = collapse(" ".join(parts))
            header = COMMAND_HEADER.match(text)
            options = [found.group(1) for found in COMMAND_OPTION.finditer(header.group(1))] \
                if header else []
            mode = header.group(2) if header else ""
            rows.append({
                "scope": scope,
                "library": library,
                "module": module,
                "path": relative_path,
                "line": index + 1,
                "tactic": tactic_label("#cas", options, mode),
                "form": text,
                "statement": command_statement(text),
                "decl": None,
            })
            continue
        joined = from_units(line)
        for match in TACTIC.finditer(joined):
            keyword = match.group(2)
            column = len(to_units(joined[:match.start()])) + len(to_units(match.group(1)))
            after = line[column + len(keyword):]
            if not CONTINUATION.match(after):
                continue
            form = tactic_form_at(lines, index, column, keyword)
            if form is None:
                continue
            form_text, mode, uses_using, options = form
            decl = enclosing(index)
            tactic = tactic_label(keyword, options, mode)
            rows.append({
                "scope": scope,
                "library": library,
                "module": module,
                "path": relative_path,
                "line": index + 1,
                "tactic": f"{tactic} using" if uses_using else tactic,
                "form": form_text,
                "statement": decl.type if decl else "",
                "decl": {
                    "kind": decl.kind,
                    "name": decl.name,
                    "fullName": None if decl.is_private else decl.full_name,
                    "line": decl.line,
                    "binders": decl.binders,
                } if decl else None,
            })
    return rows


def restore(value):
    """Recombine surrogate pairs in every string of a row."""
    if isinstance(value, str):
        return from_units(value)
    if isinstance(value, dict):
        return {key: restore(item) for key, item in value.items()}
    if isinstance(value, list):
        return [restore(item) for item in value]
    return value


def build_ledger(repo_root: str) -> dict:
    rows: list[dict] = []
    for root in SOURCE_ROOTS:
        directory = os.path.join(repo_root, root.dir)
        if not os.path.isdir(directory):
            continue
        for file in walk(directory):
            relative_path = "/".join(os.path.relpath(file, repo_root).split(os.sep))
            with open(file, "rb") as handle:
                source = handle.read().decode("utf-8", errors="replace")
            rows.extend(scan_file(relative_path, to_units(source), root))
    rows = [restore(row) for row in rows]
    rows.sort(key=lambda row: (row["scope"] != "production", utf16_key(row["path"]), row["line"]))

    def summarize(scope: str) -> dict:
        scoped = [row for row in rows if row["scope"] == scope]
        tactics: dict[str, int] = {}
        for row in scoped:
            tactics[row["tactic"]] = tactics.get(row["tactic"], 0) + 1
        libraries: dict[str, dict] = {}
        for root in SOURCE_ROOTS:
            in_library = [row for row in scoped if row["library"] == root.library]
            if not in_library:
                continue
            libraries[root.library] = {
                "rows": len(in_library),
                "modules": len({row["module"] for row in in_library}),
            }
        return {
            "rows": len(scoped),
            "modules": len({row["module"] for row in scoped}),
            "libraries": libraries,
            "tactics": tactics,
        }

    return {
        "schemaVersion": 1,
        "generator": GENERATOR,
        "sourceRoots": [root.dir for root in SOURCE_ROOTS],
        "summary": {
            "production": summarize("production"),
            "examples": summarize("examples"),
        },
        "rows": rows,
    }


def to_json(ledger: dict) -> str:
    """`JSON.stringify(ledger, null, 2)`: a lone surrogate is escaped."""
    text = json.dumps(ledger, indent=2, ensure_ascii=False)
    return regex.sub("[\\ud800-\\udfff]", lambda m: f"\\u{ord(m.group(0)):04x}", text)


DELIMITER = "####"


def lean_source(ledger: dict, text: str) -> str:
    production = ledger["summary"]["production"]
    examples = ledger["summary"]["examples"]
    libraries = "; ".join(f"{name}: {entry['rows']} sites in {entry['modules']} modules"
                          for name, entry in production["libraries"].items())
    return f"""/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

/-!
# Computation ledger data

Generated by `Blueprint/Tools/build-cas-ledger.py` from every `cas`, `cega` and
`#cas` call site under `PDE/`.
Do not edit by hand: `Blueprint/Tools/build.sh`
regenerates this file before it builds the Blueprint package, and
`Blueprint.Commands.ComputationLedger` decodes the JSON below for the textbook
coverage map, the card index and the call-site counts quoted in the computation
chapter.

Production rows: {production['rows']} call sites in
{production['modules']} modules ({libraries}). Example rows:
{examples['rows']} call sites in {examples['modules']} modules.
-/

namespace LeanPDE.CasLedger

/-- Serialized ledger rows; see `Blueprint.Commands.ComputationLedger` for the schema. -/
def json : String := r{DELIMITER}"
{text}
"{DELIMITER}

end LeanPDE.CasLedger
"""


def main(argv: list[str]) -> int:
    script_dir = os.path.dirname(os.path.abspath(__file__))
    repo_root = os.path.dirname(os.path.dirname(script_dir))
    output_path = os.path.join(repo_root, "Blueprint", "Generated", "CasLedgerData.lean")
    check_only = "--check" in argv
    json_path = argv[argv.index("--json") + 1] if "--json" in argv else None

    ledger = build_ledger(repo_root)
    text = to_json(ledger)
    if f'"{DELIMITER}' in text:
        raise SystemExit("Ledger JSON contains the raw string terminator sequence.")
    source = lean_source(ledger, text)
    relative_output = os.path.relpath(output_path, repo_root)

    if json_path:
        os.makedirs(os.path.dirname(os.path.abspath(json_path)), exist_ok=True)
        with open(json_path, "w", encoding="utf-8", newline="") as handle:
            handle.write(text + "\n")

    existing = None
    if os.path.exists(output_path):
        with open(output_path, "rb") as handle:
            existing = handle.read().decode("utf-8")
    production = ledger["summary"]["production"]
    examples = ledger["summary"]["examples"]
    if check_only:
        if existing != source:
            print("Computation ledger is stale: run python3 Blueprint/Tools/build-cas-ledger.py "
                  f"to regenerate {relative_output}.", file=sys.stderr)
            return 1
        print(f"Computation ledger is current: {production['rows']} production and "
              f"{examples['rows']} example call sites.")
        return 0
    os.makedirs(os.path.dirname(output_path), exist_ok=True)
    if existing != source:
        with open(output_path, "w", encoding="utf-8", newline="") as handle:
            handle.write(source)
    print(f"Computation ledger: {production['rows']} production call sites in "
          f"{production['modules']} modules and {examples['rows']} example call sites in "
          f"{examples['modules']} modules written to {relative_output}.")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
