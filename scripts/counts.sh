#!/usr/bin/env bash
# The quantities that README.md and TRUST.md state, counted on the sources of this checkout, and
# four checks of the layout of the library that must print 0. The script exits with status 1 when
# one of the four prints another number, and with status 2 when it cannot read an import.
# Run from the repository root: bash scripts/counts.sh
# The number of declarations and the axioms come from scripts/Audit.lean, which reads the
# compiled library.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."

# grep exits with 1 when no line matches. That is an empty result here, not a failure; any other
# failure of grep stops the script.
nomatch() { "$@" || [ $? -eq 1 ]; }
# the number of lines that are not empty
count() { nomatch grep -c .; }

lines=$(find PDE -name '*.lean' -print0 | xargs -0 cat | wc -l)
# lines that start a theorem or a lemma, outside comments and docstrings
theorems=$(find PDE -name '*.lean' -print0 | xargs -0 awk '
  FNR == 1 { c = 0 }
  { if (c == 0 && $0 ~ /^(private |protected |noncomputable |nonrec |@\[[^]]*\] )*(theorem|lemma)( |$)/) n++
    t = $0; while ((i = index(t, "/-")) > 0) { c++; t = substr(t, i + 2) }
    t = $0; while ((i = index(t, "-/")) > 0) { c--; t = substr(t, i + 2) }
    if (c < 0) c = 0 }
  END { print n + 0 }' | awk '{ s += $1 } END { print s + 0 }')
library=$(find PDE -name '*.lean' | nomatch grep -vc '^PDE/Examples/')
examples=0
if [ -d PDE/Examples ]; then examples=$(find PDE/Examples -name '*.lean' | wc -l); fi
references=$(nomatch grep -rl '^## References' PDE --include='*.lean' |
  nomatch grep -vc '^PDE/Examples/')
moduledocs=$(nomatch grep -rL '^/-!' PDE --include='*.lean' | wc -l)
# module docs whose first block holds headings only
titleonly=$(find PDE -name '*.lean' -print0 | xargs -0 awk '
  function close_file() { if (seen == 1 && words == 0) n++ }
  FNR == 1 { if (NR > 1) close_file(); seen = 0; indoc = 0; done = 0; words = 0 }
  done == 0 && indoc == 0 && /^\/-!/ { indoc = 1; seen = 1; sub(/^\/-!/, "") }
  indoc == 1 { l = $0; e = index(l, "-/"); if (e > 0) l = substr(l, 1, e - 1)
    if (l !~ /^[ \t]*#/) words += split(l, parts, " ")
    if (e > 0) { indoc = 0; done = 1 } }
  END { close_file(); print n + 0 }' | awk '{ s += $1 } END { print s + 0 }')
# The imports of the files it is given: one line for each import, with the file, the word
# `public` or `plain`, and the module. It reads the head of a file word by word. Comments are
# skipped: line comments and block comments, nested ones too. The head ends at the first word
# that is not `module`, `prelude`, a modifier of an import (`public`, `private`, `meta`),
# `import`, `all` or the module name after them, and at a docstring or a module doc. So an
# import may be laid out over several lines, several may share a line, and prose that begins
# with the word import is not read. This is not a check of Lean syntax. A module name must be
# a dotted name whose parts start with an ASCII letter or `_` and contain only ASCII letters,
# digits and `_`. Any other name, for example a name between « and » or a name with a command
# right after it, gives a line with the word `unread`, and the script stops on it.
imports='
  { sub(/\r$/, "") }
  FNR == 1 { past = 0; incom = 0; st = 0; pub = 0 }
  past { next }
  { s = $0; n = length(s); i = 1; text = ""
    while (i <= n) {
      two = substr(s, i, 2)
      if (incom > 0) {
        if (two == "/-") { incom++; i += 2 } else if (two == "-/") { incom--; i += 2 } else i++
        continue }
      if (two == "--") break
      if (two == "/-") {
        c = substr(s, i + 2, 1)
        if (c == "-" || c == "!") { text = text " /--"; break }
        incom = 1; i += 2; text = text " "; continue }
      text = text substr(s, i, 1); i++ }
    nt = split(text, tok, /[ \t]+/)
    for (k = 1; k <= nt; k++) {
      t = tok[k]
      if (t == "") continue
      if (st >= 2) {
        if (st == 2 && t == "all") { st = 3; continue }
        if (t ~ /^[A-Za-z_][A-Za-z0-9_]*([.][A-Za-z_][A-Za-z0-9_]*)*$/)
          print FILENAME "\t" (pub ? "public" : "plain") "\t" t
        else { print FILENAME "\tunread\t" t; past = 1 }
        st = 0; pub = 0
        if (past) break
        continue }
      if (t == "import") { st = 2; continue }
      if (t == "public" || t == "private" || t == "meta") { if (t == "public") pub = 1; st = 1; continue }
      if (st == 0 && (t == "module" || t == "prelude")) continue
      past = 1; break } }'
table=$({ awk "$imports" PDE.lean; find PDE -name '*.lean' -print0 | xargs -0 awk "$imports"; })
unread=$(printf '%s\n' "$table" | awk -F'\t' '$2 == "unread" { print "  " $1 ": " $3 }')
if [ -n "$unread" ]; then
  printf 'scripts/counts.sh: cannot read the module name of an import in\n%s\n' "$unread" >&2
  exit 2
fi
# the modules of NOTICE are those that turn off the header linter
notice_files=$(nomatch grep -rl '^set_option linter.style.header false' PDE --include='*.lean' |
  sort)
notice=$(printf '%s\n' "$notice_files" | count)
notice_modules=$(printf '%s\n' "$notice_files" | sed 's/\.lean$//; s#/#.#g')
importers=$(printf '%s\n' "$table" |
  awk -F'\t' 'NR == FNR { if ($0 != "") notice[$0] = 1; next }
    $1 != "PDE.lean" && ($3 in notice) { print $1 }' <(printf '%s\n' "$notice_modules") - |
  sort -u | comm -23 - <(printf '%s\n' "$notice_files") | count)
# library modules that neither PDE.lean nor another library module imports with `public import`:
# a file that imports `PDE` in the module system sees a module only through public imports
modules=$(find PDE -name '*.lean' ! -path 'PDE/Examples/*' | sed 's/\.lean$//; s#/#.#g' | sort)
imported=$(printf '%s\n' "$table" |
  awk -F'\t' '$1 !~ /^PDE\/Examples\// && $2 == "public" && $3 ~ /^PDE([.]|$)/ { print $3 }' |
  sort -u)
unreached=$(comm -23 <(printf '%s\n' "$modules") <(printf '%s\n' "$imported") | count)

printf 'lines of Lean under PDE/: %s\n' "$lines"
printf 'theorems and lemmas written in the sources (lines that start one): %s\n' "$theorems"
printf 'library modules (files under PDE/ outside PDE/Examples, and PDE.lean): %s\n' "$((library + 1))"
printf 'example modules (files under PDE/Examples): %s\n' "$examples"
printf 'library modules with a References section: %s\n' "$references"
printf 'modules that turn off the header linter (the modules of NOTICE): %s\n' "$notice"
printf 'modules under PDE/ without a module doc (must be 0): %s\n' "$moduledocs"
printf 'modules under PDE/ whose module doc is a title only (must be 0): %s\n' "$titleonly"
printf 'modules outside NOTICE that import a module of NOTICE, PDE.lean apart (must be 0): %s\n' "$importers"
printf 'library modules without a public import in PDE.lean or the library (must be 0): %s\n' "$unreached"
[ "$moduledocs" -eq 0 ] && [ "$titleonly" -eq 0 ] && [ "$importers" -eq 0 ] && [ "$unreached" -eq 0 ]
