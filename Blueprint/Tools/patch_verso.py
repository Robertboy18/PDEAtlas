"""Patch the pinned Verso source (v4.36.0): give auxiliary declarations made by Lean blocks a
module-specific name.

Verso v4.36.0 puts the registered section id on the heading of a title page and of a chapter
rendered on its own page (leanprover/verso#983), so the section-anchor patch that this helper
carried for v4.35.0 is gone."""

import argparse
import hashlib
from pathlib import Path


# A Lean block elaborates its commands in a `Command.State` literal, whose `auxDeclNGen` has the
# anonymous prefix rather than the module-specific one that `Command.mkState` gives. An auxiliary
# declaration made outside of any declaration, such as the `_proof_1` and `_simp_1` of a `#cas`
# example, then gets a root name, and two chapters that both make one cannot be imported together.
# Verso fixed this after v4.36.0 (leanprover/verso#1124); this is the same change at
# 6674cf83c82a2c260bf5827d44e58f26568f7cbe, and it goes when the pin passes that fix.
INLINE_LEAN_SOURCE_SHA256 = "dd586d03e6e69d199634a3d11f8101feb2002fc69f0b2bba16bbd755963ccae4"
INLINE_LEAN_PATCHED_SHA256 = "d4647bca53b56b561190fb0e348e0a6d90882f77248d9fa506af7a5053f6cefc"
INLINE_LEAN_CHANGES = (
    (
        "    let mut cmdState : Command.State := { env := ← getEnv, maxRecDepth := ← MonadRecDepth.getMaxRecDepth, scopes := origScopes }",
        "    -- As in `Command.mkState`, auxiliary declarations made outside of a declaration get a\n"
        "    -- module-specific name.\n"
        "    let env ← getEnv\n"
        "    let auxDeclNGen := DeclNameGenerator.ofPrefix (mkPrivateName env .anonymous)\n"
        "    let mut cmdState : Command.State := { env, maxRecDepth := ← MonadRecDepth.getMaxRecDepth, scopes := origScopes, auxDeclNGen }",
    ),
)

PATCHES = (
    ("src/verso-manual/VersoManual/InlineLean.lean", INLINE_LEAN_SOURCE_SHA256,
     INLINE_LEAN_PATCHED_SHA256, INLINE_LEAN_CHANGES),
)


def patched_source(data, name, source_sha256, patched_sha256, changes):
    digest = hashlib.sha256(data).hexdigest()
    if digest == patched_sha256:
        return data, False
    if digest != source_sha256:
        raise ValueError(f"Unexpected {name}; review the pin and patch before updating.")
    text = data.decode("utf-8")
    for before, after in changes:
        if text.count(before) != 1:
            raise ValueError(f"The pinned {name} patch no longer applies uniquely.")
        text = text.replace(before, after, 1)
    patched = text.encode("utf-8")
    if hashlib.sha256(patched).hexdigest() != patched_sha256:
        raise ValueError(f"The {name} patch produced unexpected bytes.")
    return patched, True


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("verso_directory", type=Path)
    args = parser.parse_args()
    for path, source_sha256, patched_sha256, changes in PATCHES:
        source = args.verso_directory / path
        data = source.read_bytes()
        try:
            patched, changed = patched_source(data, source.name, source_sha256, patched_sha256, changes)
        except ValueError as error:
            parser.error(str(error))
        if changed:
            if source.read_bytes() != data:
                parser.error(f"{source.name} changed during patch preparation.")
            source.write_bytes(patched)
    print("Verso auxiliary-name patch verified.")


if __name__ == "__main__":
    main()
