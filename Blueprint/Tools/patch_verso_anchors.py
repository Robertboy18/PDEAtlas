"""Patch the pinned Verso source on Lean 4.35: preserve the previous Verso pin's split-page
section anchors, and give auxiliary declarations made by Lean blocks a module-specific name."""

import argparse
import hashlib
from pathlib import Path


# Port the three production changes from Verso commit 52c8c9557bcb5cc8c0edc0ee37e74311a3d53ee9
# to the v4.35.0 source at 304b8561790c50222551c937ce02928df0d5b445.
SOURCE_SHA256 = "dddfd19180d18ffdcbfe390eee12e7b4b0b37578736bc1ec675d1a39331d452c"
PATCHED_SHA256 = "042e5935f97f8e7d7280eb7f1132476ace96759566a79cf8865c173a507b5e9a"
CHANGES = (
    (
        "    let introHtml ← Html.seq <$> part.content.mapM",
        "    let idAttrs := part.metadata.bind (·.id) |>.map state.htmlId |>.getD #[]\n"
        "    let introHtml ← Html.seq <$> part.content.mapM",
    ),
    (
        "{{<section>{{Html.titlePage titleHtml authors authorshipNote introHtml ++ contents}}",
        "{{<section {{idAttrs}}>{{Html.titlePage titleHtml authors authorshipNote introHtml ++ contents}}",
    ),
    (
        "{{<section><h1>{{titleHtml}}</h1> {{introHtml}} {{contents}} {{subTocHtml}}</section>}}",
        "{{<section {{idAttrs}}><h1>{{titleHtml}}</h1> {{introHtml}} {{contents}} {{subTocHtml}}</section>}}",
    ),
)

# A Lean block elaborates its commands in a `Command.State` literal, whose `auxDeclNGen` has the
# anonymous prefix rather than the module-specific one that `Command.mkState` gives. An auxiliary
# declaration made outside of any declaration, such as the `_proof_1` and `_simp_1` of a `#cas`
# example, then gets a root name, and two chapters that both make one cannot be imported together.
INLINE_LEAN_SOURCE_SHA256 = "04392d3c7d573dc130cad985076ee639b8367f922bc86bce459b0564a5613213"
INLINE_LEAN_PATCHED_SHA256 = "19a2b54d6ea59e9c8569a34c0f61e18398dd98d156747f8024bd8751b643d68d"
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
    ("src/verso-manual/VersoManual.lean", SOURCE_SHA256, PATCHED_SHA256, CHANGES),
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
    print("Verso section-anchor and auxiliary-name patches verified.")


if __name__ == "__main__":
    main()
