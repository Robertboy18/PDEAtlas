#!/usr/bin/env bash

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
tools_root="$repo_root/Blueprint/Tools"
output_root="$repo_root/_out"
certificates="${LEANPDE_CERTIFICATES:-kernel}"
case "$certificates" in
  kernel) cache_dir=".lake/build"; default_site="$output_root/site" ;;
  fast|native) certificates=fast; cache_dir=".lake/build-fast"; default_site="$output_root/site-fast" ;;
  *) printf 'Certificate profile must be kernel or fast.\n' >&2; exit 2 ;;
esac
export LEANPDE_CERTIFICATES="$certificates"
lake_profile_args=("-Kcertificates=$certificates")
lean_profile_args=()
if [[ "$certificates" == kernel ]]; then
  lean_profile_args+=("-Dweak.cega.nativeCertificates=false")
fi
requested_output="${1:-$default_site}"

for command in realpath lake python3; do
  if ! command -v "$command" >/dev/null 2>&1; then
    printf 'Blueprint build requires %s.\n' "$command" >&2
    exit 127
  fi
done

if [[ -L "$output_root" ]]; then
  printf 'Blueprint output root must not be a symbolic link: %s\n' "$output_root" >&2
  exit 1
fi

mkdir -p "$output_root"
output_root="$(realpath -e -- "$output_root")"

if [[ "$requested_output" != /* ]]; then
  requested_output="$repo_root/$requested_output"
fi
output_dir="$(realpath -m -- "$requested_output")"

case "$output_dir" in
  "$output_root"/*) ;;
  *)
    printf 'Blueprint output must be a strict subdirectory of %s.\n' "$output_root" >&2
    printf 'Resolved output: %s\n' "$output_dir" >&2
    exit 1
    ;;
esac

site_dir="$output_dir/html-multi"

if ! command -v node >/dev/null 2>&1; then
  printf 'Blueprint rendering requires Node.js.\n' >&2
  exit 1
fi

if ! command -v dot >/dev/null 2>&1; then
  printf 'Blueprint rendering requires Graphviz dot to pre-render the dependency atlas.\n' >&2
  exit 1
fi

cd "$repo_root/Blueprint"

# Statement cards use the compiled public library.
# Lake caches configuration values, including the selected certificate profile.
# Reconfigure once in each package before using its artifacts.
(cd "$repo_root" && lake -R "${lake_profile_args[@]}" build PDE)

# Lake runs the post_update hooks (Mathlib's cache download and the Verso
# anchor patch of this package's lakefile) only on `lake update`, not when a
# fresh clone materializes the Blueprint's own dependencies, so run both here.
lake -R "${lake_profile_args[@]}" env true
lake "${lake_profile_args[@]}" exe cache get
python3 "$tools_root/patch_verso_anchors.py" "$repo_root/Blueprint/.lake/packages/verso"

# The computation ledger is generated from the `PDE` sources on every build, so
# the Blueprint never carries a hand-maintained list of `cas`/`cega` call sites.
python3 "$tools_root/build-cas-ledger.py"

# The textbook coverage map is generated from the chapter sources on every
# build, so the map of Evans's table of contents never goes stale.
node "$tools_root/build-textbook-map.mjs"

# Declaration snapshots resolve source files while the chapters compile.
package_source_path="$(lake -R "${lake_profile_args[@]}" env printenv LEAN_SRC_PATH)"
LEAN_SRC_PATH="$package_source_path" \
  lake "${lake_profile_args[@]}" build VersoBlueprint:shared Blueprint

mkdir -p "$output_dir"
find "$output_dir" -mindepth 1 -depth -delete

# `Blueprint.lean` deliberately stays at the repository root while its Lake
# package is nested.  Put the nested package's own artifacts first so a stale
# root build artifact cannot shadow the current Blueprint module.
lean_bin="$(lake "${lake_profile_args[@]}" env which lean)"
package_lean_path="$(lake "${lake_profile_args[@]}" env printenv LEAN_PATH)"
lean_path="$(pwd)/$cache_dir/lib/lean:$package_lean_path"

if [[ -z "${LEANPDE_SOURCE_REVISION:-}" && -e "$repo_root/.git" ]]; then
  export LEANPDE_SOURCE_REVISION="$(git -C "$repo_root" rev-parse HEAD)"
fi
LEAN_PATH="$lean_path" LEAN_SRC_PATH="$package_source_path" \
  "$lean_bin" "${lean_profile_args[@]}" \
  --run ../Blueprint.lean --output "$output_dir"

manifest="$site_dir/-verso-data/blueprint-manifest.json"

python3 "$tools_root/build-dependency-atlas.py" \
  "$manifest" \
  "$site_dir/-verso-data/leanpde-dependency-atlas.svg"
node "$tools_root/optimize-site.mjs" \
  "$site_dir" \
  "$repo_root/Blueprint/.lake/packages/verso/vendored-js/marked/marked.umd.min.js"
node "$tools_root/defer-heavy-blocks.mjs" "$site_dir"

printf 'Blueprint generated at %s\n' "$site_dir"
