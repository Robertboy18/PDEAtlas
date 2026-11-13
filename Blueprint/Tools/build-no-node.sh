#!/usr/bin/env bash

# Render the Blueprint site on a machine without Node.js.
#
# `build.sh` needs Node.js for three steps. This script leaves them out:
#   * the textbook map is not regenerated: the committed
#     `Blueprint/Generated/TextbookMapData.lean` is compiled as it is;
#   * `optimize-site.mjs` does not run: the pages keep Verso's own shell, without
#     the logo, the theme button, the section rail, the "Proof map" actions, the
#     page descriptions, the Introduction notebook, the learning features and the
#     typeset figure labels, and they load Marked from its CDN;
#   * `defer-heavy-blocks.mjs` does not run: the proof and hover payloads stay
#     inside the pages, which are several megabytes each.
# The libraries, the renderer and the pre-rendered dependency atlas are those of
# `build.sh`. The default output is `_out/site-no-node`, so the two builds do not
# overwrite each other.
#
# The Mathlib cache is not downloaded. On a fresh clone run `lake exe cache get`
# in the repository root and in `Blueprint/` first.
#
# Every Lake call goes through `LEANPDE_LAKE` (default `lake`), and the renderer
# runs under it as `lake env lean --run`. A machine that schedules its builds or
# limits their memory can name a launcher there that takes Lake's arguments.

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
tools_root="$repo_root/Blueprint/Tools"
output_root="$repo_root/_out"
certificates="${LEANPDE_CERTIFICATES:-kernel}"
case "$certificates" in
  kernel) cache_dir=".lake/build"; default_site="$output_root/site-no-node" ;;
  fast|native) certificates=fast; cache_dir=".lake/build-fast"; default_site="$output_root/site-fast-no-node" ;;
  *) printf 'Certificate profile must be kernel or fast.\n' >&2; exit 2 ;;
esac
export LEANPDE_CERTIFICATES="$certificates"
lake_profile_args=("-Kcertificates=$certificates")
lean_profile_args=()
if [[ "$certificates" == kernel ]]; then
  lean_profile_args+=("-Dweak.cega.nativeCertificates=false")
fi
requested_output="${1:-$default_site}"
read -r -a lake <<< "${LEANPDE_LAKE:-lake}"

for command in realpath "${lake[0]}" python3 dot; do
  if ! command -v "$command" >/dev/null 2>&1; then
    printf 'The Blueprint build without Node.js requires %s.\n' "$command" >&2
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

cd "$repo_root/Blueprint"

# As in `build.sh`: reconfigure once in each package, then apply the Verso anchor
# patch that Lake's `post_update` hook applies only on `lake update`.
(cd "$repo_root" && "${lake[@]}" -R "${lake_profile_args[@]}" build PDE)
"${lake[@]}" -R "${lake_profile_args[@]}" env true
python3 "$tools_root/patch_verso_anchors.py" "$repo_root/Blueprint/.lake/packages/verso"

python3 "$tools_root/build-cas-ledger.py"

# Declaration snapshots resolve source files while the chapters compile.
package_source_path="$("${lake[@]}" "${lake_profile_args[@]}" env printenv LEAN_SRC_PATH)"
LEAN_SRC_PATH="$package_source_path" \
  "${lake[@]}" "${lake_profile_args[@]}" build VersoBlueprint:shared Blueprint

mkdir -p "$output_dir"
find "$output_dir" -mindepth 1 -depth -delete

# Put the nested package's own artifacts first, as `build.sh` does.
package_lean_path="$("${lake[@]}" "${lake_profile_args[@]}" env printenv LEAN_PATH)"
lean_path="$(pwd)/$cache_dir/lib/lean:$package_lean_path"

if [[ -z "${LEANPDE_SOURCE_REVISION:-}" && -e "$repo_root/.git" ]]; then
  export LEANPDE_SOURCE_REVISION="$(git -C "$repo_root" rev-parse HEAD)"
fi
"${lake[@]}" "${lake_profile_args[@]}" env \
  env LEAN_PATH="$lean_path" LEAN_SRC_PATH="$package_source_path" \
  lean "${lean_profile_args[@]}" --run ../Blueprint.lean --output "$output_dir"

python3 "$tools_root/build-dependency-atlas.py" \
  "$site_dir/-verso-data/blueprint-manifest.json" \
  "$site_dir/-verso-data/leanpde-dependency-atlas.svg"

# Every page names the favicon; `optimize-site.mjs` would have copied the brand files.
mkdir -p "$site_dir/-verso-data/leanpde-brand"
cp "$repo_root/Blueprint/Assets/Brand/"{logo-light.webp,logo-dark.webp,favicon.png} \
  "$site_dir/-verso-data/leanpde-brand/"

printf 'Blueprint generated without the Node.js steps at %s\n' "$site_dir"
