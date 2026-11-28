#!/usr/bin/env bash
# Render with the shared build, omitting its Node.js steps.
set -euo pipefail
exec bash "$(dirname "${BASH_SOURCE[0]}")/build.sh" --no-node "$@"
