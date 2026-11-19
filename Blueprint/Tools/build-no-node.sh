#!/usr/bin/env bash
# Compatibility entry point. The shared build leaves out its Node.js steps.
set -euo pipefail
exec bash "$(dirname "${BASH_SOURCE[0]}")/build.sh" --no-node "$@"
