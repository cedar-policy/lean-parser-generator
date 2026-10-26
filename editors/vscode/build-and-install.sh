#!/usr/bin/env bash
# Copyright Cedar Contributors
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#      https://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
# Build and install the LIG VS Code extension, for convenience while developing it.
#
# Steps:
#   1. build the lig-language-server binary from the repo root (lake);
#   2. install the extension's npm dependencies (once);
#   3. package the extension into a .vsix (vsce);
#   4. install that .vsix into VS Code (the `code` CLI).
#
# Usage (from anywhere):
#   editors/vscode/build-and-install.sh            # all four steps
#   editors/vscode/build-and-install.sh --no-server # skip the lake build
#   editors/vscode/build-and-install.sh --package-only # build+package, don't install
#
# The `code` CLI must be on PATH for the install step (VS Code: "Shell Command:
# Install 'code' command in PATH"). Without it, step 4 is skipped and the .vsix
# path is printed so you can install it by hand.
set -euo pipefail

# Resolve the extension directory (where this script lives) and the repo root.
ext_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "$ext_dir/../.." && pwd)"

build_server=1
install=1
for arg in "$@"; do
  case "$arg" in
    --no-server) build_server=0 ;;
    --package-only) install=0 ;;
    -h|--help) sed -n '2,20p' "${BASH_SOURCE[0]}"; exit 0 ;;
    *) echo "unknown argument: $arg" >&2; exit 2 ;;
  esac
done

# 1. Build the language server.
if [[ "$build_server" == 1 ]]; then
  echo "==> building lig-language-server"
  ( cd "$repo_root" && lake build lig-language-server )
  echo "    -> $repo_root/.lake/build/bin/lig-language-server"
fi

cd "$ext_dir"

# 2. npm dependencies (only when missing).
if [[ ! -d node_modules ]]; then
  echo "==> npm install"
  npm install
fi

# 3. Package the .vsix. Read name+version from package.json without extra tools.
name="$(node -p "require('./package.json').name")"
version="$(node -p "require('./package.json').version")"
vsix="${name}-${version}.vsix"
echo "==> packaging $vsix"
npx --yes @vscode/vsce package --out "$vsix"

# 4. Install into VS Code.
if [[ "$install" == 1 ]]; then
  if command -v code >/dev/null 2>&1; then
    echo "==> installing $vsix into VS Code"
    code --install-extension "$vsix" --force
    echo "    reload the VS Code window (Developer: Reload Window) to pick up the update"
  else
    echo "==> 'code' CLI not found on PATH; skipping install"
    echo "    install manually with: code --install-extension $ext_dir/$vsix"
  fi
else
  echo "==> packaged only; install with: code --install-extension $ext_dir/$vsix"
fi
