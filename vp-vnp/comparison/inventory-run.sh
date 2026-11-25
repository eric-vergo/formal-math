#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# Authors: Eric Vergo, GPT-6.2 (OpenAI)
set -euo pipefail
if [[ $# -ne 4 ]]; then
  printf 'usage: %s GIT_REV VP_VNP_SOURCE BUILD_VP_VNP OUTPUT_DIRECTORY\n' "$0" >&2
  exit 2
fi
revision=$1
source_dir=$(cd "$2" && pwd)
build_dir=$(cd "$3" && pwd)
mkdir -p "$4"
output_dir=$(cd "$4" && pwd)
here=$(cd "$(dirname "$0")" && pwd)
generated="$source_dir/blueprint/VpVnpBlueprint/Generated"
compiled="$build_dir/.lake/build/lib/lean"
if [[ ! -d "$generated" ]]; then
  printf 'Generate blueprint chapters in %s first.\n' "$source_dir" >&2
  exit 2
fi
cd "$build_dir"
python3 - "$source_dir" "$output_dir" "$here" <<'PY'
from pathlib import Path
import re
import subprocess
import sys

source, output, helpers = map(Path, sys.argv[1:])
docs = "\n".join(p.read_text() for p in (source / "blueprint/VpVnpBlueprint").rglob("*.lean")
                 if "Generated" not in p.relative_to(source).parts)
direct = {name.strip() for assoc in re.findall(r'lean := "([^"]*)"', docs)
          for name in assoc.split(",") if name.strip()}
inline = {n.strip() for n in re.findall(r'\{InlineLean\.name[^}]*\}\x60([^`]+)`', docs)}
qualified = set(re.findall(r'\b(?:Paper|Statement|Solution|Nc|NS1|Ov)(?:\.[\w\x27]+)+', docs))
roots = output / "blueprint-roots.txt"
roots.write_text("\n".join(sorted(direct | inline | qualified)) + "\n")
proof_files = [source / "Paper.lean", source / "Statement.lean"]
for directory in ("Nc", "NS1", "Ov", "Paper", "Comparator"):
    proof_files.extend((source / directory).rglob("*.lean"))
modules = sorted(".".join(p.relative_to(source).with_suffix("").parts)
                 for p in proof_files if p.stem != "Challenge")
with (output / "kernel.json").open("w") as kernel:
    subprocess.run(["lake", "env", "lean", "--run", helpers.parent / "scripts/InventoryKernel.lean",
                    roots, *modules], stdout=kernel, check=True)
PY
python3 "$here/inventory.py" --revision "$revision" --source "$source_dir" --compiled "$compiled" \
  --generated "$generated" --kernel "$output_dir/kernel.json" --output "$output_dir/inventory.json"
