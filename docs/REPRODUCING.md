# Reproducing the rc3 port

Use an already installed trusted `leanprover/lean4:v4.35.0-rc3` toolchain. There are no external Lake packages and no Mathlib dependency. No automatic installation or fetch script is included.

From the repository root, check source custody and build all modules serially:

```sh
python3 scripts/check_source.py
export LEAN_NUM_THREADS=1
python3 - <<'PY'
from pathlib import Path
import subprocess
for source in [Path('HamParity.lean'), *sorted(Path('HamParity').glob('*.lean'))]:
    module = source.with_suffix('').as_posix().replace('/', '.')
    subprocess.run(['lake', 'build', '+' + module + ':olean'], check=True, timeout=240)
PY
```

The exact installed verifier pins/hashes are in `verification/tools.json`. Select your already installed matching rc3 exporter and tools; these placeholders are not executable defaults:

```sh
export LEAN_TC=/absolute/path/to/lean-4.35.0-rc3
export COMPARATOR_BIN=/absolute/path/to/comparator
export COMPARATOR_LEAN4EXPORT=/absolute/path/to/matching-4.35.0-rc3/lean4export
export COMPARATOR_LANDRUN=/absolute/path/to/landrun
export PATH="$LEAN_TC/bin:$PATH"
export LEAN_PATH="$PWD/.lake/build/lib/lean:$LEAN_TC/lib/lean"
export LEAN_NUM_THREADS=1
"$COMPARATOR_BIN" comparator-finite-oracle.json
```

For individual checks, use a fresh temporary copy of the configuration selecting one theorem name at a time, keeping its query definition and axiom allowlist unchanged. Successful recorded runs printed both `Lean default kernel accepts the solution` and `Your solution is okay!` and exited 0. The altered-statement fixture was rejected after successful export, not because of a tool error. The `RegistryAudit` build prints actual target axiom dependencies.

Use a guarded environment for long builds. The recorded workflow used one thread, nice10/BelowNormal, CPUQuota100%, a 16 GiB aggregate cap, zero swap, an 8 GiB host-free floor, per-process deadlines and an allocation deadline. The command snippets alone do not install those resource controls. Original native Linux tools and the unchanged default sandbox policy were used; stop on access denials rather than changing security settings. No hosted Palomar/NanoDa result is implied.
