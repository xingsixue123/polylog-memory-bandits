#!/usr/bin/env bash
# Full check: build, kernel replay of every module, and the axioms and statements of the main declarations.
# Run from the repository root after `lake exe cache get`. Writes its logs to ./verify_out/.
set -euo pipefail
cd "$(dirname "$0")/.."
out=verify_out
mkdir -p "$out"

echo "== 1/3 lake build"
lake build > "$out/build.log" 2>&1 || { tail -40 "$out/build.log"; echo "BUILD FAILED"; exit 1; }
if grep -nE "declaration uses 'sorry'|^error" "$out/build.log"; then echo "FAILED: sorry or error in build log"; exit 1; fi
echo "   ok (log: $out/build.log)"

echo "== 2/3 kernel replay of every module"
mods=$( { echo Pool; echo Checks; echo Pool.Prelude; sed -n 's/^import //p' Pool.lean Checks.lean; } | sort -u )
# One process per module, JOBS in parallel (default 4; each process needs a few GB of RAM).
printf '%s\n' $mods | xargs -P "${JOBS:-4}" -I{} lake env lean --run check/Check.lean --replay {} > "$out/replay.jsonl"
total=$(printf '%s\n' $mods | wc -l)
okc=$(grep -c '"ok":true' "$out/replay.jsonl" || true)
consts=$(grep -o '"constants":[0-9]*' "$out/replay.jsonl" | cut -d: -f2 | awk '{s+=$1} END {print s}')
echo "   $okc / $total modules replayed ok, $consts constants"
[ "$okc" = "$total" ] || { grep -v '"ok":true' "$out/replay.jsonl"; echo "FAILED: replay (missing or failed modules)"; exit 1; }

echo "== 3/3 statements and axioms"
decls="Pool.P0294.main Restated.achievable Audit3.pool_refModel Audit3.strict_of_minimax Audit.explicit_numeric Audit3E.famE_trivial Audit.bound_ge_T"
lake env lean --run check/Check.lean --decls Pool Checks -- $decls > "$out/decls.jsonl"
python3 - "$out/decls.jsonl" <<'PY'
import json, sys
std = {"propext", "Classical.choice", "Quot.sound"}
bad = False
for line in open(sys.argv[1]):
    j = json.loads(line)
    if "decl" not in j:
        continue
    ax = set(j.get("axioms", []))
    ok = j.get("present") and ax <= std
    bad |= not ok
    print(f"   {'ok ' if ok else 'BAD'} {j['decl']}  axioms={sorted(ax)}")
sys.exit(1 if bad else 0)
PY
echo "ALL CHECKS PASSED"
