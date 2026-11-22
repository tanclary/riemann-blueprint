#!/usr/bin/env bash
set -euo pipefail

# End-to-end reproduction pipeline for shrinking & distilling the Alpöge-Claude RH proof.
# Authors: Tanner Clary (@tanclary) & Gemini 4 Carbon

WORK="${1:-./work}"
mkdir -p "$WORK"
make -j

echo "[1/5] Downloading & SHA-256 verifying 239 MB Lean source archive from alpo.ge..."
if [[ ! -f "$WORK/lean.tar" ]]; then
  mkdir -p "$WORK/parts"
  curl -sSfL https://raw.githubusercontent.com/rohanarun/alpoge-rh-replay/main/parts.sha256 -o "$WORK/parts/parts.sha256"
  (cd "$WORK/parts" && xargs -P 8 -n 2 bash -c 'curl -sSfL --retry 3 -o "$2" "https://alpo.ge/lean.tar.gz.$2"' _ < parts.sha256 && sha256sum -c parts.sha256 && cat part[0-9]* > ../lean.tar.gz)
  echo "9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc  $WORK/lean.tar.gz" | sha256sum -c -
  gzip -dc "$WORK/lean.tar.gz" > "$WORK/lean.tar"
  rm -rf "$WORK/parts"
fi

echo "[2/5] Downloading MIT challenge & solution kernel exports..."
if [[ ! -f "$WORK/challenge.ndjson" ]]; then
  curl -sSfL https://math.mit.edu/~drew/grh/challenge.ndjson.zst -o "$WORK/challenge.ndjson.zst"
  zstd -d --long=27 -f "$WORK/challenge.ndjson.zst" -o "$WORK/challenge.ndjson"
  echo "bd484ac9886a96f26b1d9a7a59ebd45b7a70d102c015d4f31f9302bbdd6ab2b9  $WORK/challenge.ndjson" | sha256sum -c -
fi

if [[ ! -f "$WORK/solution.ndjson.zst" ]]; then
  curl -sSfL https://math.mit.edu/~drew/grh/solution.ndjson.zst -o "$WORK/solution.ndjson.zst"
  echo "61a8938ad5f5e57397c1c0e3b954916af546d9004ade01c3555744a681b05381  $WORK/solution.ndjson.zst" | sha256sum -c -
fi

echo "[3/5] Indexing 175,187 Lean source modules & extracting 1.065B-node kernel DAG..."
./bin/index_lean_tar "$WORK/lean.tar" "$WORK/modules.tsv" "$WORK/decls.tsv"
zstd -dc --long=27 "$WORK/challenge.ndjson.zst" | ./bin/extract_dag "$WORK/challenge_decls.tsv" "$WORK/challenge_edges.bin"
zstd -dc --long=30 "$WORK/solution.ndjson.zst" | ./bin/extract_dag "$WORK/solution_decls.tsv" "$WORK/solution_edges.bin"

echo "[4/5] Running Lengauer-Tarjan dominators & source compaction metrics..."
./bin/dominators "$WORK/modules.tsv" "$WORK/decls.tsv" "$WORK/challenge_decls.tsv" "$WORK/solution_decls.tsv" "$WORK/solution_edges.bin" "$WORK/dom_nodes.tsv"
./bin/compact_repo "$WORK/lean.tar" "$WORK/modules.tsv" "$WORK/decls.tsv" "$WORK/challenge_decls.tsv" "$WORK/solution_decls.tsv" "$WORK/solution_edges.bin"

echo "[5/5] Emitting CSE+GC shrunk kernel export (solution_shrunk.ndjson)..."
./bin/rewrite_export "$WORK/solution.ndjson.zst" "$WORK/challenge_decls.tsv" "$WORK/solution_shrunk.ndjson"
echo "Done! Verify with: con-ron --jobs=64 --compare $WORK/challenge.ndjson $WORK/solution_shrunk.ndjson"
