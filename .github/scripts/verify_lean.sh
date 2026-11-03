#!/usr/bin/env bash
set -euo pipefail

files=(MetaAxiom.lean UHA.lean)

for file in "${files[@]}"; do
  if [[ ! -f "$file" ]]; then
    echo "::error::Verified Lean source does not exist: $file"
    exit 1
  fi

  if grep -nE '\b(sorry|admit)\b' "$file"; then
    echo "::error::Found sorry/admit in $file"
    exit 1
  fi

  lake env lean "$file"
  echo "PASS $file"
done
