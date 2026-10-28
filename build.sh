#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
ISABELLE="${ISABELLE:-isabelle}"
"$ISABELLE" version
"$ISABELLE" build -j 1 -o threads=1 -o document_variants= \
  -d sources/Thomistic_Causal_Arguments -d extensions -d ancillary \
  -d revision-extras -d context-extension -d determination-extension \
  -d grounded-extension -d source-sharing -d copy-majority -d pattern-extension \
  Causal_Efficacy_Patterns Source_Sharing_Spines Copy_Majority_Representation
python3 tests/check_finite_mechanisms.py
python3 tests/check_context_determination.py
python3 tests/check_determination_patterns.py
