#!/usr/bin/env bash
set -euo pipefail
export PYTHONDONTWRITEBYTECODE=1

repo_root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$repo_root"

echo "[1/9] Verifying supplementary exact-search artifacts"
python3 scripts/check_search_artifact.py

echo "[2/9] Reproducing arithmetic kernel certificates"
python3 -I search/e274/generate_arithmetic_kernel_certificates.py --check

echo "[3/9] Reproducing fiber kernel certificates"
python3 -I search/e274/generate_fiber_kernel_dfs_certificates.py

echo "[4/9] Building the controlled Lean dependency closure"
python3 scripts/build_lean_controlled.py --jobs 2

echo "[5/9] Auditing theorem endpoints and axioms"
axiom_output="$(lake env lean AxiomAudit.lean 2>&1)"
printf '%s\n' "$axiom_output"
printf '%s\n' "$axiom_output" | python3 scripts/check_axiom_output.py

echo "[6/9] Scanning theorem-facing Lean sources"
first_party_lean=(ErdosProblems AxiomAudit.lean ErdosProblems.lean)
if grep -R -n -E --include='*.lean' \
  '(^|[^[:alnum:]_])(sorry|admit)([^[:alnum:]_]|$)' \
  "${first_party_lean[@]}"; then
  echo "Lean proof placeholder found" >&2
  exit 1
fi
if grep -R -n -E --include='*.lean' \
  '^[[:space:]]*(@\[[^]]*\][[:space:]]*)*((private|protected|local)[[:space:]]+)*(axiom|axioms|constant|constants|unsafe)([[:space:]]|$)' \
  "${first_party_lean[@]}"; then
  echo "First-party primitive or unsafe declaration found" >&2
  exit 1
fi
if grep -R -n -E --include='*.lean' \
  '(^|[^[:alnum:]_])(native_decide|bv_decide|nativeEqTrue|implemented_by|extern)([^[:alnum:]_]|$)' \
  "${first_party_lean[@]}"; then
  echo "Native/compiler or external implementation boundary found" >&2
  exit 1
fi

sha256_file() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | awk '{print $1}'
  else
    shasum -a 256 "$1" | awk '{print $1}'
  fi
}

verify_manifest() {
  local manifest="$1"
  local entries=0
  local line=""
  local expected=""
  local path=""
  local actual=""
  while IFS= read -r line || [ -n "$line" ]; do
    [ -n "$line" ] || continue
    read -r expected path <<< "$line"
    if ! [[ "$expected" =~ ^[0-9a-f]{64}$ ]] || [ -z "$path" ]; then
      echo "Malformed manifest line in $manifest: $line" >&2
      exit 1
    fi
    if [ ! -f "$path" ]; then
      echo "Manifest file is missing: $path" >&2
      exit 1
    fi
    actual="$(sha256_file "$path")"
    if [ "$actual" != "$expected" ]; then
      echo "SHA-256 mismatch: $path" >&2
      exit 1
    fi
    entries=$((entries + 1))
  done < "$manifest"
  if [ "$entries" -eq 0 ]; then
    echo "Manifest is empty: $manifest" >&2
    exit 1
  fi
}

echo "[7/9] Verifying source and PDF manifests"
verify_manifest third_party/e274/SOURCE_SNAPSHOT_MANIFEST.tsv
expected_source_paths="$(cut -c67- third_party/e274/SOURCE_SNAPSHOT_MANIFEST.tsv | sort)"
actual_source_paths="$(find third_party/e274 -maxdepth 1 -type f \
  ! -name 'SOURCE_SNAPSHOT_MANIFEST.tsv' | sort)"
if [ "$actual_source_paths" != "$expected_source_paths" ]; then
  echo "Source snapshot manifest does not cover the exact source-record set" >&2
  diff -u <(printf '%s\n' "$expected_source_paths") \
    <(printf '%s\n' "$actual_source_paths") || true
  exit 1
fi
if [ "$(awk 'END { print NR + 0 }' RELEASE_MANIFEST.sha256)" -ne 1 ]; then
  echo "Release manifest must contain exactly one PDF" >&2
  exit 1
fi
if ! grep -Eq '^[0-9a-f]{64}  output/pdf/e274_at_least_18_review_candidate\.pdf$' \
  RELEASE_MANIFEST.sha256; then
  echo "Unexpected PDF path in release manifest" >&2
  exit 1
fi
verify_manifest RELEASE_MANIFEST.sha256

echo "[8/9] Verifying the complete release tree"
verify_manifest RELEASE_TREE_MANIFEST.sha256
generated_junk="$(find . \
  \( -path './.git' -o -path './.lake' \) -prune -o \
  \( -type d -name '__pycache__' -o -type f -name '*.pyc' -o -type f -name '.DS_Store' \) \
  -print | sort)"
if [ -n "$generated_junk" ]; then
  echo "Generated cache or Finder metadata found in the release tree:" >&2
  printf '%s\n' "$generated_junk" >&2
  exit 1
fi
expected_paths="$(cut -c67- RELEASE_TREE_MANIFEST.sha256 | sort)"
actual_paths="$(find . -type f \
  ! -path './.git/*' \
  ! -path './.lake/*' \
  ! -path './tmp/*' \
  ! -path './paper/main.aux' \
  ! -path './paper/main.log' \
  ! -path './paper/main.out' \
  ! -path './paper/main.synctex.gz' \
  ! -path '*/__pycache__/*' \
  ! -name '*.pyc' \
  ! -name 'RELEASE_TREE_MANIFEST.sha256' \
  | sed 's#^./##' | sort)"
if [ "$actual_paths" != "$expected_paths" ]; then
  echo "Release tree differs from RELEASE_TREE_MANIFEST.sha256" >&2
  diff -u <(printf '%s\n' "$expected_paths") <(printf '%s\n' "$actual_paths") || true
  exit 1
fi

echo "[9/9] Scanning release-facing text"
release_text=(
  README.md REPRODUCE.md CHANGELOG.md CITATION.cff VERIFICATION_RECORD.md paper/main.tex
  docs third_party/NOTICE.md
)
active_version_text=(README.md REPRODUCE.md CITATION.cff VERIFICATION_RECORD.md lakefile.toml paper/main.tex docs)
if grep -R -n -E \
  '0\.3\.[0-9]+-review-candidate|Review candidate v0\.3\.[0-9]+|0\.4\.1-review-candidate' \
  "${active_version_text[@]}"; then
  echo "Stale active review-candidate version found" >&2
  exit 1
fi
if grep -R -n -E -i 'source-independent' \
  README.md REPRODUCE.md CHANGELOG.md paper/main.tex docs search/e274; then
  echo "Overbroad implementation-independence wording found" >&2
  exit 1
fi
if grep -R -n -E -i 'source[- ]free|only non-local mathematical inputs' \
  README.md REPRODUCE.md CITATION.cff VERIFICATION_RECORD.md paper/main.tex \
  docs ErdosProblems AxiomAudit.lean scripts/check_axiom_output.py; then
  echo "Ambiguous theorem-boundary wording found" >&2
  exit 1
fi
if grep -R -n -E \
  'ErdosProblem274-AtLeast17|Erdos274AtLeast17|e274_at_least_17' \
  "${release_text[@]}"; then
  echo "Superseded release identifier found" >&2
  exit 1
fi
if grep -R -n -E -i \
  '(/Users/|\.codex|review_packages|publication_staging|session[_ -]?id|thread[_ -]?id|submission[_ -]?id|github[_ -]?token|ghp_[[:alnum:]]+|BEGIN (RSA |OPENSSH )?PRIVATE KEY)' \
  "${release_text[@]}"; then
  echo "Internal path, identifier, or secret pattern found" >&2
  exit 1
fi
if grep -R -n -E -i \
  '(^|[^[:alnum:]_])(impact|breakthrough|career|score|scoring|rating|ranking|groundbreaking|world-first|best-known)([^[:alnum:]_]|$)' \
  "${release_text[@]}"; then
  echo "Disallowed evaluation language found" >&2
  exit 1
fi

echo "All release-candidate checks passed."
