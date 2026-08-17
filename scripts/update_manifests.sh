#!/usr/bin/env bash
set -euo pipefail
export PYTHONDONTWRITEBYTECODE=1

repo_root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$repo_root"
export LC_ALL=C

sha256_file() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | awk '{print $1}'
  else
    shasum -a 256 "$1" | awk '{print $1}'
  fi
}

source_manifest="third_party/e274/SOURCE_SNAPSHOT_MANIFEST.tsv"
source_tmp="${source_manifest}.tmp"
: > "$source_tmp"
while IFS= read -r path; do
  printf '%s  %s\n' "$(sha256_file "$path")" "$path" >> "$source_tmp"
done < <(find third_party/e274 -maxdepth 1 -type f \
  ! -name 'SOURCE_SNAPSHOT_MANIFEST.tsv' \
  ! -name 'SOURCE_SNAPSHOT_MANIFEST.tsv.tmp' | sort)
mv "$source_tmp" "$source_manifest"

pdf_path="output/pdf/e274_at_least_18_review_candidate.pdf"
test -s "$pdf_path"
printf '%s  %s\n' "$(sha256_file "$pdf_path")" "$pdf_path" \
  > RELEASE_MANIFEST.sha256

tree_tmp="RELEASE_TREE_MANIFEST.sha256.tmp"
: > "$tree_tmp"
while IFS= read -r path; do
  clean_path="${path#./}"
  printf '%s  %s\n' "$(sha256_file "$clean_path")" "$clean_path" >> "$tree_tmp"
done < <(find . -type f \
  ! -path './.git/*' \
  ! -path './.lake/*' \
  ! -path './tmp/*' \
  ! -path './paper/main.aux' \
  ! -path './paper/main.log' \
  ! -path './paper/main.out' \
  ! -path './paper/main.synctex.gz' \
  ! -path '*/__pycache__/*' \
  ! -name '*.pyc' \
  ! -name '.DS_Store' \
  ! -name 'RELEASE_TREE_MANIFEST.sha256' \
  ! -name 'RELEASE_TREE_MANIFEST.sha256.tmp' | sort)
mv "$tree_tmp" RELEASE_TREE_MANIFEST.sha256

echo "Updated source, PDF, and release-tree manifests."
