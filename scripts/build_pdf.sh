#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$repo_root"

mode="${1:---check}"
case "$mode" in
  --check|--write|--compile) ;;
  *)
    echo "Usage: $0 [--check|--write|--compile]" >&2
    exit 2
    ;;
esac

source_date_epoch="1786806000"
pdf_path="output/pdf/e274_at_least_18_review_candidate.pdf"
manifest_path="RELEASE_MANIFEST.sha256"

latexmk_bin="${LATEXMK:-$(command -v latexmk || true)}"
if [ -z "$latexmk_bin" ]; then
  echo "latexmk is required; set LATEXMK to its executable path" >&2
  exit 1
fi
latex_bin_dir="$(cd "$(dirname "$latexmk_bin")" && pwd)"
pdftex_bin="${PDFTEX:-$latex_bin_dir/pdftex}"
if [ ! -x "$pdftex_bin" ]; then
  pdftex_bin="$(command -v pdftex || true)"
fi
if [ -z "$pdftex_bin" ] || [ ! -x "$pdftex_bin" ]; then
  echo "pdfTeX is required; set PDFTEX to its executable path" >&2
  exit 1
fi

sha256_file() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | awk '{print $1}'
  else
    shasum -a 256 "$1" | awk '{print $1}'
  fi
}

tmp_dir="$(mktemp -d "${TMPDIR:-/tmp}/e274-pdf.XXXXXX")"
trap 'rm -rf "$tmp_dir"' EXIT

pretex='\pdfinfoomitdate=1 \pdftrailerid{} \pdfsuppressptexinfo=-1 '
SOURCE_DATE_EPOCH="$source_date_epoch" \
FORCE_SOURCE_DATE=1 \
PATH="$latex_bin_dir:$PATH" \
"$latexmk_bin" \
  -pdf \
  -silent \
  -interaction=nonstopmode \
  -halt-on-error \
  -file-line-error \
  -usepretex="$pretex" \
  -outdir="$tmp_dir" \
  paper/main.tex

built_pdf="$tmp_dir/main.pdf"
test -s "$built_pdf" || {
  echo "latexmk did not produce a nonempty PDF" >&2
  exit 1
}
if grep -Eq 'There were undefined references|Citation .* undefined|Reference .* undefined' \
  "$tmp_dir/main.log"; then
  echo "The manuscript build contains unresolved citations or references" >&2
  exit 1
fi

if [ "$mode" = "--compile" ]; then
  echo "Manuscript source compiled successfully"
  exit 0
fi

if [ "$mode" = "--write" ]; then
  mkdir -p "$(dirname "$pdf_path")"
  cp "$built_pdf" "$pdf_path"
  printf '%s  %s\n' "$(sha256_file "$pdf_path")" "$pdf_path" > "$manifest_path"
  echo "Updated $pdf_path and $manifest_path"
  exit 0
fi

test -s "$pdf_path" || {
  echo "Committed PDF is missing or empty: $pdf_path" >&2
  exit 1
}
if ! cmp -s "$built_pdf" "$pdf_path"; then
  echo "Committed PDF does not match this deterministic TeX Live build" >&2
  echo "latexmk: $("$latexmk_bin" -v | head -n 1)" >&2
  echo "pdfTeX:  $("$pdftex_bin" --version | head -n 1)" >&2
  echo "built:     $(sha256_file "$built_pdf")" >&2
  echo "committed: $(sha256_file "$pdf_path")" >&2
  exit 1
fi
echo "Deterministic TeX Live build matches $pdf_path"
