#!/bin/bash
# usage: tools/build.sh chNN   -> full build, then chapter-only PDF in out/
set -e
cd "$(dirname "$0")/.."
mkdir -p out
python3 tools/lint.py
python3 tools/coverage.py "$1" || true
X() { xelatex -interaction=nonstopmode -halt-on-error -jobname="$1" "\def\jobincludes{$2}\input{main}" > "out/$1.log" 2>&1 || { tail -40 "out/$1.log"; exit 1; }; }
ALL=$(ls chapters/*.tex | sed 's/\.tex$//' | paste -sd, -)
X book "$ALL"; X book "$ALL"
X "$1" "chapters/$1"; X "$1" "chapters/$1"
grep -E "Overfull|Undefined|undefined" "out/$1.log" | head -20 || true
grep -c "Overfull" out/book.log || true
cp "$1.pdf" out/ && cp book.pdf out/
pdfinfo "out/$1.pdf" | grep Pages
