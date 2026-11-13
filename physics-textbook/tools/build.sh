#!/bin/sh
# Build the sample: regenerate tables and the compass, then run pdflatex three times.
set -e
cd "$(dirname "$0")/.."
python3 tools/multab.py
python3 tools/compass.py
for n in 1 2 3; do pdflatex -interaction=nonstopmode -halt-on-error main.tex >/dev/null; done
grep -c 'Overfull' main.log || true
pdfinfo main.pdf | grep Pages
