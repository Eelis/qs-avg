#!/bin/sh

lhs2TeX < paper.tex > processed.tex

set -e
pdflatex processed.tex
bibtex processed
pdflatex processed.tex
bibtex processed
pdflatex processed.tex
cat processed.pdf > paper.pdf
rm processed.*
