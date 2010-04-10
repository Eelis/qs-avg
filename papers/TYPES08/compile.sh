#!/bin/sh

lhs2TeX < paper.tex > processed.tex
cp processed.tex tmp.tex

set -e
pdflatex tmp.tex
bibtex tmp
pdflatex tmp.tex
bibtex tmp
pdflatex tmp.tex
cat tmp.pdf > paper.pdf
rm tmp.*
