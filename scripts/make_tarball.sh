#!/bin/bash
set -ev
cd ..
rm -f qs-avg.tar.gz
tar -czf qs-avg.tar.gz qs-avg/src/{*.v,README.html,SConstruct} qs-avg/paper/{README.txt,abstract.ltx,compile.sh,llncs.cls,macros.sty,paper.bib,paper.pdf,paper.tex,processed.tex,splncs.bst}
