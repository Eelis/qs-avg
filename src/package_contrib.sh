#!/bin/sh

set -ev

coq_makefile *.v > Makefile
touch .depend
make depend
mkdir QuicksortComplexity
cp *.v LICENSE QuicksortComplexity/
mv Makefile .depend QuicksortComplexity/
tar -czf ../QuicksortComplexity-`date +"%Y%m%dT%H%M"`.tar.gz QuicksortComplexity
rm -rf QuicksortComplexity
