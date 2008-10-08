#!/bin/sh
set -e
mkdir qs-avg
./make_dep_graph.sh
cp *.v README.html SConstruct dep_graph.png qs-avg
tar -czf ../qs-avg-`date +"%Y%m%dT%H%M"`.tar.gz qs-avg
rm -rf qs-avg
