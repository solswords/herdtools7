#!/bin/bash

if [[ $(basename `pwd`) != "aslreftests" ]]; then
    echo "Only run from the aslreftests directory";
    exit 1;
fi

export PATH=$(cd ..; pwd)/bin:$PATH

rm -rf _build

cp -rp ../../tests/*.t .

for f in `find . -name '*.t'`; do
    if [ -f $f ]; then
	sed -e 's/$ aslref/$ run-aslref-test.sh/' $f > $f.new;
	mv $f.new $f;
    fi;
done



time dune runtest . --root=.
