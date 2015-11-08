#!/bin/bash

rm -f output/*.log output/*.opb *.out output/output.txt 
for i in *.src
do
	base=`basename $i .src`
	../autopar $i >& output/$base.log
	cp min.opb output/$base.opb
	cp output.txt output/$base.out
done
