#!/bin/bash

rm -f *.log *.opb *.out output.txt 
for i in *.src
do
	base=`basename $i .src`
	../autopar $i >& $base.log
	cp min.opb $base.opb
	cp output.txt $base.out
done
