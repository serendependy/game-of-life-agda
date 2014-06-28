#!/bin/bash

for i in $(seq 0 $2);
do
	./GOL $1 $i
	sleep 1
done
