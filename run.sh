make

mkfifo fifo
./f test.f \
	| awk 'NR % 4 == 3' \
	| sed 's/$/;/'      \
	> fifo &

fullrecon/f fifo

