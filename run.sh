make -s

./f $1 \
	| awk 'NR % 4 == 3' \
	| sed 's/$/;/'      \
	| ./fullrecon/f /dev/stdin