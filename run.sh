set -e  # die on error

make -s

./f $1 \
	| awk 'NR % 5 == 4' \
	| sed 's/$/;/'      \
	| ./fullrecon/f /dev/stdin
