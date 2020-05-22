set -o pipefail

make -s

if [ $? -ne 0 ]; then
	echo !!!! ERROR !!!!
	echo failed to build the program
	exit 1
fi

./f $1 \
	| awk 'NR % 5 == 4' \
	| sed 's/$/;/'      \
	| ./fullrecon/f /dev/stdin

if [ $? -ne 0 ]; then
	echo !!!! ERROR !!!!
	echo An error occured during the processing
	exit 1
fi
