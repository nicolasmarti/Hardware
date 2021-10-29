#echo $@
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" > /dev/null && pwd )"
DIR1=$DIR
DIR2=$DIR/01
DIR3=$DIR/02

why3 ide -L $DIR1 -L $DIR2 -L $DIR3 $@
