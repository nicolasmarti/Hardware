#echo $@
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" > /dev/null && pwd )"

why3 ide -L $DIR -L $DIR/01 -L $DIR/02 -L $DIR/03 $@
