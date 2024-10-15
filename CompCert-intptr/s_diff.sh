#!/bin/bash

# Check if exactly two directories are provided as arguments
if [ "$#" -ne 2 ]; then
    echo "Usage: $0 <directory1> <directory2>"
    exit 1
fi

DIR1=$1
DIR2=$2

# Check if both arguments are directories
if [ ! -d "$DIR1" ] || [ ! -d "$DIR2" ]; then
    echo "Both arguments must be directories."
    exit 1
fi

# Loop over all .s files in the first directory
for FILE1 in "$DIR1"/*.s; do
    BASENAME=$(basename "$FILE1")
    FILE2="$DIR2/$BASENAME"

    # Check if the corresponding file exists in the second directory
    if [ ! -f "$FILE2" ]; then
        echo "$BASENAME missing in $DIR2"
        continue
    fi
    
    # Compare the two files; only print if they are different
    if ! diff -q "$FILE1" "$FILE2" >/dev/null; then
        echo "$BASENAME different"
    fi
    
    # Compare the two files
    #if diff -q "$FILE1" "$FILE2" >/dev/null; then
    #    echo "$BASENAME same"
    #else
    #    echo "$BASENAME different"
    #fi
done
