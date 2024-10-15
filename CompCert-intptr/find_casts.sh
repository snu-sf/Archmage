#!/bin/bash

# Check if exactly one directory is provided as an argument
if [ "$#" -ne 1 ]; then
    echo "Usage: $0 <directory>"
    exit 1
fi

SEARCH_DIR=$1

# Check if the directory exists
if [ ! -d "$SEARCH_DIR" ]; then
    echo "Error: Directory $SEARCH_DIR not found."
    exit 1
fi

echo "Searching for clight files containing casting in $SEARCH_DIR..."

# Recursively find *.light.c files and search for "capture"
find "$SEARCH_DIR" -type f -name "*.light.c" | while read -r FILE; do
    if grep -q "capture" "$FILE"; then
        echo "Found pointer to integer casting in: $FILE"
    fi
done

echo "Search complete."
