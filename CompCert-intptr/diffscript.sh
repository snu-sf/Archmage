#!/bin/bash

# Check if two directory paths are provided as arguments
if [ "$#" -ne 2 ]; then
    echo "Usage: $0 <directory1> <directory2>"
    exit 1
fi

directory1="$1"
directory2="$2"

# Use find to get a list of .s files in directory1 and its subdirectories
find "$directory1" -type f -name "*.s" | while read -r file1; do
    # Extract the file name without the path and extension
    filename=$(basename "$file1" .s)

    # Construct the corresponding file path in directory2
    file2="$directory2/$filename.s"

    # Check if the file exists in both directories
    if [ -e "$file2" ]; then
        # Use diff to check for differences
        if ! diff -q "$file1" "$file2" > /dev/null; then
            echo "Files $filename.s differ"
        fi
    else
        echo "File $filename.s not found in $directory2"
    fi
done

