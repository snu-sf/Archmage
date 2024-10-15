#!/bin/bash

# List of subdirectories to compare
SUBDIRS=("abi" "c" "compression" "raytracer" "regression" "spass")

# Check if s_diff.sh is present and executable
if [ ! -x ./s_diff.sh ]; then
    echo "Error: s_diff.sh not found or not executable."
    exit 1
fi

# Run 'make all' in test and test_orig directories
echo "Running 'make all' in test/ and test_orig/..."
for DIR in test test_orig; do
    if [ -d "$DIR" ]; then
        (cd "$DIR" && make all)
        if [ $? -ne 0 ]; then
            echo "Error: 'make all' failed in $DIR."
            exit 1
        fi
    else
        echo "Error: Directory $DIR not found."
        exit 1
    fi
done

# Ensure find_casts.sh exists and is executable
if [ ! -x ./find_casts.sh ]; then
    echo "Error: find_casts.sh not found or not executable."
    exit 1
fi

# Execute find_casts.sh
./find_casts.sh test

# Compare subdirectories
for SUBDIR in "${SUBDIRS[@]}"; do
    echo "Comparing $SUBDIR..."
    ./s_diff.sh "test_orig/$SUBDIR/" "test/$SUBDIR/"
done

echo "Comparison complete."
