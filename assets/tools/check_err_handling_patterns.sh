#!/bin/bash

# Recursively find all .go files and check for err handling patterns
find . -type f -name "*.go" | while read -r file; do
    # Use awk to check each file
    awk -v filename="$file" '
    /if err != nil \{/ {
        # Get the line number
        err_line = NR
        # Read the next line
        getline next_line
        # Check if next line contains "err"
        if (next_line !~ /err/) {
            print filename ":" err_line ": possible missing error handling"
            # Print the context (2 lines)
            print "    " $0
            print "    " next_line
            print ""
        }
        # Since we already read the next line, we need to adjust NR
        NR++
    }
    ' "$file"
done