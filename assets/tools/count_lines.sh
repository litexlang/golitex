#!/bin/bash

find . -type f \( -name "*.go" -o -name "*.md" -o -name "*.lix" -o -name "*.sh" \) \
    | xargs wc -l \
    | tee /dev/stderr \
    | tail -1 \
    | awk '{print "lines:", $1}'; \
    echo "files: $(find . -type f \( -name "*.go" -o -name "*.md" -o -name "*.lix" -o -name "*.sh" \) | wc -l)"