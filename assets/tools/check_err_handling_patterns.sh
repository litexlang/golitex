#!/bin/bash
# Copyright 2024 litexlang.org Jiachen Shen
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.


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