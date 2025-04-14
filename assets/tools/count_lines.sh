#!/bin/bash
# Copyright 2024 Jiachen Shen.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Original Author: Jiachen Shen (malloc_realloc_calloc@outlook.com)
# Visit litexlang.org and https://github.com/litexlang/golitex for more information.


find . -type f \( -name "*.go" -o -name "*.md" -o -name "*.lix" -o -name "*.sh" \) \
    | xargs wc -l \
    | tee /dev/stderr \
    | tail -1 \
    | awk '{print "lines:", $1}'; \
    echo "files: $(find . -type f \( -name "*.go" -o -name "*.md" -o -name "*.lix" -o -name "*.sh" \) | wc -l)"