#!/bin/bash
# Copyright 2024 Jiachen Shen.
# 
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
# 
#     http://www.apache.org/licenses/LICENSE-2.0
# 
# Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
# Litex email: <litexlang@outlook.com>
# Litex website: https://litexlang.org 
# Litex github repository: https://github.com/litexlang/golitex 
# Litex Zulip community: https://litex.zulipchat.com




# 所有文件行数总和
find . -type f \( -name "*.go" -o -name "*.md" -o -name "*.lix" -o -name "*.sh" \) \
    | xargs wc -l \
    | tee /dev/stderr \
    | tail -1 \
    | awk '{print "total lines:", $1}'

# 所有文件数量
echo "total files: $(find . -type f \( -name "*.go" -o -name "*.md" -o -name "*.lix" -o -name "*.sh" \) | wc -l)"

# 单独统计 .go 文件行数
echo "go lines: $(find . -type f -name "*.go" | xargs wc -l | tail -1 | awk '{print $1}')"

echo "go files: $(find . -type f -name "*.go" | wc -l)"

echo "func lines: $(grep -r '^func\b' ./*/*.go | wc -l)"
