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
# Litex website: https://litexlang.com 
# Litex github repository: https://github.com/litexlang/golitex 
# Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/




# 递归统计 Go 项目中的函数数量（以 `func` 开头的行）
count_funcs() {
    local dir="$1"
    local total=0

    # 遍历所有 .go 文件
    while IFS= read -r file; do
        # 统计当前文件中以 `func` 开头的行数
        cnt=$(grep -c '^func ' "$file" 2>/dev/null)
        if [ "$cnt" -gt 0 ]; then
            echo "$file: $cnt"
            total=$((total + cnt))
        fi
    done < <(find "$dir" -type f -name "*.go")

    echo "----------------------------------"
    echo "Total functions in project: $total"
}

# 用法：./count_funcs.sh <项目目录>
if [ $# -eq 0 ]; then
    echo "Usage: $0 <project_directory>"
    exit 1
fi

count_funcs "$1"