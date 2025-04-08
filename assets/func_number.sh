#!/bin/bash

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