#!/bin/bash

# 获取 main.go 文件的路径
# 如果脚本在项目根目录，直接使用 main.go
# 否则尝试从脚本所在目录向上查找 main.go
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
MAIN_GO=""

# 首先尝试脚本所在目录
if [ -f "$SCRIPT_DIR/main.go" ]; then
    MAIN_GO="$SCRIPT_DIR/main.go"
else
    # 向上查找 main.go
    CURRENT_DIR="$SCRIPT_DIR"
    while [ "$CURRENT_DIR" != "/" ]; do
        if [ -f "$CURRENT_DIR/main.go" ]; then
            MAIN_GO="$CURRENT_DIR/main.go"
            break
        fi
        CURRENT_DIR="$(dirname "$CURRENT_DIR")"
    done
fi

# 如果还是找不到，尝试当前工作目录
if [ -z "$MAIN_GO" ] && [ -f "main.go" ]; then
    MAIN_GO="main.go"
fi

# 如果找不到 main.go，报错
if [ -z "$MAIN_GO" ] || [ ! -f "$MAIN_GO" ]; then
    echo "Error: main.go not found" >&2
    exit 1
fi

# 提取 VERSION 常量的值
# 匹配格式: const VERSION = "版本号"
VERSION=$(grep 'const VERSION' "$MAIN_GO" | sed 's/.*"\(.*\)".*/\1/' | head -1)

# 输出版本号
if [ -n "$VERSION" ]; then
    echo "$VERSION"
else
    echo "Error: VERSION constant not found in $MAIN_GO" >&2
    exit 1
fi

