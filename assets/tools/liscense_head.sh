#!/bin/bash

# 删除旧版权头（多行注释）
find . -name "*.go" -exec sed -i '' '/^\/\*/,/\*\//{/Copyright/d;}' {} +

# 添加新头
addlicense -c "litexlang.org Foundation" -y 2024 -f LICENSE_TEMPLATE .

echo "Headers updated!"