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
# Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

import sys
import os

def escape_content(content):
    # 替换特殊字符
    escaped = (
        content.replace("\\", "\\\\")  # 先转义反斜杠
              .replace("\n", "\\n")   # 换行符
              .replace("\t", "\\t")   # 制表符
              .replace('"', '\\"')   # 双引号
              .replace("'", "\\'")    # 单引号
    )
    return f"$'{escaped}'"  # 用 $'' 包裹

# 执行 litex -e 命令
def execute_litex_e(content):
    escaped = escape_content(content)
    os.system(f"litex -e {escaped}")

if __name__ == "__main__":
    # 从文件读取
    filename = "input.txt"  # 替换为你的文件名
    with open(filename, "r") as f:
        content = f.read()
    
    execute_litex_e(content)

    