// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Litex email: <litexlang@outlook.com>
// Litex website: https://litexlang.org
// Litex github repository: https://github.com/litexlang/golitex
// Litex discord server: https://discord.gg/uvrHM7eS

package litex_global

import (
	"fmt"
	"strings"
)

func SplitLinesAndAdd4NIndents(line string, n uint32) string {
	if n == 0 {
		return line
	}

	spaces := strings.Repeat(Scope4Indents, int(n))
	lines := strings.Split(line, "\n")

	var builder strings.Builder
	// 预分配空间：原长度 + 缩进空间（每行4n个空格）
	builder.Grow(len(line) + len(spaces)*len(lines))

	// 处理第一行
	if len(lines) > 0 {
		builder.WriteString(spaces)
		builder.WriteString(lines[0])
	}

	// 处理剩余行
	for _, part := range lines[1:] {
		builder.WriteByte('\n')
		builder.WriteString(spaces)
		builder.WriteString(part)
	}

	return builder.String()
}

func InternalWarningMsg(s string, args ...any) string {
	return fmt.Sprintf("Interalnal Warning:\n%s\n\n", fmt.Sprintf(s, args...))
}

func WarningMsg(s string, args ...any) string {
	return fmt.Sprintf("Warning:\n%s\n\n", fmt.Sprintf(s, args...))
}
