package litex_global

import (
	"strings"
)

func SplitLinesAndAdd4NIndents(line string, n uint32) string {
	if n == 0 {
		return line
	}

	spaces := strings.Repeat(ScopeIndent, int(n))
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
