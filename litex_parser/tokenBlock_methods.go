package litex_parser

import (
	"fmt"
	"strings"
)

type TokenBlock struct {
	Header strSliceCursor
	Body   []TokenBlock
}

func (b *TokenBlock) String() string {
	return b.stringWithIndent(0)
}

func (b *TokenBlock) stringWithIndent(indentLevel int) string {
	indent := strings.Repeat("  ", indentLevel) // 根据缩进级别生成缩进字符串
	result := fmt.Sprintf("%s%s\n", indent, strings.Join(b.Header.getSlice(), " "))

	// 递归处理子块
	if b.Body != nil {
		for _, subBlock := range b.Body {
			result += subBlock.stringWithIndent(indentLevel + 1)
		}
	}

	return result
}
