package parser

import (
	"fmt"
	"strings"
)

const (
	Concept int = iota
	Property
	Var
	Type
	ConceptType
	TypeVar
)

type TokenStmtBlock struct {
	Header []string
	Body   []TokenStmtBlock
}

func (b *TokenStmtBlock) String() string {
	return b.stringWithIndent(0)
}

func (b TokenStmtBlock) stringWithIndent(indentLevel int) string {
	indent := strings.Repeat("  ", indentLevel) // 根据缩进级别生成缩进字符串
	result := fmt.Sprintf("%s%s\n", indent, strings.Join(b.Header, " "))

	// 递归处理子块
	for _, subBlock := range b.Body {
		result += subBlock.stringWithIndent(indentLevel + 1)
	}

	return result
}

func splitString(inputString string) []string {
	var result []string
	var buffer string
	for _, char := range inputString {
		switch char {
		case '[', ']', '(', ')', ':', '$', ',', '=', '*', '+', '-', '/':
			if buffer != "" {
				result = append(result, buffer)
				buffer = ""
			}
			result = append(result, string(char))
		case ' ':
			if buffer != "" {
				result = append(result, buffer)
				buffer = ""
			}
		default:
			buffer += string(char)
		}
	}
	if buffer != "" {
		result = append(result, buffer)
	}
	return result
}

func TokenizeStmtBlock(b *SourceCodeStmtBlock) (TokenStmtBlock, error) {
	var body []TokenStmtBlock
	var header []string
	// 这里假设我们需要对输入的 StrArrStmtBlock 的 Header 进行一些处理
	// 例如，将 Header 中的元素转换为大写
	header = append(header, splitString(b.Header)...)
	// 这里假设我们需要对输入的 StrArrStmtBlock 的 Body 进行一些处理
	// 例如，递归调用 ParseStmtBlock 处理 Body 中的每个元素
	for _, subBlock := range b.Body {
		parsedSubBlock, err := TokenizeStmtBlock(&subBlock)
		if err != nil {
			return TokenStmtBlock{}, err
		}
		body = append(body, parsedSubBlock)
	}
	return TokenStmtBlock{
		Header: header,
		Body:   body,
	}, nil
}
