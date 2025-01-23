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

type TokenStmt struct {
	Header []string
	Body   []TokenStmt
}

func (b *TokenStmt) String() string {
	return b.stringWithIndent(0)
}

func (b TokenStmt) stringWithIndent(indentLevel int) string {
	indent := strings.Repeat("  ", indentLevel) // 根据缩进级别生成缩进字符串
	result := fmt.Sprintf("%s%s\n", indent, strings.Join(b.Header, " "))

	// 递归处理子块
	for _, subBlock := range b.Body {
		result += subBlock.stringWithIndent(indentLevel + 1)
	}

	return result
}

func splitString(inputString string) ([]string, error) {
	var result []string
	var buffer string
	for i, char := range inputString {

		// if the next 2 characters are //, skip until the end
		if (i+1) < len(inputString) && inputString[i:i+2] == "//" {
			break
		}

		// if the next 2 characters are /*, error
		if (i+1) < len(inputString) && inputString[i:i+2] == "/*" {
			return nil, fmt.Errorf("invalid syntax: nested comment block")
		}

		if _, ok := KeyChars[string(char)]; ok {
			if buffer != "" {
				result = append(result, buffer)
				buffer = ""
			}
			result = append(result, string(char))
		}

		if (char) == ' ' {
			if buffer != "" {
				result = append(result, buffer)
				buffer = ""
			}
		}
		buffer += string(char)
	}
	if buffer != "" {
		result = append(result, buffer)
	}
	return result, nil
}

func TokenizeStmtBlock(b *SourceCodeStmtBlock) (TokenStmt, error) {
	var body []TokenStmt
	var header []string

	// 这里假设我们需要对输入的 StrArrStmtBlock 的 Header 进行一些处理
	// 例如，将 Header 中的元素转换为大写
	headerToken, err := splitString(b.Header)
	if err != nil {
		return TokenStmt{}, err
	}
	header = append(header, headerToken...)

	// 这里假设我们需要对输入的 StrArrStmtBlock 的 Body 进行一些处理
	// 例如，递归调用 ParseStmtBlock 处理 Body 中的每个元素
	for _, subBlock := range b.Body {
		parsedSubBlock, err := TokenizeStmtBlock(&subBlock)
		if err != nil {
			return TokenStmt{}, err
		}
		body = append(body, parsedSubBlock)
	}
	return TokenStmt{
		Header: header,
		Body:   body,
	}, nil
}
