package parser

import (
	"fmt"
	"strings"
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

// 提取出的 nextToken 函数，用于识别下一个 token
func nextToken(inputString string, start int) (string, int, error) {
	// 如果下两个字符是 //，跳过直到结束
	if start+1 < len(inputString) && inputString[start:start+2] == "//" {
		return "", len(inputString), nil
	}
	// 如果下两个字符是 /*，报错
	if start+1 < len(inputString) && inputString[start:start+2] == "/*" {
		return "", 0, fmt.Errorf("invalid syntax: nested comment block")
	}

	potentialKeywordSymbol := getKeywordSymbol(inputString, start)
	if potentialKeywordSymbol != "" {
		return potentialKeywordSymbol, start + len(potentialKeywordSymbol), nil
	}

	if inputString[start] == ' ' {
		return "", start + 1, nil
	}

	buffer := ""
	for i := start; i < len(inputString); i++ {
		if getKeywordSymbol(inputString, i) != "" || inputString[i] == ' ' {
			break
		}
		buffer += string(inputString[i])
	}
	return buffer, start + len(buffer), nil
}

func tokenizeString(inputString string) (*[]string, error) {
	var result []string
	var buffer string
	for i := 0; i < len(inputString); {
		token, nextIndex, err := nextToken(inputString, i)
		if err != nil {
			return nil, err
		}
		if token == "" {
			if buffer != "" {
				result = append(result, buffer)
				buffer = ""
			}
		} else if getKeywordSymbol(inputString, i) != "" {
			if buffer != "" {
				result = append(result, buffer)
				buffer = ""
			}
			result = append(result, token)
		} else {
			buffer = token
		}
		i = nextIndex
	}
	if buffer != "" {
		result = append(result, buffer)
	}
	return &result, nil
}

func TokenizeStmtBlock(b *SourceCodeStmtBlock) (*TokenStmt, error) {
	var body []TokenStmt
	var header *[]string

	// 这里假设我们需要对输入的 StrArrStmtBlock 的 Header 进行一些处理
	// 例如，将 Header 中的元素转换为大写
	header, err := tokenizeString(b.Header)
	if err != nil {
		return nil, err
	}

	// 这里假设我们需要对输入的 StrArrStmtBlock 的 Body 进行一些处理
	// 例如，递归调用 ParseStmtBlock 处理 Body 中的每个元素
	if b.Body != nil {
		for _, subBlock := range *b.Body {
			parsedSubBlock, err := TokenizeStmtBlock(&subBlock)
			if err != nil {
				return nil, err
			}
			body = append(body, *parsedSubBlock)
		}
	}
	return &TokenStmt{
		Header: *header,
		Body:   body,
	}, nil
}
