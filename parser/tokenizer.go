package parser

import (
	"fmt"
)

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
	result := []string{}
	buffer := ""
	for i := 0; i < len(inputString); {
		token, nextIndex, err := nextToken(inputString, i)
		if err != nil {
			return &result, err
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

func TokenizeStmtBlock(b *StrBlock) (*tokenBlock, error) {
	body := []tokenBlock{}
	var header []string = []string{}

	// 这里假设我们需要对输入的 StrArrStmtBlock 的 Header 进行一些处理
	// 例如，将 Header 中的元素转换为大写
	headerPtr, err := tokenizeString(b.Header)
	header = *headerPtr

	if err != nil || header == nil {
		return nil, err
	}

	// 这里假设我们需要对输入的 StrArrStmtBlock 的 Body 进行一些处理
	// 例如，递归调用 ParseStmtBlock 处理 Body 中的每个元素
	for _, subBlock := range b.Body {
		parsedSubBlock, err := TokenizeStmtBlock(&subBlock)
		if err != nil {
			return nil, err
		}
		body = append(body, *parsedSubBlock)
	}
	return &tokenBlock{
		Header: Parser{0, header},
		Body:   body,
	}, nil
}
