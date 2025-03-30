package litexparser

import (
	"fmt"
	glob "golitex/litex_globals"
)

// tokenizer 结构体封装了 inputString 和 start
type tokenizer struct {
	inputString *string // 使用指针以提高性能
	start       int
}

// newTokenizer 创建一个新的 tokenizer 实例
func newTokenizer(inputString *string) *tokenizer {
	return &tokenizer{
		inputString: inputString,
		start:       0,
	}
}

// nextToken 方法用于识别下一个 token
func (t *tokenizer) nextToken() (string, int, error) {
	input := *t.inputString // 解引用指针
	// 如果下两个字符是 //，跳过直到结束
	if t.start+1 < len(input) && input[t.start:t.start+2] == "//" {
		return "", len(input), nil
	}
	// 如果下两个字符是 /*，报错
	if t.start+1 < len(input) && input[t.start:t.start+2] == "/*" {
		return "", 0, fmt.Errorf("invalid syntax: nested comment block")
	}

	potentialKeywordSymbol := glob.GetBuiltinSymbol(input, t.start)
	if potentialKeywordSymbol != "" {
		return potentialKeywordSymbol, t.start + len(potentialKeywordSymbol), nil
	}

	if input[t.start] == ' ' {
		return "", t.start + 1, nil
	}

	buffer := ""
	for i := t.start; i < len(input); i++ {
		if glob.GetBuiltinSymbol(input, i) != "" || input[i] == ' ' {
			break
		}
		buffer += string(input[i])
	}
	return buffer, t.start + len(buffer), nil
}

// tokenizeString 方法用于将输入字符串 tokenize
func (t *tokenizer) tokenizeString() (*[]string, error) {
	input := *t.inputString // 解引用指针
	result := []string{}
	buffer := ""
	for t.start < len(input) {
		token, nextIndex, err := t.nextToken()
		if err != nil {
			return &result, err
		}
		if token == "" {
			if buffer != "" {
				result = append(result, buffer)
				buffer = ""
			}
		} else if glob.GetBuiltinSymbol(input, t.start) != "" {
			if buffer != "" {
				result = append(result, buffer)
				buffer = ""
			}
			result = append(result, token)
		} else {
			buffer = token
		}
		t.start = nextIndex
	}
	if buffer != "" {
		result = append(result, buffer)
	}
	return &result, nil
}

// TokenizeStmtBlock 函数保持不变
func TokenizeStmtBlock(b *strBlock) (*TokenBlock, error) {
	body := []TokenBlock{}

	// 创建一个新的 tokenizer 实例
	curTokenizer := newTokenizer(&b.Header) // 传递字符串的指针
	headerPtr, err := curTokenizer.tokenizeString()
	header := *headerPtr

	if err != nil || header == nil {
		return nil, err
	}

	// 处理 Body 中的每个元素
	for _, subBlock := range b.Body {
		parsedSubBlock, err := TokenizeStmtBlock(&subBlock)
		if err != nil {
			return nil, err
		}
		body = append(body, *parsedSubBlock)
	}
	return &TokenBlock{
		Header: Parser{0, header},
		Body:   body,
	}, nil
}
