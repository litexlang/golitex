package litex_parser

import (
	"fmt"
	glob "golitex/litex_global"
	"strings"
)

// tokenizer 结构体封装了 inputString 和 start
type tokenizer struct {
	inputString string // 使用指针以提高性能
	start       int
}

// newTokenizer 创建一个新的 tokenizer 实例
func newTokenizer(inputString string) *tokenizer {
	return &tokenizer{
		inputString: inputString,
		start:       0,
	}
}

// nextToken 方法用于识别下一个 token
func (t *tokenizer) nextToken() (string, int, error) {
	// input := t.inputString // 解引用指针
	// 如果下两个字符是 //，跳过直到结束
	if t.start+1 < len(t.inputString) && t.inputString[t.start:t.start+2] == "//" {
		return "", len(t.inputString), nil
	}
	// 如果下两个字符是 /*，报错
	if t.start+1 < len(t.inputString) && t.inputString[t.start:t.start+2] == "/*" {
		return "", 0, fmt.Errorf("invalid syntax: nested comment block")
	}

	potentialKeywordSymbol := glob.GetKeySymbol(t.inputString, t.start)
	if potentialKeywordSymbol != "" {
		return potentialKeywordSymbol, t.start + len(potentialKeywordSymbol), nil
	}

	if t.inputString[t.start] == ' ' {
		return "", t.start + 1, nil
	}

	buffer := ""
	for i := t.start; i < len(t.inputString); i++ {
		if glob.GetKeySymbol(t.inputString, i) != "" || t.inputString[i] == ' ' {
			break
		}
		buffer += string(t.inputString[i])
	}
	return buffer, t.start + len(buffer), nil
}

// tokenizeString 方法用于将输入字符串 tokenize
func (t *tokenizer) tokenizeString() ([]string, error) {
	input := t.inputString // 解引用指针
	result := []string{}
	buffer := ""
	for t.start < len(input) {
		token, nextIndex, err := t.nextToken()
		if err != nil {
			return result, err
		}
		if token == "" {
			if buffer != "" {
				result = append(result, buffer)
				buffer = ""
			}
		} else if glob.GetKeySymbol(input, t.start) != "" {
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
	return result, nil
}

// strSliceCursor 表示字符串切片的游标
type strSliceCursor struct {
	index int
	slice []string
}

// tokenizerWithScope 合并 tokenization 和 scope 解析
type tokenizerWithScope struct {
	lines         []string // 所有行
	currentLine   int      // 当前行索引
	currentIndent int      // 当前缩进级别
}

// newTokenizerWithScope 创建一个新的 tokenizerWithScope 实例
func newTokenizerWithScope(lines []string) *tokenizerWithScope {
	return &tokenizerWithScope{
		lines:         lines,
		currentLine:   0,
		currentIndent: 0,
	}
}

// nextToken 返回当前行的下一个 token
func (t *tokenizerWithScope) nextToken(line string, start int) (string, int, error) {
	// 跳过注释
	if start+1 < len(line) && line[start:start+2] == "//" {
		return "", len(line), nil
	}
	if start+1 < len(line) && line[start:start+2] == "/*" {
		return "", 0, fmt.Errorf("invalid syntax: nested comment block")
	}

	// 检查关键字或符号
	if symbol := glob.GetKeySymbol(line, start); symbol != "" {
		return symbol, start + len(symbol), nil
	}

	// 跳过空格
	if line[start] == ' ' {
		return "", start + 1, nil
	}

	// 提取 token
	buffer := ""
	for i := start; i < len(line); i++ {
		if glob.GetKeySymbol(line, i) != "" || line[i] == ' ' {
			break
		}
		buffer += string(line[i])
	}
	return buffer, start + len(buffer), nil
}

// tokenizeLine 将一行 tokenize
func (t *tokenizerWithScope) tokenizeLine(line string) ([]string, error) {
	tokens := []string{}
	buffer := ""
	start := 0
	for start < len(line) {
		token, next, err := t.nextToken(line, start)
		if err != nil {
			return nil, err
		}
		if token == "" {
			if buffer != "" {
				tokens = append(tokens, buffer)
				buffer = ""
			}
		} else if glob.GetKeySymbol(line, start) != "" {
			if buffer != "" {
				tokens = append(tokens, buffer)
				buffer = ""
			}
			tokens = append(tokens, token)
		} else {
			buffer = token
		}
		start = next
	}
	if buffer != "" {
		tokens = append(tokens, buffer)
	}
	return tokens, nil
}

// parseBlocks 递归解析块结构
func (t *tokenizerWithScope) parseBlocks(currentIndent int) ([]tokenBlock, error) {
	blocks := []tokenBlock{}
	for t.currentLine < len(t.lines) {
		line := t.lines[t.currentLine]
		trimmed := strings.TrimSpace(line)

		// 跳过空行或注释
		if trimmed == "" || strings.HasPrefix(trimmed, "//") {
			t.currentLine++
			continue
		}
		if strings.HasPrefix(trimmed, "/*") {
			t.currentLine++
			for t.currentLine < len(t.lines) {
				if strings.Contains(t.lines[t.currentLine], "*/") {
					t.currentLine++
					break
				}
				t.currentLine++
			}
			continue
		}

		// 计算缩进
		indent := len(line) - len(strings.TrimLeft(line, " "))
		if indent < currentIndent {
			return blocks, nil
		}

		// 解析当前行
		if indent == currentIndent {
			tokens, err := t.tokenizeLine(trimmed)
			if err != nil {
				return nil, err
			}

			block := tokenBlock{
				header: strSliceCursor{0, tokens},
				body:   []tokenBlock{},
			}

			t.currentLine++

			// 如果以冒号结尾，解析子块
			if strings.HasSuffix(trimmed, ":") {
				// 检查下一行的缩进是否大于当前缩进
				if t.currentLine < len(t.lines) {
					nextLine := t.lines[t.currentLine]
					nextIndent := len(nextLine) - len(strings.TrimLeft(nextLine, " "))
					if nextIndent > currentIndent {
						subBlocks, err := t.parseBlocks(nextIndent)
						if err != nil {
							return nil, err
						}
						block.body = subBlocks
					}
				}
			}

			blocks = append(blocks, block)
			continue
		}

		// 缩进比当前多但不是以冒号结尾的行，跳过或报错？
		// 这里可以根据需求决定是跳过还是报错
		t.currentLine++
	}

	return blocks, nil
}

// makeTokenBlocks 合并 tokenization 和 scope 解析的入口函数
func makeTokenBlocks(lines []string) ([]tokenBlock, error) {
	t := newTokenizerWithScope(lines)
	return t.parseBlocks(0)
}
