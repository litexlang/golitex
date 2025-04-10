package litex_parser

import (
	"fmt"
	glob "golitex/litex_global"
	"strings"
)

// TokenBlock 表示一个 tokenized 的块
// type TokenBlock struct {
// 	Header StrSliceCursor
// 	Body   []TokenBlock
// }

// StrSliceCursor 表示字符串切片的游标
type StrSliceCursor struct {
	index int
	slice []string
}

// strBlock 表示一个未 tokenized 的块
type strBlock struct {
	Header string
	Body   []strBlock
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
func (t *tokenizerWithScope) parseBlocks(currentIndent int) ([]TokenBlock, error) {
	blocks := []TokenBlock{}
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

			block := TokenBlock{
				Header: StrSliceCursor{0, tokens},
				Body:   nil,
			}

			t.currentLine++

			// 如果以冒号结尾，解析子块
			if strings.HasSuffix(trimmed, ":") {
				subBlocks, err := t.parseBlocks(indent + 1)
				if err != nil {
					return nil, err
				}
				block.Body = subBlocks
			}

			blocks = append(blocks, block)
			continue
		}

		// 缩进不符合预期，跳过
		t.currentLine++
	}

	return blocks, nil
}

// makeTokenBlocks 合并 tokenization 和 scope 解析的入口函数
func makeTokenBlocks(lines []string) ([]TokenBlock, error) {
	t := newTokenizerWithScope(lines)
	return t.parseBlocks(0)
}
