// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Contact the development team: <litexlang@outlook.com>
// Visit litexlang.org and https://github.com/litexlang/golitex for more info.

package litex_parser

import (
	"fmt"
	glob "golitex/glob"
	"strings"
)

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
	if start+1 < len(line) && line[start:start+1] == glob.CommentSig {
		return "", len(line), nil
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

func (t *tokenizerWithScope) parseBlocks(currentIndent int, parserEnv *ParserEnv) ([]tokenBlock, error) {
	blocks := []tokenBlock{}

	for t.currentLine < len(t.lines) {
		line := t.lines[t.currentLine]

		// 计算当前行的缩进
		indent := len(line) - len(strings.TrimLeft(line, " "))

		if indent < currentIndent {
			// 缩进减少，说明当前块结束
			return blocks, nil
		}

		if indent > currentIndent {
			return nil, fmt.Errorf("incorrect indentation:\n\"%s\"", line)
		}

		// indent == currentIndent:
		// 判断是否为 header 行（是否以 : 结尾）
		lineForTokenize := line
		if strings.HasSuffix(line, ":") {
			lineForTokenize = line
		}

		tokens, err := t.tokenizeLine(lineForTokenize)
		if err != nil {
			return nil, err
		}

		block := tokenBlock{
			header: strSliceCursor{0, tokens, parserEnv},
			body:   nil,
		}

		t.currentLine++ // consume this line

		// 判断是否需要解析子 block
		if strings.HasSuffix(line, ":") {
			for t.currentLine < len(t.lines) {
				nextLine := t.lines[t.currentLine]

				// 同样先处理注释
				if idx := strings.Index(nextLine, "//"); idx >= 0 {
					nextLine = nextLine[:idx]
				}
				nextTrimmed := strings.TrimSpace(nextLine)

				// 跳过空行
				if nextTrimmed == "" {
					t.currentLine++
					continue
				}

				nextIndent := len(nextLine) - len(strings.TrimLeft(nextLine, " "))
				if nextIndent <= currentIndent {
					// 没有更深缩进，说明没有子块
					break
				}

				// 有子 block
				subBlocks, err := t.parseBlocks(nextIndent, parserEnv)
				if err != nil {
					return nil, err
				}
				block.body = subBlocks
				break
			}
		}

		blocks = append(blocks, block)
	}

	return blocks, nil
}
