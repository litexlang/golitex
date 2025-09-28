// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Litex email: <litexlang@outlook.com>
// Litex website: https://litexlang.com
// Litex github repository: https://github.com/litexlang/golitex
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

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
	if start+1 < len(line) && line[start:start+1] == glob.InlineCommentSig {
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
	start := 0
	for start < len(line) {
		token, next, err := t.nextToken(line, start)
		if err != nil {
			return nil, err
		}
		if token != "" {
			tokens = append(tokens, token)
		}
		start = next
	}
	return tokens, nil
}

func lineNum(l int) int {
	return l + 1
}

func (t *tokenizerWithScope) inlineCommentTokenBlock(line string) *tokenBlock {
	if strings.HasPrefix(line, glob.LatexSig) {
		return newTokenBlock(strSliceCursor{0, []string{glob.LatexSig, strings.TrimSpace(strings.TrimPrefix(line, glob.LatexSig))}}, nil, uint(t.currentLine))
	} else {
		return newTokenBlock(strSliceCursor{0, []string{glob.InlineCommentSig, strings.TrimSpace(strings.TrimPrefix(line, glob.InlineCommentSig))}}, nil, uint(t.currentLine))
	}
}

// skipCommentsAndEmptyLines 跳过注释和空行，返回是否应该继续处理当前行
// 返回值：true 表示跳过当前行，false 表示继续处理当前行
func (t *tokenizerWithScope) skipCommentsAndEmptyLines() (bool, *tokenBlock, error) {
	line := t.lines[t.currentLine]
	trimmed := strings.TrimSpace(line)

	// 跳过以 # 开头的行
	if strings.HasPrefix(trimmed, "#") {
		ret := t.inlineCommentTokenBlock(line)
		t.currentLine++
		return true, ret, nil
	}

	// 跳过以 """ 开头的多行注释块
	if strings.HasPrefix(trimmed, glob.MultiLinesCommentSig) {
		found := false
		lines := []string{}

		isLatexMultiLine := strings.HasPrefix(trimmed, glob.LatexMultiLineSig)

		for t.currentLine < len(t.lines) {
			t.currentLine++
			if t.currentLine >= len(t.lines) {
				return false, nil, fmt.Errorf("unclosed triple quote comment starting, line %d", lineNum(t.currentLine))
			}
			nextLine := t.lines[t.currentLine]
			nextTrimmed := strings.TrimSpace(nextLine)
			lines = append(lines, nextLine)
			if strings.HasPrefix(nextTrimmed, glob.MultiLinesCommentSig) {
				found = true
				t.currentLine++
				break
			}
		}
		if !found {
			return false, nil, fmt.Errorf("unclosed triple quote comment starting, line %d", lineNum(t.currentLine))
		}

		comment := strings.Join(lines, "\n")

		var ret *tokenBlock
		if isLatexMultiLine {
			ret = newTokenBlock(strSliceCursor{0, []string{glob.LatexMultiLineSig, comment}}, nil, uint(t.currentLine))
		} else {
			ret = newTokenBlock(strSliceCursor{0, []string{glob.MultiLinesCommentSig, comment}}, nil, uint(t.currentLine))
		}

		return true, ret, nil
	}

	// 跳过空行
	if trimmed == "" {
		t.currentLine++
		return true, nil, nil
	}

	return false, nil, nil
}

// removeInlineComment 移除行内注释（# 后面的内容）
func (t *tokenizerWithScope) removeInlineComment(line string) string {
	if idx := strings.Index(line, "#"); idx >= 0 {
		return line[:idx]
	}
	return line
}

// findFirstNonCommentLine 找到第一个非注释、非空行，返回处理后的行和缩进
// 用于确定子块的缩进级别
func (t *tokenizerWithScope) findFirstNonCommentLine(currentIndent int) (string, int, error) {
	for t.currentLine < len(t.lines) {
		nextLine := t.lines[t.currentLine]

		// 处理行内注释
		nextLine = t.removeInlineComment(nextLine)

		// 跳过空行
		if strings.TrimSpace(nextLine) == "" {
			t.currentLine++
			continue
		}

		// 跳过注释行
		if strings.HasPrefix(strings.TrimSpace(nextLine), "#") {
			t.currentLine++
			continue
		}

		// 跳过多行注释
		if strings.HasPrefix(strings.TrimSpace(nextLine), glob.MultiLinesCommentSig) {
			found := false
			for t.currentLine < len(t.lines) {
				t.currentLine++
				if t.currentLine >= len(t.lines) {
					return "", 0, fmt.Errorf("unclosed triple quote comment starting, line %d", lineNum(t.currentLine))
				}
				nextTrimmed := strings.TrimSpace(t.lines[t.currentLine])
				if strings.HasPrefix(nextTrimmed, glob.MultiLinesCommentSig) {
					found = true
					t.currentLine++
					break
				}
			}
			if !found {
				return "", 0, fmt.Errorf("unclosed triple quote comment starting, line %d", lineNum(t.currentLine))
			}
			continue
		}

		// 计算子行的缩进
		nextIndent := len(nextLine) - len(strings.TrimLeft(nextLine, " "))

		// 如果缩进没有更深，说明没有子块
		if nextIndent <= currentIndent {
			return "", 0, nil
		}

		return nextLine, nextIndent, nil
	}

	return "", currentIndent, nil
}

func (t *tokenizerWithScope) parseBlocks(currentIndent int) ([]tokenBlock, error) {
	blocks := []tokenBlock{}

	for t.currentLine < len(t.lines) {
		// 处理注释和空行
		shouldSkip, ret, err := t.skipCommentsAndEmptyLines()
		if err != nil {
			return nil, err
		}
		if shouldSkip {
			if ret != nil && currentIndent == 0 {
				blocks = append(blocks, *ret)
			}
			continue
		}

		// 重新获取当前行（因为可能已经跳过了注释行）
		line := t.lines[t.currentLine]

		// 计算当前行的缩进
		indent := len(line) - len(strings.TrimLeft(line, " "))

		// 如果缩进小于当前缩进，说明当前块结束
		if indent < currentIndent {
			return blocks, nil
		}

		// 如果缩进大于当前缩进，说明缩进错误
		if indent > currentIndent {
			return nil, fmt.Errorf("incorrect indentation:\n\"%s\"\nMaybe the previous nonempty line should end with \":\", line %d", line, lineNum(t.currentLine))
		}

		// 处理行内注释：截断 # 后面的内容
		lineForTokenize := t.removeInlineComment(line)

		// Tokenize 当前行
		tokens, err := t.tokenizeLine(lineForTokenize)
		if err != nil {
			return nil, err
		}

		// 创建 block
		block := newTokenBlock(strSliceCursor{0, tokens}, nil, uint(t.currentLine))
		t.currentLine++ // consume this line

		// 如果当前行以 : 结尾，需要解析子块
		if tokens[len(tokens)-1] == ":" {
			// 找到第一个非空、非注释的子行来确定缩进
			_, nextIndent, err := t.findFirstNonCommentLine(currentIndent)
			if err != nil {
				return nil, err
			}

			// 如果有更深的缩进，递归解析子块
			if nextIndent > currentIndent {
				subBlocks, err := t.parseBlocks(nextIndent)
				if err != nil {
					return nil, err
				}
				block.body = subBlocks
			}
		}

		blocks = append(blocks, *block)
	}

	return blocks, nil
}
