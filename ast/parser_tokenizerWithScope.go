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

package litex_ast

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
	if start >= len(line) {
		return "", len(line), nil
	}

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

	// 提取 token - 使用 rune 来正确处理 Unicode 字符
	// 将字符串转换为 rune 来处理多字节字符
	runes := []rune(line)

	// 计算 start 字节位置对应的 rune 位置
	runeStart := 0
	byteCount := 0
	for i, r := range runes {
		if byteCount >= start {
			runeStart = i
			break
		}
		byteCount += len(string(r))
	}

	buffer := ""
	for i := runeStart; i < len(runes); i++ {
		r := runes[i]
		// 计算当前位置的字节位置用于检查符号
		currentBytePos := len(string(runes[:i]))

		// 检查是否是符号
		if glob.GetKeySymbol(line, currentBytePos) != "" {
			break
		}
		// 检查是否是空格
		if r == ' ' {
			break
		}
		buffer += string(r)
	}

	// 计算返回的字节位置
	byteEnd := len(string(runes[:runeStart+len([]rune(buffer))]))
	return buffer, byteEnd, nil
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

// skipCommentsAndEmptyLines 跳过注释和空行，返回是否应该继续处理当前行
// 返回值：true 表示跳过当前行，false 表示继续处理当前行
func (t *tokenizerWithScope) skipCommentsAndEmptyLines() (bool, *tokenBlock, error) {
	line := t.lines[t.currentLine]
	trimmed := strings.TrimSpace(line)

	// 跳过以 # 开头的单行注释（不创建 block，直接跳过）
	if strings.HasPrefix(trimmed, "#") {
		t.currentLine++
		return true, nil, nil
	}

	// 跳过以 """ 开头的多行注释块（不创建 block，直接跳过）
	if strings.HasPrefix(trimmed, glob.MultiLinesCommentSig) {
		commentStartLine := t.currentLine // 保存注释开始的行号
		found := false

		for t.currentLine < len(t.lines) {
			t.currentLine++
			if t.currentLine >= len(t.lines) {
				return false, nil, fmt.Errorf("unclosed triple quote comment starting, line %d", lineNum(commentStartLine))
			}
			nextLine := t.lines[t.currentLine]
			nextTrimmed := strings.TrimSpace(nextLine)
			if strings.HasPrefix(nextTrimmed, glob.MultiLinesCommentSig) {
				found = true
				t.currentLine++
				break
			}
		}
		if !found {
			return false, nil, fmt.Errorf("unclosed triple quote comment starting, line %d", lineNum(commentStartLine))
		}

		return true, nil, nil
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
			commentStartLine := t.currentLine // 保存注释开始的行号
			found := false
			for t.currentLine < len(t.lines) {
				t.currentLine++
				if t.currentLine >= len(t.lines) {
					return "", 0, fmt.Errorf("unclosed triple quote comment starting, line %d", lineNum(commentStartLine))
				}
				nextTrimmed := strings.TrimSpace(t.lines[t.currentLine])
				if strings.HasPrefix(nextTrimmed, glob.MultiLinesCommentSig) {
					found = true
					t.currentLine++
					break
				}
			}
			if !found {
				return "", 0, fmt.Errorf("unclosed triple quote comment starting, line %d", lineNum(commentStartLine))
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

// mergeContinuationLines 合并续行（以 \\ 结尾的行）
// 返回合并后的行和消耗的行数
func (t *tokenizerWithScope) mergeContinuationLines(startLine int) (string, int, error) {
	if startLine >= len(t.lines) {
		return "", 0, nil
	}

	mergedLine := t.lines[startLine]
	linesConsumed := 1

	// 检查当前行是否以续行符结尾
	for {
		// 移除行内注释后再检查续行符
		lineForCheck := t.removeInlineComment(mergedLine)
		trimmed := strings.TrimRight(lineForCheck, " \t")

		// 检查是否以单个反斜杠结尾（续行符）
		// 注意：在源代码中，用户写的是 \\，但实际存储的是一个反斜杠字符 \
		if strings.HasSuffix(trimmed, "\\") && (len(trimmed) == 1 || trimmed[len(trimmed)-2] != '\\') {
			// 移除续行符和后面的空格
			// 找到续行符的位置（在移除注释后的行中）
			lineForCheckTrimmed := strings.TrimRight(mergedLine, " \t")
			// 找到最后一个反斜杠的位置（应该是续行符）
			lastBackslashIndex := strings.LastIndex(lineForCheckTrimmed, "\\")
			if lastBackslashIndex >= 0 {
				// 移除续行符和后面的空格
				mergedLine = strings.TrimRight(mergedLine[:lastBackslashIndex], " \t")
			}

			// 检查是否有下一行
			if startLine+linesConsumed >= len(t.lines) {
				return "", 0, fmt.Errorf("line continuation at line %d has no following line", lineNum(startLine+linesConsumed-1))
			}

			// 获取下一行
			nextLine := t.lines[startLine+linesConsumed]
			// 移除下一行的前导空格（续行时，下一行的内容直接接在上一行后面）
			nextLineTrimmed := strings.TrimLeft(nextLine, " \t")

			// 合并行
			mergedLine = mergedLine + " " + nextLineTrimmed
			linesConsumed++

			// 继续检查合并后的行是否还有续行符
			continue
		}

		// 没有续行符，返回合并后的行
		break
	}

	return mergedLine, linesConsumed, nil
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
		// 合并续行
		line, linesConsumed, err := t.mergeContinuationLines(t.currentLine)
		if err != nil {
			return nil, err
		}

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

		// 创建 block（使用原始行号）
		block := newTokenBlock(strSliceCursor{0, tokens}, nil, uint(t.currentLine))
		t.currentLine += linesConsumed // consume merged lines

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
