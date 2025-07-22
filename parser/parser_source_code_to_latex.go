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
// Litex website: https://litexlang.org
// Litex github repository: https://github.com/litexlang/golitex
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_parser

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
	"strings"
)

func ParseSourceCode_WhenCompileToLatex(code string) ([]ast.Stmt, error) {
	// code, err := preprocessSourceCode(code)
	preprocessedCodeLines, err := preprocessSourceCodeWhenCompileToLatex(code)
	if err != nil {
		return []ast.Stmt{}, err
	}

	blocks, err := makeTokenBlocks_WhenCompileToLatex(preprocessedCodeLines)
	if err != nil {
		return nil, err
	}

	ret := []ast.Stmt{}
	for _, block := range blocks {
		cur, err := block.Stmt()
		if err != nil {
			return nil, err
		}
		ret = append(ret, cur)
	}

	return ret, nil
}

func makeTokenBlocks_WhenCompileToLatex(lines []string) ([]tokenBlock, error) {
	t := newTokenizerWithScope(lines)
	return t.parseBlocks_WhenCompileToLatex(0)
}

func (t *tokenizerWithScope) parseBlocks_WhenCompileToLatex(currentIndent int) ([]tokenBlock, error) {
	blocks := []tokenBlock{}

	for t.currentLine < len(t.lines) {
		line := t.lines[t.currentLine]

		if strings.HasPrefix(line, glob.CommentSig) {
			blocks = append(blocks, tokenBlock{
				header: strSliceCursor{0, []string{glob.CommentSig, strings.TrimSpace(strings.TrimPrefix(line, glob.CommentSig))}},
				body:   nil,
			})
			t.currentLine++
			continue
		}

		// 计算当前行的缩进
		indent := len(line) - len(strings.TrimLeft(line, " "))

		if indent < currentIndent {
			// 缩进减少，说明当前块结束
			return blocks, nil
		}

		if indent > currentIndent {
			return nil, fmt.Errorf("incorrect indentation:\n\"%s\"\nMaybe the previous nonempty line should end with \":\"", line)
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
			header: strSliceCursor{0, tokens},
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
				subBlocks, err := t.parseBlocks(nextIndent)
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

func preprocessSourceCodeWhenCompileToLatex(code string) ([]string, error) {
	processedCode := strings.ReplaceAll(code, "\t", glob.Scope4Indents)
	lines := strings.Split(processedCode, "\n")
	lines = preprocessCommentsWhenCompileToLatex(lines)
	return lines, nil
}

const CommentSigPlusCommentSig = glob.CommentSig + glob.CommentSig
const MultiLinesCommentSigPlusCommentSig = glob.MultiLinesCommentSig + glob.CommentSig

func preprocessCommentsWhenCompileToLatex(lines []string) []string {
	ret := []string{}
	for i := 0; i < len(lines); i++ {
		if len(lines[i]) == 0 {
			continue
		}

		// 如果是 """ 开头的行，说明是注释块，直接跳过好多行，直到"""再次出现的那一行
		if strings.HasPrefix(strings.TrimSpace(lines[i]), glob.MultiLinesCommentSig) {
			if strings.HasPrefix(strings.TrimSpace(lines[i]), MultiLinesCommentSigPlusCommentSig) {
				i++ // 跳过开始阶段的 """
				var builder strings.Builder
				builder.WriteString(glob.CommentSig)

				for i < len(lines) && !strings.HasPrefix(strings.TrimSpace(lines[i]), glob.MultiLinesCommentSig) {
					builder.WriteString(lines[i])
					builder.WriteString("\n")
					i++
				}

				ret = append(ret, builder.String())

				continue
			} else {
				i++ // 跳过开始阶段的 """
				for i < len(lines) && !strings.HasPrefix(strings.TrimSpace(lines[i]), glob.MultiLinesCommentSig) {
					i++
				}
				continue // 这时候跳到for的i++环节，i++把“”“跳过了
			}
		}

		if strings.HasPrefix(strings.TrimSpace(lines[i]), CommentSigPlusCommentSig) {
			ret = append(ret, strings.TrimPrefix(strings.TrimSpace(lines[i]), glob.CommentSig))
			continue
		}

		// 移除行内注释
		if idx := strings.Index(lines[i], glob.CommentSig); idx >= 0 {
			lines[i] = lines[i][:idx]
		}
		// 移除行末的空白字符
		lines[i] = strings.TrimRight(lines[i], " \t\r\n")
		if lines[i] == "" {
			continue // 跳过纯注释行
		}
		ret = append(ret, lines[i])
	}
	return ret
}
