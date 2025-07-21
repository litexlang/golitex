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
	ast "golitex/ast"
	glob "golitex/glob"
	"strings"
)

func ParseSourceCodeToLatex(code string) ([]ast.Stmt, error) {
	// code, err := preprocessSourceCode(code)
	preprocessedCodeLines, err := preprocessSourceCodeWhenCompileToLatex(code)
	if err != nil {
		return []ast.Stmt{}, err
	}

	blocks, err := makeTokenBlocks(preprocessedCodeLines)
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

func preprocessSourceCodeWhenCompileToLatex(code string) ([]string, error) {
	processedCode := strings.ReplaceAll(code, "\t", glob.Scope4Indents)
	lines := strings.Split(processedCode, "\n")
	lines = preprocessCommentsWhenCompileToLatex(lines)
	return lines, nil
}

func preprocessCommentsWhenCompileToLatex(lines []string) []string {
	ret := []string{}
	for i := 0; i < len(lines); i++ {
		// 如果是 """ 开头的行，说明是注释块，直接跳过好多行，直到"""再次出现的那一行
		if strings.HasPrefix(strings.TrimSpace(lines[i]), glob.MultiLinesCommentSig) {
			i++ // 跳过开始阶段的 """

			var builder strings.Builder
			builder.WriteString(glob.CommentSig)

			for i < len(lines) && !strings.HasPrefix(strings.TrimSpace(lines[i]), glob.MultiLinesCommentSig) {
				builder.WriteString(lines[i])
				builder.WriteString("\n")
				i++
			}

			ret = append(ret, builder.String())

			continue // 这时候跳到for的i++环节，i++把“”“跳过了
		}

		if strings.HasPrefix(strings.TrimSpace(lines[i]), glob.CommentSig) {
			ret = append(ret, strings.TrimSpace(lines[i]))
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
