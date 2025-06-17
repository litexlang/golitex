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
// Litex Zulip community: https://litex.zulipchat.com

package litex_parser

import (
	ast "golitex/ast"
	glob "golitex/glob"
	"strings"
)

// * TODO: 在parse时，把pkgName改成当前项目里定义的 pkgName，而不是继续沿用原来的
func ParseSourceCode(code string) ([]ast.TopStmt, error) {
	// code, err := preprocessSourceCode(code)
	preprocessedCodeLines, err := preprocessSourceCode(code)
	if err != nil {
		return []ast.TopStmt{}, err
	}

	blocks, err := makeTokenBlocks(preprocessedCodeLines)
	if err != nil {
		return nil, err
	}

	ret := []ast.TopStmt{}
	for _, block := range blocks {
		cur, err := block.TopStmt()
		if err != nil {
			return nil, err
		}
		if cur != nil { // cur 可能是nil，比如非执行型语句import返回就是nil，因为压根没有要执行的东西
			ret = append(ret, *cur)
		}
	}

	return ret, nil
}

func preprocessSourceCode(code string) ([]string, error) {
	processedCode := strings.ReplaceAll(code, "\t", glob.Scope4Indents)
	lines := splitAndReplaceSemicolons(processedCode)
	lines = preprocessComments(lines)
	return lines, nil
}

func preprocessComments(lines []string) []string {
	ret := []string{}
	for i := 0; i < len(lines); i++ {
		// 如果是 """ 开头的行，说明是注释块，直接跳过好多行，直到"""再次出现的那一行
		if strings.HasPrefix(strings.TrimSpace(lines[i]), glob.MultiLinesCommentSig) {
			i++ // 跳过开始阶段的 """
			for i < len(lines) && !strings.HasPrefix(strings.TrimSpace(lines[i]), glob.MultiLinesCommentSig) {
				i++
			}
			continue // 这时候跳到for的i++环节，i++把“”“跳过了
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

func splitAndReplaceSemicolons(input string) []string {
	// 按行分割字符串
	lines := strings.Split(input, "\n")
	if glob.PreprocessSemicolonAtParseTime {
		return preprocessReplaceSemicolons(lines)
	}
	return lines
}

func preprocessReplaceSemicolons(lines []string) []string {
	// 创建一个新的切片来存储处理后的行
	transformedLines := make([]string, 0, len(lines))

	// 遍历每一行
	for _, line := range lines {
		// 查找行头的空白字符
		indent := ""
		for _, char := range line {
			// if char == ' ' || char == '\t' {
			if char == ' ' {
				indent += string(char)
			} else {
				break
			}
		}

		// 如果行中包含 `;`，则进行替换
		if strings.Contains(line, ";") {
			// 将 `;` 和它后面的空白字符一起替换为 `\n` + 行头空白
			transformedLine := ""
			for i := 0; i < len(line); i++ {
				if line[i] == ';' {
					// 找到 `;`，替换为 `\n` + 行头空白
					transformedLine += "\n" + indent
					// 跳过 `;` 后面的空白字符
					for i+1 < len(line) && (line[i+1] == ' ' || line[i+1] == '\t') {
						i++
					}
				} else {
					// 如果不是 `;`，直接追加字符
					transformedLine += string(line[i])
				}
			}

			// 将替换后的行按换行符分割
			splitLines := strings.Split(transformedLine, "\n")
			// 将处理后的行添加到新的切片中
			transformedLines = append(transformedLines, splitLines...)
		} else {
			// 如果行中没有 `;`，直接添加到新的切片中
			transformedLines = append(transformedLines, line)
		}
	}

	// 返回新的切片的指针
	return transformedLines
}
