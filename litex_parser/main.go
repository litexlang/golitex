package litex_parser

import (
	ast "golitex/litex_ast"
	glob "golitex/litex_global"
	"strings"
)

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
		ret = append(ret, *cur)
	}

	return ret, nil
}

func preprocessSourceCode(code string) ([]string, error) {
	processedCode := strings.ReplaceAll(code, "\t", glob.Scope4Indents)
	lines := splitAndReplaceSemicolons(processedCode)
	return lines, nil
}

func SetupAndParseSourceCode(code string) ([]ast.TopStmt, error) {
	return ParseSourceCode(code)
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
