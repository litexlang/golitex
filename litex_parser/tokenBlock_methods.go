package litex_parser

import (
	"fmt"
	ast "golitex/litex_ast"
	"strings"
)

type TokenBlock struct {
	Header StrSliceCursor
	Body   []TokenBlock
}

func (b *TokenBlock) String() string {
	return b.stringWithIndent(0)
}

func (b *TokenBlock) stringWithIndent(indentLevel int) string {
	indent := strings.Repeat("  ", indentLevel) // 根据缩进级别生成缩进字符串
	result := fmt.Sprintf("%s%s\n", indent, strings.Join(b.Header.getSlice(), " "))

	// 递归处理子块
	if b.Body != nil {
		for _, subBlock := range b.Body {
			result += subBlock.stringWithIndent(indentLevel + 1)
		}
	}

	return result
}

type TopLevelStmtSlice struct {
	Body []strBlock
}

// strBlock 结构体表示一个语句块
type strBlock struct {
	Header string
	Body   []strBlock
}

const parseIndent = 4

// String 方法实现 fmt.Stringer 接口
func (b *strBlock) String() string {
	return b.stringWithIndent(0)
}

// stringWithIndent 递归生成带缩进的字符串表示
func (b *strBlock) stringWithIndent(indentLevel int) string {
	indent := strings.Repeat("  ", indentLevel) // 根据缩进级别生成缩进字符串
	result := fmt.Sprintf("%s%s\n", indent, b.Header)

	// 递归处理子块
	for _, subBlock := range b.Body {
		result += subBlock.stringWithIndent(indentLevel + 1)
	}

	return result
}

func splitAndReplaceSemicolons(input string) []string {
	// 按行分割字符串
	lines := strings.Split(input, "\n")

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

// func getTopLevelStmtSlice(content string) (*TopLevelStmtSlice, error) {
// 	lines := splitAndReplaceSemicolons(content)
// 	blocks, _, err := parseStrBlocks(lines, 0, 0)
// 	if err != nil {
// 		return nil, err
// 	}

// 	return &TopLevelStmtSlice{blocks}, err
// }

func getTopLevelStmtSlice(lines []string) (*TopLevelStmtSlice, error) {
	blocks, _, err := parseStrBlocks(lines, 0, 0)
	if err != nil {
		return nil, err
	}

	return &TopLevelStmtSlice{blocks}, err
}

func parseStrBlocks(lines []string, currentIndent int, startIndex int) ([]strBlock, int, error) {
	blocks := []strBlock{}
	i := startIndex

	for i < len(lines) {
		line := (lines)[i]
		trimLine := strings.TrimSpace(line)

		// 跳过空行
		if trimLine == "" {
			i++
			continue
		}

		// 跳过单行注释
		if strings.HasPrefix(trimLine, "//") {
			i++
			continue
		}

		// 跳过多行注释
		if strings.HasPrefix(trimLine, "/*") {
			// 找到 */，可能跨越多行
			j := i + 1
			for j < len((lines)) {
				if strings.Contains((lines)[j], "*/") {
					if !strings.HasSuffix(strings.TrimSpace((lines)[j]), "*/") {
						return nil, 0, fmt.Errorf("invalid line: a line with */ should end with */:\n%s", (lines)[j])
					}
					break
				}
				j++
			}
			i = j + 1
			continue
		}

		indent := len(line) - len(strings.TrimLeft(line, " "))

		// 如果当前行的缩进小于当前块的缩进，返回
		if indent < currentIndent {
			return blocks, i, nil
		}

		// 如果当前行的缩进等于当前块的缩进，创建一个新的块
		if indent == currentIndent {
			block := strBlock{
				Header: strings.TrimSpace(line),
				Body:   nil,
			}

			// 如果 trimLine 以 : 结尾，检查下一行的缩进
			if strings.HasSuffix(trimLine, ":") {
				i++
				// 找到下一个非空、非注释的行
				nextLineIndex := i
				for nextLineIndex < len((lines)) {
					nextLine := (lines)[nextLineIndex]
					nextTrimLine := strings.TrimSpace(nextLine)

					// 跳过空行和注释
					if nextTrimLine == "" || strings.HasPrefix(nextTrimLine, "//") {
						nextLineIndex++
						continue
					}

					// 处理多行注释 /* ... */
					if strings.HasPrefix(nextTrimLine, "/*") {
						// 找到注释的结束位置 */
						for nextLineIndex < len((lines)) {
							if strings.Contains((lines)[nextLineIndex], "*/") {
								if !strings.HasSuffix(strings.TrimSpace((lines)[nextLineIndex]), "*/") {
									return nil, 0, fmt.Errorf("invalid line: a line with */ should end with */:\n%s", (lines)[nextLineIndex])
								}
								nextLineIndex++
								break
							}
							nextLineIndex++
						}
						continue
					}

					// 检查下一行的缩进是否等于 currentIndent + parseIndent
					nextIndent := len(nextLine) - len(strings.TrimLeft(nextLine, " "))
					if nextIndent != currentIndent+parseIndent {
						return nil, i, fmt.Errorf("错误：'%s' 后的行缩进不正确，期望缩进 %d，实际缩进 %d", trimLine, currentIndent+parseIndent, nextIndent)
					}

					// 递归解析子块
					subBlocks, nextIndex, err := parseStrBlocks(lines, currentIndent+parseIndent, nextLineIndex)
					if err != nil {
						return nil, i, err
					}
					block.Body = subBlocks
					i = nextIndex
					break
				}

				// 如果没有找到有效的下一行，报错
				if nextLineIndex >= len(lines) {
					return nil, i, fmt.Errorf("错误：'%s' 后缺少缩进的子块", trimLine)
				}
			} else {
				// 否则，直接跳过该行
				i++
			}

			blocks = append(blocks, block)
		} else {
			// 如果缩进不符合预期，跳过该行
			i++
		}
	}

	return blocks, i, nil
}

func getUniParamsInUniFactRecursively(facts []ast.FactStmt, uniParamAtCurrentLevel []string) (map[string]struct{}, error) {
	uniParamsRecur := make(map[string]struct{})
	for _, domainFact := range facts {
		factAsConUni, ok := domainFact.(*ast.ConUniFactStmt)
		if ok {
			for key := range factAsConUni.UniParamsRecur {
				for _, curParam := range uniParamAtCurrentLevel {
					if curParam == key {
						return nil, fmt.Errorf("duplicate universal parameter in %v and current parameter slice %v", domainFact, uniParamAtCurrentLevel)
					}
				}
				uniParamsRecur[key] = struct{}{}
			}
			factAsConUni.UniParamsRecur = nil // 未来不再有用了，因为我只看最上层的
			continue
		}

		factAsGenUni, ok := domainFact.(*ast.ConUniFactStmt)
		if ok {
			for key := range factAsGenUni.UniParamsRecur {
				for _, curParam := range uniParamAtCurrentLevel {
					if curParam == key {
						return nil, fmt.Errorf("duplicate universal parameter in %v and current parameter slice %v", domainFact, uniParamAtCurrentLevel)
					}
				}
			}
			factAsGenUni.UniParamsRecur = nil // 未来不再有用了，因为我只看最上层的
			continue
		}
	}

	for _, paramAtCurLevel := range uniParamAtCurrentLevel {
		uniParamsRecur[paramAtCurLevel] = struct{}{}
	}

	return uniParamsRecur, nil
}
