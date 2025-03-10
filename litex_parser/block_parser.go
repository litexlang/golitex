package litexparser

import (
	"fmt"
	"os"
	"strings"
)

type TokenBlock struct {
	Header Parser
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

// ParseFile 读取文件并解析为 StmtBlock 结构
func ParseFile(filePath string) (*TopLevelStmtSlice, error) {
	content, err := os.ReadFile(filePath)
	if err != nil {
		return nil, fmt.Errorf("无法读取文件: %v", err)
	}

	return GetTopLevelStmtSlice(string(content))
}

func GetTopLevelStmtSlice(content string) (*TopLevelStmtSlice, error) {
	lines := strings.Split((content), "\n")
	blocks, _, err := parseStrBlocks(lines, 0, 0)
	if err != nil {
		return nil, err
	}

	return &TopLevelStmtSlice{*blocks}, err
}

func parseStrBlocks(lines []string, currentIndent int, startIndex int) (*[]strBlock, int, error) {
	blocks := []strBlock{}
	i := startIndex

	for i < len(lines) {
		line := lines[i]
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
			for j < len(lines) {
				if strings.Contains(lines[j], "*/") {
					if !strings.HasSuffix(strings.TrimSpace(lines[j]), "*/") {
						return nil, 0, fmt.Errorf("invalid line: a line with */ should end with */:\n%s", lines[j])
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
			return &blocks, i, nil
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
				for nextLineIndex < len(lines) {
					nextLine := lines[nextLineIndex]
					nextTrimLine := strings.TrimSpace(nextLine)

					// 跳过空行和注释
					if nextTrimLine == "" || strings.HasPrefix(nextTrimLine, "//") {
						nextLineIndex++
						continue
					}

					// 处理多行注释 /* ... */
					if strings.HasPrefix(nextTrimLine, "/*") {
						// 找到注释的结束位置 */
						for nextLineIndex < len(lines) {
							if strings.Contains(lines[nextLineIndex], "*/") {
								if !strings.HasSuffix(strings.TrimSpace(lines[nextLineIndex]), "*/") {
									return nil, 0, fmt.Errorf("invalid line: a line with */ should end with */:\n%s", lines[nextLineIndex])
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
					block.Body = *subBlocks
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

	return &blocks, i, nil
}

func ParseSourceCodeGetTokenBlock(code string) (*[]TokenBlock, error) {
	lines := strings.Split(code, "\n")
	strBlocks, _, err := parseStrBlocks(lines, 0, 0)
	if err != nil {
		return nil, err
	}

	tokenBlocks := []TokenBlock{}
	for _, strBlock := range *strBlocks {
		block, err := TokenizeStmtBlock(&strBlock)
		if err != nil {
			return nil, err
		}
		tokenBlocks = append(tokenBlocks, *block)
	}

	return &tokenBlocks, nil
}
