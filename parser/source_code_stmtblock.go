package parser

import (
	"fmt"
	"os"
	"strings"
)

const parseIndent = 4

// SourceCodeStmtBlock 结构体表示一个语句块
type SourceCodeStmtBlock struct {
	Header string
	Body   []SourceCodeStmtBlock
}

// String 方法实现 fmt.Stringer 接口
func (b *SourceCodeStmtBlock) String() string {
	return b.stringWithIndent(0)
}

// stringWithIndent 递归生成带缩进的字符串表示
func (b *SourceCodeStmtBlock) stringWithIndent(indentLevel int) string {
	indent := strings.Repeat("  ", indentLevel) // 根据缩进级别生成缩进字符串
	result := fmt.Sprintf("%s%s\n", indent, b.Header)

	// 递归处理子块
	for _, subBlock := range b.Body {
		result += subBlock.stringWithIndent(indentLevel + 1)
	}

	return result
}

// ParseFile 读取文件并解析为 StmtBlock 结构
func ParseFile(filePath string) (*SourceCodeStmtBlock, error) {
	content, err := os.ReadFile(filePath)
	if err != nil {
		return nil, fmt.Errorf("无法读取文件: %v", err)
	}

	lines := strings.Split((string(content)), "\n")

	blocks, _, _ := parseStmtBlocks(lines, 0, 0)
	return &SourceCodeStmtBlock{"", blocks}, nil
}

func ParseString(content string) ([]SourceCodeStmtBlock, error) {
	lines := strings.Split((content), "\n")
	blocks, _, _ := parseStmtBlocks(lines, 0, 0)
	return blocks, nil
}

func parseStmtBlocks(lines []string, currentIndent int, startIndex int) ([]SourceCodeStmtBlock, int, error) {
	var blocks []SourceCodeStmtBlock
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
				if strings.HasSuffix(trimLine, "*/") {
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
			block := SourceCodeStmtBlock{
				Header: strings.TrimSpace(line),
				Body:   []SourceCodeStmtBlock{},
			}

			// 如果 trimLine 以 : 结尾，检查下一行的缩进
			if strings.HasSuffix(trimLine, ":") {
				i++
				if i >= len(lines) {
					return nil, i, fmt.Errorf("错误：'%s' 后缺少缩进的子块", trimLine)
				}

				nextLine := lines[i]
				nextIndent := len(nextLine) - len(strings.TrimLeft(nextLine, " "))

				// 检查下一行的缩进是否等于 currentIndent + parseIndent
				if nextIndent != currentIndent+parseIndent {
					return nil, i, fmt.Errorf("错误：'%s' 后的行缩进不正确，期望缩进 %d，实际缩进 %d", trimLine, currentIndent+parseIndent, nextIndent)
				}

				// 递归解析子块
				subBlocks, nextIndex, err := parseStmtBlocks(lines, currentIndent+parseIndent, i)
				if err != nil {
					return nil, i, err
				}
				block.Body = subBlocks
				i = nextIndex
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
