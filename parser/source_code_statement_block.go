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
func (b SourceCodeStmtBlock) String() string {
	return b.stringWithIndent(0)
}

// stringWithIndent 递归生成带缩进的字符串表示
func (b SourceCodeStmtBlock) stringWithIndent(indentLevel int) string {
	indent := strings.Repeat("  ", indentLevel) // 根据缩进级别生成缩进字符串
	result := fmt.Sprintf("%s%s\n", indent, b.Header)

	// 递归处理子块
	for _, subBlock := range b.Body {
		result += subBlock.stringWithIndent(indentLevel + 1)
	}

	return result
}

// ParseFile 读取文件并解析为 StmtBlock 结构
func ParseFile(filePath string) ([]SourceCodeStmtBlock, error) {
	content, err := os.ReadFile(filePath)
	if err != nil {
		return nil, fmt.Errorf("无法读取文件: %v", err)
	}

	lines := strings.Split((string(content)), "\n")

	blocks, _ := parseStmtBlocks(lines, 0, 0)
	return blocks, nil
}

func ParseString(content string) ([]SourceCodeStmtBlock, error) {
	lines := strings.Split((content), "\n")
	blocks, _ := parseStmtBlocks(lines, 0, 0)
	return blocks, nil
}

func parseStmtBlocks(lines []string, currentIndent int, startIndex int) ([]SourceCodeStmtBlock, int) {

	var blocks []SourceCodeStmtBlock
	i := startIndex

	for i < len(lines) {
		line := lines[i]

		// Skip empty lines
		if strings.TrimSpace(line) == "" {
			i++
			continue
		}

		indent := len(line) - len(strings.TrimLeft(line, " "))

		// 如果当前行的缩进小于当前块的缩进，返回
		if indent < currentIndent {
			return blocks, i
		}

		// 如果当前行的缩进等于当前块的缩进，创建一个新的块
		if indent == currentIndent {
			block := SourceCodeStmtBlock{
				Header: strings.TrimSpace(line),
				Body:   []SourceCodeStmtBlock{},
			}

			// 递归解析子块
			i++
			subBlocks, nextIndex := parseStmtBlocks(lines, currentIndent+parseIndent, i)
			block.Body = subBlocks
			blocks = append(blocks, block)
			i = nextIndex
		} else {
			// 如果缩进不符合预期，跳过该行
			i++
		}
	}

	return blocks, i
}
