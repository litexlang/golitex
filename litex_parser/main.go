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
		return []ast.TopStmt{}, nil
	}

	slice, err := chunkStr(preprocessedCodeLines)
	if err != nil {
		return nil, err
	}

	blocks := []TokenBlock{}
	for _, strBlock := range slice.Body {
		block, err := tokenizeStmtBlock(&strBlock)
		if err != nil {
			return nil, err
		}
		blocks = append(blocks, *block)
	}

	ret := []ast.TopStmt{}
	for _, block := range blocks {
		cur, err := block.TopLevelStmt()
		if err != nil {
			return nil, err
		}
		ret = append(ret, *cur)
	}

	return ret, nil
}

func preprocessSourceCode(code string) ([]string, error) {
	processedCode := strings.ReplaceAll(code, "\t", glob.ScopeIndent)
	lines := splitAndReplaceSemicolons(processedCode)
	return lines, nil
}
