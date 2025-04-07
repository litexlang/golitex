package litexparser

import (
	ast "golitex/litex_ast"
)

func ParseSourceCode(code string) ([]ast.TopStmt, error) {
	// // 解引用指针以获取实际的字符串内容
	// code = strings.ReplaceAll(code, "\t", "    ")

	slice, err := getTopLevelStmtSlice(code)
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
