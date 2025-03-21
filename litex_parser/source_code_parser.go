package litexparser

import (
	"fmt"
	"strings"
)

type parseStmtErr struct {
	previous error
	stmt     TokenBlock
}

func (e *parseStmtErr) Error() string {
	curTok, err := e.stmt.Header.currentToken()
	if err != nil {
		return fmt.Sprintf("error at %s, column %d: %s", e.stmt.Header.String(), e.stmt.Header.getIndex(), e.previous.Error())
	} else {
		return fmt.Sprintf("error at %s, column %d, at '%s': %s", e.stmt.Header.String(), e.stmt.Header.getIndex(), curTok, e.previous.Error())
	}
}

func ParseSourceCode(codePtr *string) (*[]TopStmt, error) {
	// 解引用指针以获取实际的字符串内容
	code := *codePtr
	code = strings.ReplaceAll(code, "\t", "    ")

	slice, err := GetTopLevelStmtSlice(&code)
	if err != nil {
		return nil, err
	}

	blocks := []TokenBlock{}
	for _, strBlock := range slice.Body {
		block, err := TokenizeStmtBlock(&strBlock)
		if err != nil {
			return nil, err
		}
		blocks = append(blocks, *block)
	}

	ret := []TopStmt{}
	for _, block := range blocks {
		cur, err := block.ParseTopLevelStmt()
		if err != nil {
			return nil, err
		}
		ret = append(ret, *cur)
	}

	return &ret, nil
}
