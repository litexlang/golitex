package litex_parser

import (
	"fmt"
	glob "golitex/litex_global"
)

// ----------------------------------------
// strSliceErr
// ----------------------------------------

type strSliceErr struct {
	previous error
	parser   *strSliceCursor
}

func (e *strSliceErr) Error() string {
	curTok, err := e.parser.currentToken()
	if err != nil {
		return fmt.Sprintf("error at %s, column %d: %s", e.parser.String(), e.parser.getIndex(), e.previous.Error())
	} else {
		return fmt.Sprintf("error at %s, column %d, at '%s': %s", e.parser.String(), e.parser.getIndex(), curTok, e.previous.Error())
	}
}

// ----------------------------------------
// tokenBlockErr
// ----------------------------------------

type tokenBlockErr struct {
	previous error
	stmt     tokenBlock
}

func (e *tokenBlockErr) Error() string {
	var source, position, tokenInfo string

	source = e.stmt.header.String()
	position = fmt.Sprintf("column %d", e.stmt.header.getIndex())

	// 尝试获取当前token（失败不影响主要错误信息）
	if curTok, err := e.stmt.header.currentToken(); err == nil {
		tokenInfo = fmt.Sprintf(" at '%s'", curTok)
	}

	if e.previous == nil {
		return fmt.Sprintf("parse error at %s, %s%s",
			source,
			position,
			tokenInfo)
	} else {
		return fmt.Sprintf("parse error at %s, %s%s: %v",
			source,
			position,
			tokenInfo,
			e.previous)
	}
}

func uniDomFactMoreThanOneLayerUniFactErrMsg(err error, curStmt *tokenBlock) error {
	startStr := curStmt.header.strAtIndex(0)
	if startStr == glob.KeywordForall {
		return &tokenBlockErr{fmt.Errorf("dom fact in universal fact should not be a universal fact with a universal fact as dom fact"), *curStmt}
	}

	return &tokenBlockErr{err, *curStmt}
}

func thenFactMustSpecMsg(curStmt *tokenBlock, err error) error {
	startStr := curStmt.header.strAtIndex(0)
	if startStr == glob.KeywordForall {
		return &tokenBlockErr{fmt.Errorf("then fact in universal fact should only be specific fact and can not be universal fact which starts with %s", glob.KeywordForall), *curStmt}
	}
	if startStr == glob.KeywordWhen {
		return &tokenBlockErr{fmt.Errorf("then fact in universal fact should only be specific fact and can not be conditional fact which starts with %s", glob.KeywordWhen), *curStmt}
	}
	return &tokenBlockErr{err, *curStmt}
}
