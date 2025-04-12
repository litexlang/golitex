package litex_parser

import (
	"fmt"
)

type strSliceErr struct {
	previous error
	parser   *strSliceCursor
}

type tokenBlockErr struct {
	previous error
	stmt     tokenBlock
}

func (e *strSliceErr) Error() string {
	curTok, err := e.parser.currentToken()
	if err != nil {
		return fmt.Sprintf("error at %s, column %d: %s", e.parser.String(), e.parser.getIndex(), e.previous.Error())
	} else {
		return fmt.Sprintf("error at %s, column %d, at '%s': %s", e.parser.String(), e.parser.getIndex(), curTok, e.previous.Error())
	}
}

func (e *tokenBlockErr) Error() string {

	// 安全获取基础位置信息
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
