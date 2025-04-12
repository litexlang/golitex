package litex_parser

import (
	"fmt"
	"strings"
)

type parseTimeErr struct {
	previous error
	stmt     tokenBlock
}

func (e *parseTimeErr) Error() string {

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

func (p *strSliceCursor) String() string {
	return strings.Join(p.slice, " ")
}
