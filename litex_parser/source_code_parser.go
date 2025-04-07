package litexparser

import (
	"fmt"
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
