package litex_parser

import (
	"fmt"
	glob "golitex/litex_global"
)

func thenFactMustSpecMsg(curStmt *TokenBlock, err error) error {
	startStr := curStmt.Header.strAtIndex(0)
	if startStr == glob.KeywordForall {
		return &parseTimeErr{fmt.Errorf("then fact in universal fact should only be specific fact and can not be universal fact which starts with %s", glob.KeywordForall), *curStmt}
	}
	if startStr == glob.KeywordWhen {
		return &parseTimeErr{fmt.Errorf("then fact in universal fact should only be specific fact and can not be conditional fact which starts with %s", glob.KeywordWhen), *curStmt}
	}
	return &parseTimeErr{err, *curStmt}
}
