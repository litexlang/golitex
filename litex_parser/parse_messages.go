package litex_parser

import (
	"fmt"
	glob "golitex/litex_global"
)

func thenFactMustSpecMsg(curStmt *tokenBlock, err error) error {
	startStr := curStmt.header.strAtIndex(0)
	if startStr == glob.KeywordForall {
		return &parseTimeErr{fmt.Errorf("then fact in universal fact should only be specific fact and can not be universal fact which starts with %s", glob.KeywordForall), *curStmt}
	}
	if startStr == glob.KeywordWhen {
		return &parseTimeErr{fmt.Errorf("then fact in universal fact should only be specific fact and can not be conditional fact which starts with %s", glob.KeywordWhen), *curStmt}
	}
	return &parseTimeErr{err, *curStmt}
}

func uniDomFactMoreThanOneLayerUniFactErrMsg(err error, curStmt *tokenBlock) error {
	startStr := curStmt.header.strAtIndex(0)
	if startStr == glob.KeywordForall {
		return &parseTimeErr{fmt.Errorf("dom fact in universal fact should only be a universal fact with a universal fact as dom fact"), *curStmt}
	}

	return &parseTimeErr{err, *curStmt}
}
