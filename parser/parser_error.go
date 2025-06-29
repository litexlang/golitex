// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Litex email: <litexlang@outlook.com>
// Litex website: https://litexlang.org
// Litex github repository: https://github.com/litexlang/golitex
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_parser

import (
	"fmt"
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

func tbErr(previousErr error, stmt *tokenBlock) error {
	tokenInfo := ""
	if curTok, err := stmt.header.currentToken(); err == nil {
		tokenInfo = fmt.Sprintf("at '%s'", curTok)
	}

	if previousErr == nil {
		return fmt.Errorf("parse error:\n%s\n%s", stmt.String(), tokenInfo)
	} else {
		return fmt.Errorf("parse error:\n%s\n%s\n%s", stmt.String(), tokenInfo, previousErr.Error())
	}
}
