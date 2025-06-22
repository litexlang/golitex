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

// ----------------------------------------
// tokenBlockErr
// ----------------------------------------

type tokenBlockErr struct {
	previous error
	stmt     tokenBlock
}

func (e *tokenBlockErr) Error() string {
	var source, tokenInfo string

	source = e.stmt.String()

	// 尝试获取当前token（失败不影响主要错误信息）
	if curTok, err := e.stmt.header.currentToken(); err == nil {
		tokenInfo = fmt.Sprintf(" at '%s'", curTok)
	}

	if e.previous == nil {
		return fmt.Sprintf("parse error:\n%s\n%s",
			source,
			tokenInfo)
	} else {
		return fmt.Sprintf("parse error:\n%s\n%s\n%s",
			source,
			tokenInfo,
			e.previous.Error())
	}
}
