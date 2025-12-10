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
// Litex website: https://litexlang.com
// Litex github repository: https://github.com/litexlang/golitex
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_ast

import (
	"fmt"
)

// TODO 最好能把函数名传过来，因为常常出现的消息的格式是
// parse error at end of line, line 1:
// a
// parse error at end of line, line 1:
// a
// parse error at end of line, line 1:
// a
func parserErrAtTb(previousErr error, stmt *tokenBlock) *errAtLine {
	if _, ok := previousErr.(*errAtLine); ok {
		return previousErr.(*errAtLine)
	}

	return newErrAtLine(stmt.line, previousErr)
}

type errAtLine struct {
	line uint
	err  error
}

func newErrAtLine(line uint, err error) *errAtLine {
	return &errAtLine{
		line: line,
		err:  err,
	}
}

func (e *errAtLine) Error() string {
	return fmt.Sprintf("parse error at line %d:\n%s", e.line, e.err.Error())
}
