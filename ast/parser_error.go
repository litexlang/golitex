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

// 工作原理是：如果error回传的时候，某一步已经把现在的故障出现在第几行写好了，那么就返回这个error，否则就新开一个error，并把现在的故障出现在第几行写好
func ErrInLine(previousErr error, stmt *tokenBlock) *ParseErrAtLine {
	if _, ok := previousErr.(*ParseErrAtLine); ok {
		return previousErr.(*ParseErrAtLine)
	}

	return newErrAtLine(stmt.line, previousErr)
}

type ParseErrAtLine struct {
	line uint
	err  error
}

func newErrAtLine(line uint, err error) *ParseErrAtLine {
	return &ParseErrAtLine{
		line: line,
		err:  err,
	}
}

func (e *ParseErrAtLine) Error() string {
	return fmt.Sprintf("parse error at line %d:\n%s", e.line, e.err.Error())
}
