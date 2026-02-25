// Copyright Jiachen Shen.
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
	glob "golitex/glob"
)

type AlgoIfAlgoReturnSlice []AlgoIfAlgoReturn

type AlgoIfAlgoReturn interface {
	algoIfAlgoReturn()
	String() string
	GetLine() uint
}

func (a *AlgoReturn) algoIfAlgoReturn() {}
func (a *AlgoIf) algoIfAlgoReturn()     {}

type AlgoReturn struct {
	Value Obj

	Line uint
}

type AlgoIf struct {
	Condition  SpecificFactStmt
	ReturnStmt *AlgoReturn

	Line uint
}

type DefAlgoStmt struct {
	FuncName string
	Params   StrSlice
	Stmts    AlgoIfAlgoReturnSlice

	Line uint
}

func (a *AlgoIf) String() string {
	return fmt.Sprintf("%s %s:\n%s", glob.KeywordIf, a.Condition.String(), glob.SplitLinesAndAdd4NIndents(a.ReturnStmt.String(), 1))
}

func (a *AlgoReturn) String() string {
	return fmt.Sprintf("%s %s", glob.KeywordReturn, a.Value.String())
}

func (a *AlgoReturn) GetLine() uint {
	return a.Line
}

func (a *AlgoIf) GetLine() uint {
	return a.Line
}

func (a *DefAlgoStmt) GetLine() uint {
	return a.Line
}
