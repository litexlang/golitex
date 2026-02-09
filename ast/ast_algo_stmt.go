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
