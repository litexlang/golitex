package parser

type varTypePairBracketBrace struct {
	pairs []VarTypePair
	facts []FactExprStmt
}

type VarTypePair struct {
	Var  string
	Type string
}

type Var interface {
}

type PureVar string

type FnReturnVar struct {
	CalledFn
}

type CalledFn struct {
	Name   string
	Params []Var
}
