package parser

type varTypePairBracketBrace struct {
	pairs []VarTypePair
	facts []FactStmt
}

type VarTypePair struct {
	Var  string
	Type string
}

type Var interface {
}

type SingletonVar string

type FnReturnVar struct {
	CalledFn
}

type CalledFn struct {
	Name   string
	Params []Var
}

type Declaration interface{}
