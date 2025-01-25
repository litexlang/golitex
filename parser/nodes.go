package parser

type varTypePairBracketBrace struct {
	pairs []VarTypePair
	facts []FactStmt
}

type VarTypePair struct {
	Var  string
	Type string
}

type SingletonVar string

type FnReturnVar struct {
	CalledFn
}

type CalledFn struct {
	fn         FirstClassEntity
	typeParams []FirstClassEntity
	varParams  []FirstClassEntity
}

type Declaration interface{}

// 变量和函数是一等公民。它们的表现形式是：1. 单纯的string 2. 函数返回值
type FirstClassEntity interface {
}

type FirstClassStr string

type FnReturnValue struct {
	fn         FirstClassEntity
	typeParams []FirstClassEntity
	varParams  []FirstClassEntity
}
