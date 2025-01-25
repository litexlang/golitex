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
	FCCFnRetVal
}

type FCCFnRetVal struct {
	fn         FCC
	typeParams []FCC
	varParams  []FCC
}

type Declaration interface{}

// 变量和函数是一等公民。它们的表现形式是：1. 单纯的string 2. 函数返回值
type FCC interface{}

type FCCStr string

type Var interface{}
