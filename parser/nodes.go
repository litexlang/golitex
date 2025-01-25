package parser

type varTypePairBracket struct {
	pairs []varTypePair
}

type varTypePair struct {
	Var  string
	Type string
}

type SingletonVar string

type FnReturnVar struct {
	FcFnRetVal
}

type FcFnRetVal struct {
	fn         Fc
	typeParams []FcStr
	varParams  []Fc
}

type Declaration interface{}

// 变量和函数是一等公民。它们的表现形式是：1. 单纯的string 2. 函数返回值
type Fc interface{}

type FcStr string

type Var interface{}
