package parser

type bracketedVarTypePair struct {
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

type Fc interface{}

type FcStr string

type Var interface{}

type FcMemberAccessExpr struct {
	Fc []Fc
}
