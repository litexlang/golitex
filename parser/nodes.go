package parser

type TypeVarPair struct {
	Var  string
	Type string
}

type Fact interface{}
type ExistFact struct{}

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
