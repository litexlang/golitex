package litex_ast

type SpecificFactStmt interface {
	specificFactStmt()
	factStmt()
	stmt()
	String() string
	InstantiateFact(map[string]Obj) (FactStmt, error)
	ToLatexString() string
	canBeKnown()
	InlineString() string
	GetLine() uint
	algoStmt()
	Instantiate(map[string]Obj) (Stmt, error)
	SetLine(l uint)
	ReverseIsTrue() []SpecificFactStmt
}

func (s *PureSpecificFactStmt) specificFactStmt()  {}
func (s *ExistSpecificFactStmt) specificFactStmt() {}

type PureSpecificFactStmt struct {
	IsTrue   bool
	PropName Atom
	Params   ObjSlice
	Line     uint
}

type ExistSpecificFactStmt struct {
	IsTrue             bool
	ExistFreeParams    []string
	ExistFreeParamSets []Obj
	PureFact           *PureSpecificFactStmt
	Line               uint
}

func (s *PureSpecificFactStmt) ReverseIsTrue() []SpecificFactStmt {
	return []SpecificFactStmt{NewPureSpecificFactStmt(!s.IsTrue, s.PropName, s.Params, s.Line)}
}

func (s *ExistSpecificFactStmt) ReverseIsTrue() []SpecificFactStmt {
	return []SpecificFactStmt{NewExistSpecificFactStmt(!s.IsTrue, s.ExistFreeParams, s.ExistFreeParamSets, s.PureFact, s.Line)}
}
