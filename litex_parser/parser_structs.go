package litexparser

import (
	glob "golitex/litex_global"
)

type TopStmt struct {
	Stmt  Stmt
	IsPub bool
}

type DefObjStmt struct {
	Objs  []string
	Facts []FactStmt
}

type DefInterfaceStmt struct {
}

type DefTypeStmt struct {
}

type DefConcreteNormalPropStmt struct {
	DefHeader      ConcreteDefHeader
	ParamCondFacts []FactStmt
	ThenFacts      []FactStmt
}

type DefConcreteExistPropStmt struct {
	DefHeader      ConcreteDefHeader
	ExistFc        []string
	ExistFcTypes   []FcAtom
	ParamCondFacts []FactStmt
	ThenFacts      []FactStmt
}

type DefConcreteFnStmt struct {
	DefHeader      ConcreteDefHeader
	retType        FcAtom
	ParamCondFacts []FactStmt
	ThenFacts      []FactStmt
}

type UniFactStmt struct {
	Params         []string
	ParamTypes     []Fc
	ParamCondFacts []FactStmt
	ThenFacts      []SpecFactStmt
}

type GenericUniStmt struct {
	TypeParams     []string
	TypeInterfaces []FcAtom
	Params         []string
	ParamTypes     []Fc
	ParamCondFacts []FactStmt
	ThenFacts      []SpecFactStmt
}

type SpecFactStmt struct {
	IsTrue bool
	Opt    FcAtom
	Params []Fc
}

func (f *SpecFactStmt) IsEqualFact() bool {
	return f.Opt.OptName == glob.KeywordEqual && f.Opt.PkgName == ""
}

type ClaimProveByContradictStmt struct {
	toCheck []FactStmt
	proof   []Stmt
}

type ClaimProveStmt struct {
	toCheck []FactStmt
	proof   []Stmt
}

type KnowStmt struct {
	Facts []FactStmt
}

type HaveStmt struct {
	PropStmt SpecFactStmt
	member   []string
}

// syntax sugar for defining spec prop + claim forall true
type AxiomStmt struct {
	decl DefPropStmt
}

// syntax sugar for defining spec prop + claim forall true + prove it
type ThmStmt struct {
	decl  DefPropStmt
	proof []Stmt
}

type CondFactStmt struct {
	CondFacts []FactStmt
	ThenFacts []SpecFactStmt
}

type FcFnDecl struct {
	Name   string
	Params []string
}

type ConcreteDefHeader struct {
	Name       string
	Params     []string
	TypeParams []FcAtom
}
