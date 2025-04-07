package litexstatements

import (
	glob "golitex/litex_global"
)

type TopStmt struct {
	Stmt  Stmt
	IsPub bool
}

type DefObjStmt struct {
	Objs    []string
	ObjSets []Fc
	Facts   []FactStmt
}

type DefInterfaceStmt struct {
}

type DefTypeStmt struct {
}

type DefConPropStmt struct {
	DefHeader ConDefHeader
	DomFacts  []FactStmt      // 如果输入的参数不满足dom，那就是error
	IffFacts  []*SpecFactStmt // 如果输入参数满足dom，满足iff，那就true. 这里必须是spec，因为我需要 know forall x: prop+dom => iffFacts，而iffFacts出现在了then的位置
}

type DefConExistPropStmt struct {
	DefHeader    ConDefHeader
	ExistFc      []string
	ExistFcTypes []*FcAtom
	DomFacts     []FactStmt
	ThenFacts    []FactStmt
}

type DefConFnStmt struct {
	DefHeader ConDefHeader
	RetType   Fc
	DomFacts  []FactStmt
	ThenFacts []*SpecFactStmt
}

type UniFactStmt struct {
	Params     []string // 它可能也是来自另外一个被share的地方。比如defConFn里面的Params，在被存成facts的时候，整个struct被复制到了这里，但本质上它们共享了一片内存
	ParamTypes []Fc
	DomFacts   []FactStmt
	ThenFacts  []*SpecFactStmt
}

type GenericUniStmt struct {
	TypeParams     []string
	TypeInterfaces []*FcAtom
	Params         []string
	ParamTypes     []Fc
	DomFacts       []FactStmt
	ThenFacts      []*SpecFactStmt
}

type SpecFactStmt struct {
	IsTrue   bool
	PropName FcAtom
	Params   []Fc
}

func (f *SpecFactStmt) IsEqualFact() bool {
	return f.PropName.Value == glob.KeywordEqual && f.PropName.PkgName == ""
}

type ClaimProveByContradictStmt struct {
	ToCheck []FactStmt
	Proof   []Stmt
}

type ClaimProveStmt struct {
	ToCheckFacts []FactStmt
	Proofs       []Stmt
}

type KnowStmt struct {
	Facts []FactStmt
}

type HaveStmt struct {
	PropStmt SpecFactStmt
	Member   []string
}

// syntax sugar for defining spec prop + claim forall true
type AxiomStmt struct {
	Decl DefPropStmt
}

// syntax sugar for defining spec prop + claim forall true + prove it
type ThmStmt struct {
	Decl  DefPropStmt
	Proof []Stmt
}

type CondFactStmt struct {
	CondFacts []FactStmt
	ThenFacts []*SpecFactStmt
}

type FcFnDecl struct {
	Name   string
	Params []string
}

type ConDefHeader struct {
	Name       string
	Params     []string
	TypeParams []Fc
}
