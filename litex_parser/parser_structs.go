package litexparser

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
	DeclHeader PropDeclHeader
	CondFacts  []FactStmt
	ThenFacts  []FactStmt
}

type DefConcreteExistPropStmt struct {
	DeclHeader PropDeclHeader
	Members    []DefMember
	CondFacts  []FactStmt
	ThenFacts  []FactStmt
}

type DefConcreteFnStmt struct {
	Name      string
	Params    []string
	CondFacts []FactStmt
	ThenFacts []FactStmt
}

type ConcreteForallStmt struct {
	Params     []string
	ParamTypes []Fc // 注意到函数的返回值也可以是集合，所以这里是Fc，而不是string
	CondFacts  []FactStmt
	ThenFacts  []SpecFactStmt
}

type GenericForallStmt struct {
	TypeParams     []string
	TypeInterfaces []FcAtom
	Params         []string
	ParamTypes     []Fc
	CondFacts      []FactStmt
	ThenFacts      []SpecFactStmt
}

type FuncFactStmt struct {
	IsTrue bool
	Opt    FcAtom
	Params []Fc
}

type RelationFactStmt struct {
	IsTrue bool
	Opt    FcAtom
	Params []Fc
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
	propStmt SpecFactStmt
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

type ConditionalFactStmt struct {
	CondFacts []FactStmt
	ThenFacts []SpecFactStmt
}

/*
Data structures below are not statement nodes.
*/

// type TypeConceptStr string

type FcFnDecl struct {
	Name   string
	Params []string
}

type PropDeclHeader struct {
	Name   string
	Params []string
}

// type FcObjTypeStrValue string
// type FcObjTypeFuncValue struct {
// 	Name      string
// 	ObjParams []Fc
// }
