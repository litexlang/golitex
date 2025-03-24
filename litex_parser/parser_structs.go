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

// TODO: Generics
type DefSpecPropStmt struct {
	DeclHeader PropDeclHeader
	CondFacts  []FactStmt
	ThenFacts  []FactStmt
}

// TODO: Generics
type DefFnStmt struct {
	name      string
	tp        []string
	CondFacts []FactStmt
	ThenFacts []FactStmt
}

// TODO: Generics
type ConcreteForallStmt struct {
	Params     []string
	ParamTypes []Fc
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

// type DefAliasStmt struct {
// 	PreviousName string
// 	NewName      string
// }

type KnowStmt struct {
	Facts []FactStmt
}

type DefExistPropStmt struct {
	DeclHeader PropDeclHeader
	CondFacts  []FactStmt
	Members    []DefMember
	ThenFacts  []FactStmt
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
