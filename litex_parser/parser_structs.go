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
	decl            string
	structName      TypeConceptStr
	typeMembers     []TypeMember
	instanceMembers []InstanceMember
	knowFacts       []FactStmt
}

type DefTypeStmt struct {
	decl            string
	typeMembers     []TypeMember
	instanceMembers []InstanceMember
	knowFacts       []FactStmt
}

type DefPropStmt struct {
	DeclHeader PropDeclHeader
	CondFacts  []FactStmt
	ThenFacts  []FactStmt
}

type DefFnStmt struct {
	name      string
	tp        []string
	CondFacts []FactStmt
	ThenFacts []FactStmt
}

type BlockForallStmt struct {
	VarParams []string
	CondFacts []FactStmt
	ThenFacts []SpecFactStmt
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

type DefAliasStmt struct {
	PreviousName string
	NewName      string
}

type KnowStmt struct {
	Facts []FactStmt
}

type DefExistStmt struct {
	decl      PropDeclHeader
	ifFacts   []FactStmt
	member    []InstanceMember
	thenFacts []FactStmt
}

type HaveStmt struct {
	propStmt SpecFactStmt
	member   []string
}

// syntax sugar for defining spec prop + claim forall true
type AxiomStmt struct {
	decl DefPropExistDeclStmt
}

// syntax sugar for defining spec prop + claim forall true + prove it
type ThmStmt struct {
	decl  DefPropExistDeclStmt
	proof []Stmt
}

type WhenCondFactStmt struct {
	CondFacts []FactStmt
	ThenFacts []SpecFactStmt
}

/*
Data structures below are not statement nodes.
*/

type TypeConceptStr string

type FcFnDecl struct {
	name string
	vars []string
}

type PropDeclHeader struct {
	name string
	vars []string
}

// type FcObjTypeStrValue string
// type FcObjTypeFuncValue struct {
// 	Name      string
// 	ObjParams []Fc
// }
