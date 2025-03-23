package litexparser

type TopStmt struct {
	Stmt  Stmt
	IsPub bool
}

type DefObjStmt struct {
	Decl  []string
	Facts []FactStmt
}

type DefSetStructStmt struct {
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
	decl      PropDecl
	condFacts []FactStmt
	thenFacts []FactStmt
}

type DefFnStmt struct {
	name      string
	tp        []string
	ifFacts   []FactStmt
	thenFacts []FactStmt
}

type BlockForallStmt struct {
	varParams []string
	cond      []FactStmt
	then      []SpecFactStmt
}

type FuncFactStmt struct {
	IsTrue bool
	Fc     Fc
}

type RelationFactStmt struct {
	IsTrue bool
	Objs   []Fc
	Opt    FcAtom
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
	decl      PropDecl
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

type PropDecl struct {
	name string
	vars []string
}

// type FcObjTypeStrValue string
// type FcObjTypeFuncValue struct {
// 	Name      string
// 	ObjParams []Fc
// }
