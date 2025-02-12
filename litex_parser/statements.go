package litexparser

type TopStmt struct {
	Stmt  Stmt
	IsPub bool
}

type DefVarStmt struct {
	Decl  FcVarDecl
	Facts []factStmt
}

// if concept and type has more conceptTypes, use know impl

type DefConceptStmt struct {
	decl               fcDecl
	conceptName        TypeConceptStr
	typeVarMember      []FcVarDecl
	typeFnMember       []FcFnDecl
	typePropertyMember []PropDecl
	varMember          []FcVarDecl
	fnMember           []FcFnDecl
	propertyMember     []PropDecl
	thenFacts          []factStmt
}

type DefTypeStmt struct {
	decl               fcDecl
	conceptName        TypeConceptStr
	typeVarMember      []FcVarDecl
	typeFnMember       []FcFnDecl
	typePropertyMember []PropDecl
	varMember          []FcVarDecl
	fnMember           []FcFnDecl
	propertyMember     []PropDecl
	thenFacts          []factStmt
}

type DefPropStmt struct {
	decl      PropDecl
	ifFacts   []factStmt
	thenFacts []factStmt
}

type DefFnStmt struct {
	decl      FcFnDecl
	ifFacts   []factStmt
	thenFacts []factStmt
}

type ForallStmt struct {
	typeParams []TypeConceptPair
	varParams  []StrTypePair
	ifFacts    []factStmt
	thenFacts  []factStmt
}

type FuncPtyStmt struct {
	IsTrue bool
	Fc     Fc
}

// 1 = 2 -1 = 1 * 1, vars = [1, 2 -1, 1 * 1], opt = "="
type RelationFactStmt struct {
	isTrue bool
	vars   []Fc
	opt    Fc
}

type ClaimProveByContradictStmt struct {
	toCheck []factStmt
	proof   []Stmt
}

type ClaimProveStmt struct {
	toCheck []factStmt
	proof   []Stmt
}

type ThmStmt struct {
	decl  DefPropExistDeclStmt
	proof []Stmt
}

type DefuseStmt struct {
	name     string
	variable Fc
}

type KnowStmt struct {
	facts []factStmt
}

type DefExistStmt struct {
	decl      PropDecl
	ifFacts   []factStmt
	member    []fcDecl
	thenFacts []factStmt
}

type HaveStmt struct {
	propertyStmt NotFactStmt
	member       []string
}

type DefMemberStmt struct {
	typeConcept TypeConceptPair
	varType     StrTypePair
	member      fcDecl
	facts       []factStmt
}

type DefTypeMemberStmt struct {
	typeConcept TypeConceptPair
	member      fcDecl
	facts       []factStmt
}

type AxiomStmt struct {
	decl DefPropExistDeclStmt
}
