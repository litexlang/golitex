package litexparser

type TopStmt struct {
	Stmt  Stmt
	IsPub bool
}

type DefVarStmt struct {
	Decl  FcVarDecl
	Facts []FactStmt
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
	thenFacts          []FactStmt
}

type DefTypeStmt struct {
	decl fcDecl
	// implType can be concept, or type, because a new type can either
	// implement a concept or just be a subset of a type
	implType           NamedFcType
	typeVarMember      []FcVarDecl
	typeFnMember       []FcFnDecl
	typePropertyMember []PropDecl
	varMember          []FcVarDecl
	fnMember           []FcFnDecl
	propertyMember     []PropDecl
	thenFacts          []FactStmt
}

type DefPropStmt struct {
	decl      PropDecl
	ifFacts   []FactStmt
	thenFacts []FactStmt
}

type DefFnStmt struct {
	name string
	tp   FcFnType
	// decl      FcFnDecl
	ifFacts   []FactStmt
	thenFacts []FactStmt
}

type BlockForallStmt struct {
	typeParams []TypeConceptPair
	varParams  []StrTypePair
	cond       []FactStmt
	then       []BaseFactStmt
}

type FuncPropStmt struct {
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
	facts []FactStmt
}

type DefExistStmt struct {
	decl      PropDecl
	ifFacts   []FactStmt
	member    []fcDecl
	thenFacts []FactStmt
}

type HaveStmt struct {
	propertyStmt BaseFactStmt
	member       []string
}

type DefMemberStmt struct {
	typeConcept TypeConceptPair
	varType     StrTypePair
	member      fcDecl
	facts       []FactStmt
}

type DefTypeMemberStmt struct {
	typeConcept TypeConceptPair
	member      fcDecl
	facts       []FactStmt
}

// syntax sugar for defining propExist + claim forall true
type AxiomStmt struct {
	decl DefPropExistDeclStmt
}

// syntax sugar for defining propExist + claim forall true
type ThmStmt struct {
	decl  DefPropExistDeclStmt
	proof []Stmt
}

// TODO 需要写一下 什么类型的事实写成什么样
type InlineIfFactStmt struct {
	condFacts []FactStmt
	thenFacts []BaseFactStmt
}

// forall []() cond {then}
// type InlineForallStmt struct {
// 	typeParams []TypeConceptPair
// 	varParams  []StrTypePair
// 	cond       []InlineFactStmt
// 	then       []BaseFactStmt
// }
