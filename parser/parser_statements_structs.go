package parser

type TopStmt struct {
	stmt  Stmt
	isPub bool
}

type DefVarStmt struct {
	decl  FcVarDecl
	facts []factStmt
}

type DefConceptStmt struct {
	typeVar            TypeVarStr
	fcType             fcType
	conceptName        TypeConceptStr
	inherit            []TypeConceptStr
	typeVarMember      []FcVarDecl
	typeFnMember       []FcFnDecl
	typePropertyMember []PropertyDecl
	varMember          []FcVarDecl
	fnMember           []FcFnDecl
	propertyMember     []PropertyDecl
	thenFacts          []factStmt
}

type DefTypeStmt struct {
	typeVar        TypeVarStr
	fcType         fcType
	extendTypeName TypeVarStr // 方便继承操作符和接口，比如复数extend了实数，那复数的性质实数都有
	conceptName    TypeConceptStr
	varMember      []FcVarDecl
	fnMember       []FcFnDecl
	propertyMember []PropertyDecl
	thenFacts      []factStmt
}

type DefPropertyStmt struct {
	decl      PropertyDecl
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
	varParams  []FcStrTypePair
	ifFacts    []factStmt
	thenFacts  []factStmt
}

type FuncPtyStmt struct {
	isTrue bool
	fc     Fc
}

// 1 = 2 -1 = 1 * 1, vars = [1, 2 -1, 1 * 1], opt = "="
type RelationFactStmt struct {
	isTrue bool
	vars   []Fc
	opt    Fc
}

type ClaimStmt struct {
	toCheck []factStmt
	proof   []Stmt
}

type DefuseStmt struct {
	name     string
	variable Fc
}

type KnowStmt struct {
	facts []factStmt
}

type DefExistStmt struct {
	decl      PropertyDecl
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
	varType     FcStrTypePair
	member      fcDecl
	facts       []factStmt
}

type DefTypeMemberStmt struct {
	typeConcept TypeConceptPair
	member      fcDecl
	facts       []factStmt
}
