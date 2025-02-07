package parser

type TopStmt struct {
	Stmt  Stmt
	IsPub bool
}

type DefVarStmt struct {
	Decl  FcVarDecl
	Facts []factStmt
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
	fcType         fcType // 可以是 fn, 比如 type m Matrix(a nat, b nat) fn m(i nat, b nat) nat: 1 <= i <= a, 1 <= j <= b then: m(i,j) = xxx(i,j) ...。这也可以看到有下标的都是 函数
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
	varType     StrTypePair
	member      fcDecl
	facts       []factStmt
}

type DefTypeMemberStmt struct {
	typeConcept TypeConceptPair
	member      fcDecl
	facts       []factStmt
}
