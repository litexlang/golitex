package parser

type topStmt struct {
	stmt  Stmt
	isPub bool
}

type defVarStmt struct {
	decl  FcVarDecl
	facts []factStmt
}

type defConceptStmt struct {
	typeVar            typeVarStr
	fcType             fcType
	conceptName        typeConceptStr
	inherit            []typeConceptStr
	typeVarMember      []FcVarDecl
	typeFnMember       []FcFnDecl
	typePropertyMember []PropertyDecl
	varMember          []FcVarDecl
	fnMember           []FcFnDecl
	propertyMember     []PropertyDecl
	thenFacts          []factStmt
}

type defTypeStmt struct {
	typeVar        typeVarStr
	fcType         fcType
	conceptName    typeConceptStr
	varMember      []FcVarDecl
	fnMember       []FcFnDecl
	propertyMember []PropertyDecl
	thenFacts      []factStmt
}

type defPropertyStmt struct {
	decl      PropertyDecl
	ifFacts   []factStmt
	thenFacts []factStmt
}

type defFnStmt struct {
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

type funcPtyStmt struct {
	isTrue bool
	fc     Fc
}

// 1 = 2 -1 = 1 * 1, vars = [1, 2 -1, 1 * 1], opt = "="
type relationFactStmt struct {
	isTrue bool
	vars   []Fc
	opt    Fc
}

type claimStmt struct {
	toCheck []factStmt
	proof   []Stmt
}

type defuseStmt struct {
	name     string
	variable Fc
}

type knowStmt struct {
	facts []factStmt
}

type defExistStmt struct {
	decl      PropertyDecl
	ifFacts   []factStmt
	member    []fcDecl
	thenFacts []factStmt
}

type haveStmt struct {
	propertyStmt NotFactStmt
	member       []string
}

type defMemberStmt struct {
	typeConcept TypeConceptPair
	varType     FcStrTypePair
	member      fcDecl
	facts       []factStmt
}

type defTypeMemberStmt struct {
	typeConcept TypeConceptPair
	member      fcDecl
	facts       []factStmt
}
