package parser

type topStmt struct {
	stmt  Stmt
	isPub bool
}

type defVarStmt struct {
	decl  fcVarDecl
	facts []factStmt
}

type defConceptStmt struct {
	typeVar            typeVarStr
	fcType             fnRetType
	conceptName        typeConceptStr
	inherit            []typeConceptStr
	typeVarMember      []fcVarDecl
	typeFnMember       []fcFnDecl
	typePropertyMember []propertyDecl
	varMember          []fcVarDecl
	fnMember           []fcFnDecl
	propertyMember     []propertyDecl
	thenFacts          []factStmt
}

type defTypeStmt struct {
	typeVar        typeVarStr
	fcType         fnRetType
	conceptName    typeConceptStr
	varMember      []fcVarDecl
	fnMember       []fcFnDecl
	propertyMember []propertyDecl
	thenFacts      []factStmt
}

type defPropertyStmt struct {
	decl      propertyDecl
	ifFacts   []factStmt
	thenFacts []factStmt
}

type defFnStmt struct {
	decl      fcFnDecl
	ifFacts   []factStmt
	thenFacts []factStmt
}

type forallStmt struct {
	typeParams []typeConceptPair
	varParams  []fcStrTypePair
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
	decl      propertyDecl
	ifFacts   []factStmt
	member    []fnRetTypeMemberDecl
	thenFacts []factStmt
}

type haveStmt struct {
	propertyStmt notFactStmt
	member       []string
}

type defMemberStmt struct {
	typeConcept typeConceptPair
	varType     fcStrTypePair
	member      fcDecl
	facts       []factStmt
}

type defTypeMemberStmt struct {
	typeConcept typeConceptPair
	member      fcDecl
	facts       []factStmt
}
