package parser

type topStmt struct {
	stmt  Stmt
	isPub bool
}

type typeConceptStr string

type defVarStmt struct {
	decl  fcVarDecl
	facts []factStmt
}

type defConceptStmt struct {
	typeVar            typeVarStr
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
	conceptName    typeConceptStr
	varMember      []fcVarDecl
	fnMember       []fcFnDecl
	propertyMember []propertyDecl
	thenFacts      []factStmt
}

type fcVarDecl struct {
	varTypePairs []fcStrTypePair
}

type fcFnDecl struct {
	name string
	tp   fcFnType
}

type propertyDecl struct {
	name string
	tp   propertyType
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

type localStmt struct {
	statements []Stmt
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

type typeConceptPair struct {
	Var  typeVarStr
	Type typeConceptStr
}

type typeVarStr string

type typedTypeVar struct {
	value   typeVarStr
	concept typeConceptStr
}

type fcStrTypePair struct {
	Var  FcStr
	Type fcType
}

type fcVarType string

type fcFnType struct {
	typeParamsTypes []typeConceptPair
	varParamsTypes  []fcStrTypePair
	retType         fnRetType
}

// 需要让 property 不能是 fc type
type propertyType struct {
	typeParams []typeConceptPair
	varParams  []fcStrTypePair // TODO not fcType!
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
