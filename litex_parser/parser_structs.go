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
	decl           fcDecl
	conceptName    TypeConceptStr
	typeVarMember  []FcVarDecl
	typeFnMember   []FcFnDecl
	typePropMember []PropDecl
	varMember      []FcVarDecl
	fnMember       []FcFnDecl
	propMember     []PropDecl
	thenFacts      []FactStmt
}

type DefTypeStmt struct {
	decl fcDecl
	// implType can be concept, or type, because a new type can either
	// implement a concept or just be a subset of a type
	implType       NamedFcType
	typeVarMember  []FcVarDecl
	typeFnMember   []FcFnDecl
	typePropMember []PropDecl
	varMember      []FcVarDecl
	fnMember       []FcFnDecl
	propMember     []PropDecl
	thenFacts      []FactStmt
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
	then       []SpecFactStmt
}

type FuncFactStmt struct {
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
	Facts []FactStmt
}

type DefExistStmt struct {
	decl      PropDecl
	ifFacts   []FactStmt
	member    []fcDecl
	thenFacts []FactStmt
}

type HaveStmt struct {
	propStmt SpecFactStmt
	member   []string
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
type IfFactStmt struct {
	condFacts []FactStmt
	thenFacts []SpecFactStmt
}

/*
Data structures below are not statement nodes.
*/

type TypeConceptStr string

type FcVarDecl struct {
	VarTypePair FcVarDeclPair
}

type FcVarDeclPair struct {
	Var string
	Tp  FcVarType
}

type FcFnDecl struct {
	name string
	tp   FcFnType
}

type PropDecl struct {
	name string
	tp   FcPropType
}

type TypeConceptPair struct {
	Var  TypeVarStr
	Type TypeConceptStr
}

type TypeVarStr string

type StrTypePair struct {
	Var  string
	Type fcType
}

type FcVarType struct {
	PackageName string
	Value       FcVarTypeValue
}

type FcVarTypeStrValue string
type FcVarTypeFuncValue struct {
	Name       string
	TypeParams []TypeVarStr
	VarParams  []Fc
}

type FcFnType struct {
	typeParamsTypes []TypeConceptPair
	varParamsTypes  []StrTypePair
	retType         fcType
}

type FcPropType struct {
	typeParams []TypeConceptPair
	varParams  []StrTypePair
}

type UndefinedFnType struct{}

var undefinedFnTypeInstance *UndefinedFnType = &UndefinedFnType{}

type UndefinedVarType struct{}

var undefinedVarTypeInstance *UndefinedVarType = &UndefinedVarType{}

type UndefinedPropType struct{}

var undefinedPropTypeInstance *UndefinedPropType = &UndefinedPropType{}

var AnyType = Keywords["any"]
var VarType = Keywords["var"]
var FnType = Keywords["fn"]
var PropType = Keywords["prop"]

type NamedFcType struct {
	typeNameArr []string // packageName.packageName.typeName
	params      []Fc
}

type fcUndefinedType interface {
	fcUndefinedType()
	fcType()
}

func (f *UndefinedFnType) fcUndefinedType()   {}
func (f *UndefinedVarType) fcUndefinedType()  {}
func (f *UndefinedPropType) fcUndefinedType() {}
