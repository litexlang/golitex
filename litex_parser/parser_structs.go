package litexparser

type TopStmt struct {
	Stmt  Stmt
	IsPub bool
}

type DefVarStmt struct {
	Decl  FcVarDecl
	Facts []FactStmt
}

type DefStructStmt struct {
	decl            fcDecl
	structName      TypeConceptStr
	typeMembers     []TypeMember
	instanceMembers []InstanceMember
	knowFacts       []FactStmt
}

type DefTypeStmt struct {
	decl            fcDecl
	implType        NamedFcType
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
	Vars   []Fc
	Opt    FcStr
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
type CondFactStmt struct {
	CondFacts []FactStmt
	ThenFacts []SpecFactStmt
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
	tp   []string
}

type PropDecl struct {
	name string
	tp   []string
	// tp   FcPropType
}

type TypeDecl struct {
	DefType DefTypeStmt
}

type TypeConceptPair struct {
	Var  TypeVarStr
	Type TypeConceptStr
}

type TypeVarStr string

// type StrTypePair struct {
// 	Var  string
// 	Type fcType
// }

type FcVarType struct {
	PackageName string
	Value       FcVarTypeValue
}

type FcVarTypeStrValue string
type FcVarTypeFuncValue struct {
	Name string
	// TypeParams []TypeVarStr
	VarParams []Fc
}

// type FcFnType struct {
// 	// typeParamsTypes []TypeConceptPair
// 	varParamsTypes []StrTypePair
// 	retType        fcType
// }

// type FcPropType struct {
// 	// typeParams []TypeConceptPair
// 	varParams []StrTypePair
// }

var AnyType = Keywords["any"]
var VarType = Keywords["var"]
var FnType = Keywords["fn"]
var PropType = Keywords["prop"]

type NamedFcType struct {
	typeNameArr []string // packageName.packageName.typeName
	params      []Fc
}
