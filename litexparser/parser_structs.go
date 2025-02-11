package litexparser

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

type PropertyDecl struct {
	name string
	tp   FcPropertyType
}

type TypeConceptPair struct {
	Var  TypeVarStr
	Type TypeConceptStr
}

type TypeVarStr string

type TypedTypeVar struct {
	value   TypeVarStr
	concept TypeConceptStr
}

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
	TypeParams []typeVar
	VarParams  []Fc
}

type FcFnType struct {
	typeParamsTypes []TypeConceptPair
	varParamsTypes  []StrTypePair
	retType         fcType
}

type FcPropertyType struct {
	typeParams []TypeConceptPair
	varParams  []StrTypePair
}

type UndefinedFnType struct{}

var undefinedFnTypeInstance *UndefinedFnType = &UndefinedFnType{}

type UndefinedVarType struct{}

var undefinedVarTypeInstance *UndefinedVarType = &UndefinedVarType{}

type UndefinedPropertyType struct{}

var undefinedPropertyTypeInstance *UndefinedPropertyType = &UndefinedPropertyType{}

var AnyType = Keywords["any"]
var VarType = Keywords["var"]
var FnType = Keywords["fn"]
var PropertyType = Keywords["prop"]
