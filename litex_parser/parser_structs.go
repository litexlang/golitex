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

type PropDecl struct {
	name string
	tp   FcPropType
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
