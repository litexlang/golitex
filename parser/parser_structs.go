package parser

type TypeConceptStr string

type FcVarDecl struct {
	varTypePairs []FcStrTypePair
}

type FcFnDecl struct {
	name string
	tp   FcFnType
}

type PropertyDecl struct {
	name string
	tp   PropertyType
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

type FcStrTypePair struct {
	Var  FcStr
	Type fcType
}

type FcVarType string

type FcFnType struct {
	typeParamsTypes []TypeConceptPair
	varParamsTypes  []FcStrTypePair
	retType         fcType
}

type PropertyType struct {
	typeParams []TypeConceptPair
	varParams  []FcStrTypePair
}

type UndefinedFnType struct{}

var undefinedFnTypeInstance *UndefinedFnType = &UndefinedFnType{}

type UndefinedVarType struct{}

var undefinedVarTypeInstance *UndefinedVarType = &UndefinedVarType{}

type UndefinedPropertyType struct{}

var undefinedPropertyTypeInstance *UndefinedPropertyType = &UndefinedPropertyType{}
