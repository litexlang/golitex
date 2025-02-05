package parser

type typeConceptStr string

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
	Var  typeVarStr
	Type typeConceptStr
}

type typeVarStr string

type typedTypeVar struct {
	value   typeVarStr
	concept typeConceptStr
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

type undefinedFnType struct{}

var undefinedFnTypeInstance *undefinedFnType = &undefinedFnType{}

type undefinedVarType struct{}

var undefinedVarTypeInstance *undefinedVarType = &undefinedVarType{}

type undefinedPropertyType struct{}

var undefinedPropertyTypeInstance *undefinedPropertyType = &undefinedPropertyType{}
