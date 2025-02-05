package parser

type typeConceptStr string

type fcVarDecl struct {
	varTypePairs []FcStrTypePair
}

type fcFnDecl struct {
	name string
	tp   fcFnType
}

type propertyDecl struct {
	name string
	tp   propertyType
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

type fcVarType string

type fcFnType struct {
	typeParamsTypes []TypeConceptPair
	varParamsTypes  []FcStrTypePair
	retType         fcType
}

type propertyType struct {
	typeParams []TypeConceptPair
	varParams  []FcStrTypePair
}

type undefinedFnType struct{}

var undefinedFnTypeInstance *undefinedFnType = &undefinedFnType{}

type undefinedVarType struct{}

var undefinedVarTypeInstance *undefinedVarType = &undefinedVarType{}

type undefinedPropertyType struct{}

var undefinedPropertyTypeInstance *undefinedPropertyType = &undefinedPropertyType{}
