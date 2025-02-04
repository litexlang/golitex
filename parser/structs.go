package parser

type typeConceptStr string

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
	retType         fcType
}

type propertyType struct {
	typeParams []typeConceptPair
	varParams  []fcStrTypePair
}

type undefinedFnType struct{}

var undefinedFnTypeInstance *undefinedFnType = &undefinedFnType{}

type undefinedVarType struct{}

var undefinedVarTypeInstance *undefinedVarType = &undefinedVarType{}

type undefinedPropertyType struct{}

var undefinedPropertyTypeInstance *undefinedPropertyType = &undefinedPropertyType{}
