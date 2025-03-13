package litexparser

import (
	"fmt"
)

func (parser *Parser) parseBracedFcArr() (*[]Fc, error) {
	params := []Fc{}
	parser.skip(BuiltinSyms["("])

	for !parser.is(BuiltinSyms[")"]) {
		fc, err := parser.ParseFc()

		if err != nil {
			return nil, &parserErr{err, parser}
		}

		params = append(params, fc)

		if !parser.is(BuiltinSyms[","]) {
			if !parser.is(BuiltinSyms[")"]) {
				return nil, &parserErr{err, parser}
			} else {
				break
			}
		} else {
			parser.next()
		}

	}

	parser.skip(BuiltinSyms[")"])

	return &params, nil
}

func (parser *Parser) parseFcVarTypePairArrEndWithColon() (*[]StrTypePair, error) {
	pairs := []StrTypePair{}

	for !parser.is(BuiltinSyms[":"]) {
		varName, err := parser.next()
		if err != nil {
			return nil, &parserErr{err, parser}
		}

		typeName, err := parser.parseFcType()
		if err != nil {
			return nil, &parserErr{err, parser}
		}

		pairs = append(pairs, StrTypePair{(varName), (typeName)})

		if parser.isAndSkip(BuiltinSyms[":"]) {
			break
		}

		if err := parser.testAndSkip(BuiltinSyms[","]); err != nil {
			return nil, &parserErr{err, parser}
		}
	}

	return &pairs, nil
}

func (parser *Parser) parseFcFnVar() (*FcFnType, error) {
	parser.skip(Keywords["fn"])

	typeParamsTypes := &[]TypeConceptPair{}
	var err error = nil
	if parser.is(BuiltinSyms["["]) {
		typeParamsTypes, err = parser.parseBracketedTypeConceptPairArray()
		if err != nil {
			return nil, &parserErr{err, parser}
		}
	}

	varParamsTypes := &[]StrTypePair{}
	if parser.is(BuiltinSyms["("]) {
		varParamsTypes, err = parser.parseBracedFcStrTypePairArray()
		if err != nil {
			return nil, &parserErr{err, parser}
		}

	}

	retType, err := parser.parseFcType()
	if err != nil {
		return nil, &parserErr{err, parser}
	}

	return &FcFnType{*typeParamsTypes, *varParamsTypes, retType}, nil
}

func (parser *Parser) parseBracketedTypeConceptPairArrAndBracedFcTypePairArr() (*[]TypeConceptPair, *[]StrTypePair, error) {
	typeParamsTypes := &[]TypeConceptPair{}
	var err error = nil
	if parser.is(BuiltinSyms["["]) {
		typeParamsTypes, err = parser.parseBracketedTypeConceptPairArray()
		if err != nil {
			return nil, nil, err
		}
	}

	varParamsTypes := &[]StrTypePair{}
	if parser.is(BuiltinSyms["("]) {
		varParamsTypes, err = parser.parseBracedFcStrTypePairArray()
		if err != nil {
			return nil, nil, err
		}
	}

	return typeParamsTypes, varParamsTypes, nil
}

func (parser *Parser) parseFcFnDecl() (*FcFnDecl, error) {
	parser.skip(Keywords["fn"])

	name, err := parser.next()
	if err != nil {
		return nil, &parserErr{err, parser}
	}

	typeParamsTypes, varParamsTypes, err := parser.parseBracketedTypeConceptPairArrAndBracedFcTypePairArr()
	if err != nil {
		return nil, &parserErr{err, parser}
	}

	retType, err := parser.parseFcType()
	if err != nil {
		return nil, &parserErr{err, parser}
	}

	return &FcFnDecl{name, FcFnType{*typeParamsTypes, *varParamsTypes, retType}}, nil
}

func (parser *Parser) parseFcType() (fcType, error) {
	if parser.is(BuiltinSyms["?"]) {
		return parser.parseUndefinedFcType()
	}

	if parser.is(Keywords["fn"]) {
		return parser.parseFcFnVar()
	} else if parser.is(Keywords["prop"]) {
		return parser.parsePropType()
	} else {
		return parser.parseFcVarType()
	}
}

func (parser *Parser) parseUndefinedFcType() (fcUndefinedType, error) {
	parser.skip(BuiltinSyms["?"])
	if parser.is(Keywords["fn"]) {
		parser.skip()
		return undefinedFnTypeInstance, nil
	} else if parser.is(Keywords["prop"]) {
		parser.skip()
		return undefinedVarTypeInstance, nil
	} else if parser.is(Keywords["var"]) {
		parser.skip()
		return undefinedPropTypeInstance, nil
	}

	return nil, &parserErr{fmt.Errorf("expect 'fn', 'prop', 'var' after '?'"), parser}
}

// func (parser *Parser) parseFnRetType() (fnRetType, error) {
// 	if parser.is(Keywords["fn"]) {
// 		return parser.parseFcFnVar()
// 	} else {
// 		return parser.parseFcVarType()
// 	}
// }

func (parser *Parser) parsePropType() (*FcPropType, error) {
	parser.skip()

	typeParams, varParams, err := parser.parseBracketedTypeConceptPairArrAndBracedFcTypePairArr()
	if err != nil {
		return nil, &parserErr{err, parser}
	}

	return &FcPropType{*typeParams, *varParams}, nil
}

func (parser *Parser) parseFcVarType() (FcVarType, error) {
	packageName := ""
	name, err := parser.next()

	if err != nil {
		return FcVarType{"", nil}, err
	}

	if parser.is(BuiltinSyms["::"]) {
		parser.skip()
		packageName = name

		name, err = parser.next()
		if err != nil {
			return FcVarType{"", nil}, err
		}
	}

	isFunc := false
	typeParams := &[]TypeVarStr{}
	varParams := &[]Fc{}
	if parser.is(BuiltinSyms["["]) {
		typeParams, err = parser.parseBracketedTypeVarArr()
		if err != nil {
			return FcVarType{"", nil}, err
		}
		isFunc = true
	}

	if parser.is(BuiltinSyms["("]) {
		varParams, err = parser.parseBracedFcArr()
		if err != nil {
			return FcVarType{"", nil}, err
		}
		isFunc = true
	}

	if isFunc {
		return FcVarType{packageName, &FcVarTypeFuncValue{name, *typeParams, *varParams}}, nil
	} else {
		return FcVarType{packageName, FcVarTypeStrValue(name)}, nil
	}

}

func (parser *Parser) parseTypeConcept() (TypeConceptStr, error) {
	tok, err := parser.next()
	if err != nil {
		return "", err
	}
	return TypeConceptStr(tok), nil
}

func (parser *Parser) parseBracketedTypeConceptPairArray() (*[]TypeConceptPair, error) {
	concepts := []TypeConceptPair{}
	parser.skip(BuiltinSyms["["])

	for !parser.is(BuiltinSyms["]"]) {
		name, err := parser.parseTypeVarStr()
		if err != nil {
			return nil, &parserErr{err, parser}
		}

		concept, err := parser.parseTypeConcept()
		if err != nil {
			return nil, &parserErr{err, parser}
		}

		concepts = append(concepts, TypeConceptPair{name, concept})

		if parser.isAndSkip(BuiltinSyms["]"]) {
			break
		}

		if err := parser.testAndSkip(BuiltinSyms[","]); err != nil {
			return nil, &parserErr{err, parser}
		}
	}

	return &concepts, nil
}

func (parser *Parser) parseBracedFcStrTypePairArray() (*[]StrTypePair, error) {
	pairs := []StrTypePair{}
	parser.skip(BuiltinSyms["("])

	for !parser.is(BuiltinSyms[")"]) {
		s, err := parser.next()
		if err != nil {
			return nil, &parserErr{err, parser}
		}

		fcType, err := parser.parseFcType()
		if err != nil {
			return nil, &parserErr{err, parser}
		}

		pairs = append(pairs, StrTypePair{s, fcType})

		if parser.isAndSkip(BuiltinSyms[")"]) {
			break
		}

		if err := parser.testAndSkip(BuiltinSyms[","]); err != nil {
			return nil, &parserErr{err, parser}
		}
	}

	return &pairs, nil
}

func (parser *Parser) parseVarDecl() (*FcVarDecl, error) {
	parser.skip(Keywords["var"])

	pair, err := parser.parseFcVarPair()
	if err != nil {
		return nil, &parserErr{err, parser}
	}

	return &FcVarDecl{*pair}, nil
}

func (parser *Parser) parseFcVarPair() (*FcVarDeclPair, error) {
	v, err := parser.next()
	if err != nil {
		return nil, &parserErr{err, parser}
	}

	tp, err := parser.parseFcVarType()
	if err != nil {
		return nil, &parserErr{err, parser}
	}

	return &FcVarDeclPair{v, tp}, nil
}

func (parser *Parser) parsePropDecl() (*PropDecl, error) {
	parser.skip(Keywords["prop"])
	name, err := parser.next()
	if err != nil {
		return nil, &parserErr{err, parser}
	}

	typeParams, varParams, err := parser.parseBracketedTypeConceptPairArrAndBracedFcTypePairArr()
	if err != nil {
		return nil, &parserErr{err, parser}
	}

	return &PropDecl{name, FcPropType{*typeParams, *varParams}}, nil
}

func (parser *Parser) parseExistDecl() (*PropDecl, error) {
	parser.skip(Keywords["exist"])
	name, err := parser.next()
	if err != nil {
		return nil, &parserErr{err, parser}
	}

	typeParams, varParams, err := parser.parseBracketedTypeConceptPairArrAndBracedFcTypePairArr()
	if err != nil {
		return nil, &parserErr{err, parser}
	}

	return &PropDecl{name, FcPropType{*typeParams, *varParams}}, nil
}

func (parser *Parser) parseStringArrUntilEnd() (*[]string, error) {
	members := &[]string{}

	for {
		member, err := parser.next()
		if err != nil {
			return nil, &parserErr{err, parser}
		}
		*members = append(*members, member)
		if !parser.is(BuiltinSyms[","]) {
			break
		}
		parser.skip()
	}

	if !parser.ExceedEnd() {
		return nil, &parserErr{fmt.Errorf("expected comma or end of string array"), parser}
	}

	return members, nil
}

func (parser *Parser) parseIsExpr(left Fc) (*FuncFactStmt, error) {
	err := parser.skip(Keywords["is"])
	if err != nil {
		return nil, &parserErr{err, parser}
	}

	opt, err := parser.next() // get the operator.

	if err != nil {
		return nil, &parserErr{err, parser}
	}

	typeParams := &[]TypeVarStr{}
	if parser.is(BuiltinSyms["["]) {
		typeParams, err = parser.parseBracketedTypeVarArr()
		if err != nil {
			return nil, &parserErr{err, parser}
		}

		if len(*typeParams) != 1 {
			return nil, &parserErr{fmt.Errorf("expect one type parameter"), parser}
		}
	}

	return &FuncFactStmt{true, &FcFnRetValue{FcStr(opt), []TypeParamsAndVarParamsPair{{*typeParams, []Fc{left}}}}}, nil
}

func (parser *Parser) parseTypeVar() (TypeVarStr, error) {
	return parser.parseTypeVarStr()
}

func (parser *Parser) parseTypeVarStr() (TypeVarStr, error) {
	name, err := parser.next()
	if err != nil {
		return "", &parserErr{err, parser}
	}

	return TypeVarStr(name), nil
}

func (parser *Parser) parseBracketedTypeVarArr() (*[]TypeVarStr, error) {
	arr := &[]TypeVarStr{}

	parser.skip(BuiltinSyms["["])

	for !parser.is(BuiltinSyms["]"]) {
		tv, err := parser.parseTypeVar()
		if err != nil {
			return nil, &parserErr{err, parser}
		}
		*arr = append(*arr, tv)

		if parser.is(BuiltinSyms[","]) {
			parser.skip()
		}

	}

	parser.skip(BuiltinSyms["]"])
	return arr, nil
}

func (stmt *TokenBlock) parseDefPropExistStmt() (DefPropExistDeclStmt, error) {
	if stmt.Header.is(Keywords["prop"]) {
		prop, err := stmt.parseDefPropStmt()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
		return prop, nil
	} else if stmt.Header.is(Keywords["exist"]) {
		exist, err := stmt.parseDefExistStmt()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
		return exist, nil
	}

	return nil, fmt.Errorf(`expected keyword "prop" or "exist"`)
}

func (parser *Parser) parseNamedFcType() (*NamedFcType, error) {
	name, err := parser.next()
	if err != nil {
		return nil, &parserErr{err, parser}
	}

	typeNameArr := []string{name}
	params := []Fc{}

	for parser.is(BuiltinSyms["."]) {
		parser.skip()
		name, err := parser.next()
		if err != nil {
			return nil, &parserErr{err, parser}
		}
		typeNameArr = append(typeNameArr, name)
	}

	if parser.is(BuiltinSyms["("]) {
		paramsPtr, err := parser.parseBracedFcArr()
		if err != nil {
			return nil, &parserErr{err, parser}
		}
		params = *paramsPtr
		parser.skip(BuiltinSyms[")"])
	}

	return &NamedFcType{typeNameArr, params}, nil
}

func (block *TokenBlock) parseTypeMember() (TypeMember, error) {
	if block.Header.is(Keywords["var"]) {
		return block.parseDefVarStmt()
	} else if block.Header.is(Keywords["fn"]) {
		return block.parseDefFnStmt()
	} else if block.Header.is(Keywords["prop"]) {
		return block.parseDefPropStmt()
	} else if block.Header.is(Keywords["type"]) {
		return block.parseDefTypeStmt()
	}

	return nil, fmt.Errorf("var, fn, prop, type expected")
}

func (block *TokenBlock) parseInstanceMember() (InstanceMember, error) {
	if block.Header.is(Keywords["var"]) {
		return block.parseDefVarStmt()
	} else if block.Header.is(Keywords["fn"]) {
		return block.parseDefFnStmt()
	} else if block.Header.is(Keywords["prop"]) {
		return block.parseDefPropStmt()
	}
	return nil, fmt.Errorf("var, fn, prop expected")
}
