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

func (parser *Parser) parseFcVarTypePairArrEndWithColon() (*[]string, error) {
	pairs := []string{}

	for !parser.is(BuiltinSyms[":"]) {
		varName, err := parser.next()
		if err != nil {
			return nil, &parserErr{err, parser}
		}

		pairs = append(pairs, varName)

		if parser.isAndSkip(BuiltinSyms[":"]) {
			break
		}

		if err := parser.testAndSkip(BuiltinSyms[","]); err != nil {
			return nil, &parserErr{err, parser}
		}
	}

	return &pairs, nil
}

func (parser *Parser) parseBracedFcTypePairArr() (*[]string, error) {
	var err error = nil

	varParams := &[]string{}
	varParams, err = parser.parseBracedFcStrTypePairArray()
	if err != nil {
		return nil, err
	}

	return varParams, nil
}

func (parser *Parser) parseFcFnDecl() (*FcFnDecl, error) {
	parser.skip(KeywordFn)

	name, err := parser.next()
	if err != nil {
		return nil, &parserErr{err, parser}
	}

	varParamsTypes, err := parser.parseBracedFcTypePairArr()
	if err != nil {
		return nil, &parserErr{err, parser}
	}

	return &FcFnDecl{name, *varParamsTypes}, nil
}

func (parser *Parser) parseBracedFcStrTypePairArray() (*[]string, error) {
	fcSlice := []string{}
	parser.skip(BuiltinSyms["("])

	for !parser.is(BuiltinSyms[")"]) {
		s, err := parser.next()
		if err != nil {
			return nil, &parserErr{err, parser}
		}

		// fcType, err := parser.parseFcType()
		// if err != nil {
		// 	return nil, &parserErr{err, parser}
		// }

		fcSlice = append(fcSlice, s)

		if parser.isAndSkip(BuiltinSyms[")"]) {
			break
		}

		if err := parser.testAndSkip(BuiltinSyms[","]); err != nil {
			return nil, &parserErr{err, parser}
		}
	}

	return &fcSlice, nil
}

func (parser *Parser) parsePropDecl() (*PropDecl, error) {
	parser.skip(KeywordProp)
	name, err := parser.next()
	if err != nil {
		return nil, &parserErr{err, parser}
	}

	varParams, err := parser.parseBracedFcTypePairArr()
	if err != nil {
		return nil, &parserErr{err, parser}
	}

	return &PropDecl{name, *varParams}, nil
}

func (parser *Parser) parseExistDecl() (*PropDecl, error) {
	parser.skip(KeywordExist)
	name, err := parser.next()
	if err != nil {
		return nil, &parserErr{err, parser}
	}

	varParams, err := parser.parseBracedFcTypePairArr()
	if err != nil {
		return nil, &parserErr{err, parser}
	}

	return &PropDecl{name, *varParams}, nil
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
	err := parser.skip(KeywordIs)
	if err != nil {
		return nil, &parserErr{err, parser}
	}

	opt, err := parser.next() // get the operator.

	if err != nil {
		return nil, &parserErr{err, parser}
	}

	return &FuncFactStmt{true, &FcFnRetValue{FcStr(opt), []TypeParamsAndVarParamsPair{{[]Fc{left}}}}}, nil
}

func (stmt *TokenBlock) parseDefPropExistStmt() (DefPropExistDeclStmt, error) {
	if stmt.Header.is(KeywordProp) {
		prop, err := stmt.parseDefPropStmt()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
		return prop, nil
	} else if stmt.Header.is(KeywordExist) {
		exist, err := stmt.parseDefExistStmt()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
		return exist, nil
	}

	return nil, fmt.Errorf(`expected keyword "prop" or "exist"`)
}

// func (parser *Parser) parseNamedFcType() (*NamedFcType, error) {
// 	name, err := parser.next()
// 	if err != nil {
// 		return nil, &parserErr{err, parser}
// 	}

// 	typeNameArr := []string{name}
// 	params := []Fc{}

// 	for parser.is(BuiltinSyms["."]) {
// 		parser.skip()
// 		name, err := parser.next()
// 		if err != nil {
// 			return nil, &parserErr{err, parser}
// 		}
// 		typeNameArr = append(typeNameArr, name)
// 	}

// 	if parser.is(BuiltinSyms["("]) {
// 		paramsPtr, err := parser.parseBracedFcArr()
// 		if err != nil {
// 			return nil, &parserErr{err, parser}
// 		}
// 		params = *paramsPtr
// 		parser.skip(BuiltinSyms[")"])
// 	}

// 	return &NamedFcType{typeNameArr, params}, nil
// }

func (block *TokenBlock) parseTypeMember() (TypeMember, error) {
	if block.Header.is(KeywordVar) {
		return block.parseDefVarStmt()
	} else if block.Header.is(KeywordFn) {
		return block.parseDefFnStmt()
	} else if block.Header.is(KeywordProp) {
		return block.parseDefPropStmt()
	} else if block.Header.is(KeywordType) {
		return block.parseDefTypeStmt()
	}

	return nil, fmt.Errorf("var, fn, prop, type expected")
}

func (block *TokenBlock) parseInstanceMember() (InstanceMember, error) {
	if block.Header.is(KeywordVar) {
		return block.parseDefVarStmt()
	} else if block.Header.is(KeywordFn) {
		return block.parseDefFnStmt()
	} else if block.Header.is(KeywordProp) {
		return block.parseDefPropStmt()
	}
	return nil, fmt.Errorf("var, fn, prop expected")
}
