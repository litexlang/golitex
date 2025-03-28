package litexparser

import (
	"fmt"
)

func (parser *Parser) parseBracedFcArr() (*[]Fc, error) {
	params := []Fc{}
	parser.skip(KeywordLeftParen)

	for !parser.is(KeywordRightParen) {
		fc, err := parser.ParseFc()

		if err != nil {
			return nil, &parserErr{err, parser}
		}

		params = append(params, fc)

		if !parser.is(KeywordComma) {
			if !parser.is(KeywordRightParen) {
				return nil, &parserErr{err, parser}
			} else {
				break
			}
		} else {
			parser.next()
		}

	}

	parser.skip(KeywordRightParen)

	return &params, nil
}

func (parser *Parser) parseParamListInDeclsAndSkipEnd(endWith string) (*[]string, *[]Fc, error) {
	paramName := []string{}
	paramTypes := []Fc{}

	for !parser.is(endWith) {
		objName, err := parser.next()
		if err != nil {
			return nil, nil, &parserErr{err, parser}
		}

		tp, err := parser.ParseFc()
		if err != nil {
			return nil, nil, &parserErr{err, parser}
		}

		paramName = append(paramName, objName)
		paramTypes = append(paramTypes, tp)

		if parser.isAndSkip(endWith) {
			break
		}

		if err := parser.testAndSkip(KeywordComma); err != nil {
			return nil, nil, &parserErr{err, parser}
		}
	}

	return &paramName, &paramTypes, nil
}

// func (parser *Parser) parsePropDecl() (*ConcreteDefHeader, error) {
// 	parser.skip(KeywordSpecProp)
// 	name, err := parser.next()
// 	if err != nil {
// 		return nil, &parserErr{err, parser}
// 	}

// 	params, err := parser.parseBracedFcTypePairArr()
// 	if err != nil {
// 		return nil, &parserErr{err, parser}
// 	}

// 	return &ConcreteDefHeader{name, *params}, nil
// }

// func (parser *Parser) parseExistDecl() (*ConcreteDefHeader, error) {
// 	parser.skip(KeywordExistProp)
// 	panic("")
// }

func (parser *Parser) parseStringArrUntilEnd() (*[]string, error) {
	members := &[]string{}

	for {
		member, err := parser.next()
		if err != nil {
			return nil, &parserErr{err, parser}
		}
		*members = append(*members, member)
		if !parser.is(KeywordComma) {
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

	opt, err := parser.parseFcAtom() // get the operator.

	if err != nil {
		return nil, &parserErr{err, parser}
	}

	return &FuncFactStmt{true, opt, []Fc{left}}, nil
}

func (stmt *TokenBlock) parseDefPropExistStmt() (DefPropStmt, error) {
	if stmt.Header.is(KeywordProp) {
		prop, err := stmt.parseDefConcreteNormalPropStmt()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
		return prop, nil
	} else if stmt.Header.is(KeywordExistProp) {
		exist, err := stmt.parseDefConcreteExistPropStmt()
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

// 	for parser.is(KeywordDot) {
// 		parser.skip()
// 		name, err := parser.next()
// 		if err != nil {
// 			return nil, &parserErr{err, parser}
// 		}
// 		typeNameArr = append(typeNameArr, name)
// 	}

// 	if parser.is(KeywordLeftParen) {
// 		paramsPtr, err := parser.parseBracedFcArr()
// 		if err != nil {
// 			return nil, &parserErr{err, parser}
// 		}
// 		params = *paramsPtr
// 		parser.skip(KeywordRightParen)
// 	}

// 	return &NamedFcType{typeNameArr, params}, nil
// }

// func (block *TokenBlock) parseInstanceMember() (DefMember, error) {
// 	if block.Header.is(KeywordObj) {
// 		return block.parseDefObjStmt()
// 	} else if block.Header.is(KeywordFn) {
// 		return block.parseDefConcreteFnStmt()
// 	} else if block.Header.is(KeywordSpecProp) {
// 		return block.parseDefConcreteNormalPropStmt()
// 	} else if block.Header.is(KeywordExistProp) {
// 		return block.parseDefConcreteExistPropStmt()
// 	}
// 	return nil, fmt.Errorf("%v, %v, %v expected", KeywordObj, KeywordFn, KeywordSpecProp)
// }

func (parser *Parser) parseTypeListInDeclsAndSkipEnd(endWith string) (*[]string, *[]FcAtom, error) {
	paramName := []string{}
	paramTypes := []FcAtom{}

	for !parser.is(endWith) {
		objName, err := parser.next()
		if err != nil {
			return nil, nil, &parserErr{err, parser}
		}

		tp, err := parser.parseFcAtom()
		if err != nil {
			return nil, nil, &parserErr{err, parser}
		}

		paramName = append(paramName, objName)
		paramTypes = append(paramTypes, tp)

		if parser.isAndSkip(endWith) {
			break
		}

		if err := parser.testAndSkip(KeywordComma); err != nil {
			return nil, nil, &parserErr{err, parser}
		}
	}

	return &paramName, &paramTypes, nil
}
