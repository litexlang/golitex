package litexparser

import (
	"fmt"
	ast "golitex/litex_ast"
	glob "golitex/litex_global"
)

func (parser *StrSliceCursor) bracedFcSlice() ([]ast.Fc, error) {
	params := []ast.Fc{}
	parser.skip(glob.KeywordLeftParen)

	for !parser.is(glob.KeywordRightParen) {
		fc, err := parser.Fc()

		if err != nil {
			return nil, &parserErr{err, parser}
		}

		params = append(params, fc)

		if !parser.is(glob.KeywordComma) {
			if !parser.is(glob.KeywordRightParen) {
				return nil, &parserErr{err, parser}
			} else {
				break
			}
		} else {
			parser.next()
		}

	}

	parser.skip(glob.KeywordRightParen)

	return params, nil
}

func (parser *StrSliceCursor) paramSliceInDeclHeadAndSkipEnd(endWith string) ([]string, []ast.Fc, error) {
	paramName := []string{}
	paramTypes := []ast.Fc{}

	for !parser.is(endWith) {
		objName, err := parser.next()
		if err != nil {
			return nil, nil, &parserErr{err, parser}
		}

		tp, err := parser.Fc()
		if err != nil {
			return nil, nil, &parserErr{err, parser}
		}

		paramName = append(paramName, objName)
		paramTypes = append(paramTypes, tp)

		if parser.isAndSkip(endWith) {
			break
		}

		if err := parser.testAndSkip(glob.KeywordComma); err != nil {
			return nil, nil, &parserErr{err, parser}
		}
	}

	return paramName, paramTypes, nil
}

func (parser *StrSliceCursor) stringSliceUntilEnd() ([]string, error) {
	members := []string{}

	for {
		member, err := parser.next()
		if err != nil {
			return nil, &parserErr{err, parser}
		}
		members = append(members, member)
		if !parser.is(glob.KeywordComma) {
			break
		}
		parser.skip()
	}

	if !parser.ExceedEnd() {
		return nil, &parserErr{fmt.Errorf("expected comma or end of string array"), parser}
	}

	return members, nil
}

func (parser *StrSliceCursor) isExpr(left ast.Fc) (*ast.SpecFactStmt, error) {
	err := parser.skip(glob.KeywordIs)
	if err != nil {
		return nil, &parserErr{err, parser}
	}

	opt, err := parser.fcAtom() // get the operator.

	if err != nil {
		return nil, &parserErr{err, parser}
	}

	return ast.NewSpecFactStmt(true, opt, []ast.Fc{left}), nil
	// return &ast.SpecFactStmt{true, opt, []ast.Fc{left}}, nil
}

func (stmt *TokenBlock) defPropExistStmt() (ast.DefPropStmt, error) {
	if stmt.Header.is(glob.KeywordProp) {
		prop, err := stmt.defConPropStmt()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
		return prop, nil
	} else if stmt.Header.is(glob.KeywordExistProp) {
		exist, err := stmt.defConExistPropStmt()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
		return exist, nil
	}

	return nil, fmt.Errorf(`expected keyword "prop" or "exist"`)
}

func (parser *StrSliceCursor) typeListInDeclsAndSkipEnd(endWith string) ([]string, []*ast.FcAtom, error) {
	paramName := []string{}
	paramTypes := []*ast.FcAtom{}

	for !parser.is(endWith) {
		objName, err := parser.next()
		if err != nil {
			return nil, nil, &parserErr{err, parser}
		}

		tp, err := parser.fcAtom()
		if err != nil {
			return nil, nil, &parserErr{err, parser}
		}

		paramName = append(paramName, objName)
		paramTypes = append(paramTypes, &tp)

		if parser.isAndSkip(endWith) {
			break
		}

		if err := parser.testAndSkip(glob.KeywordComma); err != nil {
			return nil, nil, &parserErr{err, parser}
		}
	}

	return paramName, paramTypes, nil
}
