package litexparser

import (
	"fmt"
	glob "golitex/litex_global"
	st "golitex/litex_statements"
)

func (parser *StrSliceCursor) parseBracedFcArr() ([]st.Fc, error) {
	params := []st.Fc{}
	parser.skip(glob.KeywordLeftParen)

	for !parser.is(glob.KeywordRightParen) {
		fc, err := parser.ParseFc()

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

func (parser *StrSliceCursor) parseParamListInDeclsAndSkipEnd(endWith string) ([]string, []st.Fc, error) {
	paramName := []string{}
	paramTypes := []st.Fc{}

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

		if err := parser.testAndSkip(glob.KeywordComma); err != nil {
			return nil, nil, &parserErr{err, parser}
		}
	}

	return paramName, paramTypes, nil
}

func (parser *StrSliceCursor) parseStringArrUntilEnd() ([]string, error) {
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

func (parser *StrSliceCursor) parseIsExpr(left st.Fc) (*st.SpecFactStmt, error) {
	err := parser.skip(glob.KeywordIs)
	if err != nil {
		return nil, &parserErr{err, parser}
	}

	opt, err := parser.parseFcAtom() // get the operator.

	if err != nil {
		return nil, &parserErr{err, parser}
	}

	return &st.SpecFactStmt{true, opt, []st.Fc{left}}, nil
}

func (stmt *TokenBlock) parseDefPropExistStmt() (st.DefPropStmt, error) {
	if stmt.Header.is(glob.KeywordProp) {
		prop, err := stmt.parseDefConPropStmt()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
		return prop, nil
	} else if stmt.Header.is(glob.KeywordExistProp) {
		exist, err := stmt.parseDefConExistPropStmt()
		if err != nil {
			return nil, &parseStmtErr{err, *stmt}
		}
		return exist, nil
	}

	return nil, fmt.Errorf(`expected keyword "prop" or "exist"`)
}

func (parser *StrSliceCursor) parseTypeListInDeclsAndSkipEnd(endWith string) ([]string, []*st.FcAtom, error) {
	paramName := []string{}
	paramTypes := []*st.FcAtom{}

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
