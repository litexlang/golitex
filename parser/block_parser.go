package parser

func (p *tokenBlock) parseMember() (*[]fcVarDecl, *[]fcFnDecl, *[]propertyDecl, error) {
	p.header.next()
	if err := p.header.testAndSkip(Keywords[":"]); err != nil {
		return nil, nil, nil, err
	}

	varMember := &[]fcVarDecl{}
	fnMember := &[]fcFnDecl{}
	propertyMember := &[]propertyDecl{}

	for _, curStmt := range p.body {
		if curStmt.header.is(Keywords["var"]) {
			member, err := p.parseVarDecl()
			if err != nil {
				return nil, nil, nil, err
			}
			*varMember = append(*varMember, *member)
		} else if curStmt.header.is(Keywords["fn"]) {
			member, err := p.parseFnDecl()
			if err != nil {
				return nil, nil, nil, err
			}
			*fnMember = append(*fnMember, *member)
		} else if curStmt.header.is(Keywords["property"]) {
			member, err := p.parsePropertyDecl()
			if err != nil {
				return nil, nil, nil, err
			}
			*propertyMember = append(*propertyMember, *member)
		}
	}

	return varMember, fnMember, propertyMember, nil
}

func (stmt *tokenBlock) parseVarDecl() (*fcVarDecl, error) {
	stmt.header.next()
	name, err := stmt.header.next()
	if err != nil {
		return nil, err
	}

	// TODO
	typ, err := stmt.header.parseFcVarType()
	if err != nil {
		return nil, err
	}

	return &fcVarDecl{name, typ}, nil
}

func (stmt *tokenBlock) parseFnDecl() (*fcFnDecl, error) {
	stmt.header.next()
	name, err := stmt.header.next()
	if err != nil {
		return nil, err
	}

	// TODO
	typ, err := stmt.header.parseFcFnType()
	if err != nil {
		return nil, err
	}

	return &fcFnDecl{name, *typ}, nil

}

func (stmt *tokenBlock) parsePropertyDecl() (*propertyDecl, error) {
	stmt.header.next()
	name, err := stmt.header.next()
	if err != nil {
		return nil, err
	}

	// TODO
	typ, err := stmt.header.parsePropertyType()
	if err != nil {
		return nil, err
	}

	return &propertyDecl{name, *typ}, nil
}

func (stmt *tokenBlock) parseThenFacts() (*[]FactStmt, error) {
	stmt.header.next()
	if err := stmt.header.testAndSkip(BuiltinSyms[":"]); err != nil {
		return nil, err
	}

	facts := &[]FactStmt{}

	for _, curStmt := range stmt.body {
		if curStmt.header.is(Keywords["fact"]) {
			fact, err := curStmt.parseFactStmt()
			if err != nil {
				return nil, err
			}
			*facts = append(*facts, fact)
		}
	}

	return facts, nil
}
