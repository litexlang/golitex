// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Litex email: <litexlang@outlook.com>
// Litex website: https://litexlang.com
// Litex github repository: https://github.com/litexlang/golitex
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_parser

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
)

func (p *tbParser) Obj(tb *tokenBlock) (ast.Obj, error) {
	return nil, fmt.Errorf("not implemented")
}

func (p *tbParser) objInfixExpr(tb *tokenBlock, currentPrec glob.BuiltinOptPrecedence) (ast.Obj, error) {
	return nil, fmt.Errorf("not implemented")
}

func (p *tbParser) unaryOptObj(tb *tokenBlock) (ast.Obj, error) {
	return nil, fmt.Errorf("not implemented")
}

func (p *tbParser) fnSetObjAndBracedExprAndAtomObjAndFnObj(tb *tokenBlock) (ast.Obj, error) {
	return nil, fmt.Errorf("not implemented")
}

func (p *tbParser) notNumberAtom(tb *tokenBlock) (ast.Atom, error) {
	return ast.Atom(""), fmt.Errorf("not implemented")
}

func (p *tbParser) numberAtom(tb *tokenBlock) (ast.Atom, error) {
	return ast.Atom(""), fmt.Errorf("not implemented")
}

func (p *tbParser) bracedObjSlice(tb *tokenBlock) ([]ast.Obj, error) {
	return nil, fmt.Errorf("not implemented")
}

func (p *tbParser) bracketedObj(tb *tokenBlock) (ast.Obj, error) {
	return nil, fmt.Errorf("not implemented")
}

func (p *tbParser) bracedObj(tb *tokenBlock) (ast.Obj, error) {
	return nil, fmt.Errorf("not implemented")
}

func (p *tbParser) fnObjWithRepeatedBraceAndBracket(tb *tokenBlock, head ast.Obj) (ast.Obj, error) {
	return nil, fmt.Errorf("not implemented")
}

func (p *tbParser) fnSet(tb *tokenBlock) (ast.Obj, error) {
	return nil, fmt.Errorf("not implemented")
}

func (p *tbParser) backSlashExpr(tb *tokenBlock) (ast.Obj, error) {
	return nil, fmt.Errorf("not implemented")
}

func (p *tbParser) EnumSetObjOrIntensionalSetObj(tb *tokenBlock) (ast.Obj, error) {
	return nil, fmt.Errorf("not implemented")
}

func (p *tbParser) intensionalSetObj(tb *tokenBlock, paramAsObj ast.Obj) (ast.Obj, error) {
	return nil, fmt.Errorf("not implemented")
}

func (p *tbParser) enumSetObj(tb *tokenBlock, firstParam ast.Obj) (ast.Obj, error) {
	return nil, fmt.Errorf("not implemented")
}

func (p *tbParser) makeEnumSetObj(params []ast.Obj) ast.Obj {
	return nil
}

func (p *tbParser) makeIntensionalSetObj(param string, parentSet ast.Obj, facts []ast.FactStmt) ast.Obj {
	return nil
}
