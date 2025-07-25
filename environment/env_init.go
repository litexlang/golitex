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
// Litex website: https://litexlang.org
// Litex github repository: https://github.com/litexlang/golitex
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_env

import (
	ast "golitex/ast"
	glob "golitex/glob"
)

// template of arithmetic operations。用来证明 + $in fn(R, R)R 这样的事实
func (env *Env) Init() {
	addAtom := ast.FcAtom(glob.KeySymbolPlus)
	addTemplateQ := ast.NewFnTemplateNoName([]string{"x", "y"}, []ast.Fc{ast.FcAtom(glob.KeywordRational), ast.FcAtom(glob.KeywordRational)}, ast.FcAtom(glob.KeywordRational), []ast.FactStmt{}, []ast.FactStmt{})
	env.InsertFnInFnTT(addAtom, nil, addTemplateQ)
	addTemplateN := ast.NewFnTemplateNoName([]string{"x", "y"}, []ast.Fc{ast.FcAtom(glob.KeywordNatural), ast.FcAtom(glob.KeywordNatural)}, ast.FcAtom(glob.KeywordNatural), []ast.FactStmt{}, []ast.FactStmt{})
	env.InsertFnInFnTT(addAtom, nil, addTemplateN)
	addTemplateZ := ast.NewFnTemplateNoName([]string{"x", "y"}, []ast.Fc{ast.FcAtom(glob.KeywordInteger), ast.FcAtom(glob.KeywordInteger)}, ast.FcAtom(glob.KeywordInteger), []ast.FactStmt{}, []ast.FactStmt{})
	env.InsertFnInFnTT(addAtom, nil, addTemplateZ)
	addTemplateR := ast.NewFnTemplateNoName([]string{"x", "y"}, []ast.Fc{ast.FcAtom(glob.KeywordReal), ast.FcAtom(glob.KeywordReal)}, ast.FcAtom(glob.KeywordReal), []ast.FactStmt{}, []ast.FactStmt{})
	env.InsertFnInFnTT(addAtom, nil, addTemplateR)

	minusAtom := ast.FcAtom(glob.KeySymbolMinus)
	minusTemplateQ := ast.NewFnTemplateNoName([]string{"x", "y"}, []ast.Fc{ast.FcAtom(glob.KeywordRational), ast.FcAtom(glob.KeywordRational)}, ast.FcAtom(glob.KeywordRational), []ast.FactStmt{}, []ast.FactStmt{})
	env.InsertFnInFnTT(minusAtom, nil, minusTemplateQ)
	minusTemplateN := ast.NewFnTemplateNoName([]string{"x", "y"}, []ast.Fc{ast.FcAtom(glob.KeywordNatural), ast.FcAtom(glob.KeywordNatural)}, ast.FcAtom(glob.KeywordNatural), []ast.FactStmt{}, []ast.FactStmt{})
	env.InsertFnInFnTT(minusAtom, nil, minusTemplateN)
	minusTemplateZ := ast.NewFnTemplateNoName([]string{"x", "y"}, []ast.Fc{ast.FcAtom(glob.KeywordInteger), ast.FcAtom(glob.KeywordInteger)}, ast.FcAtom(glob.KeywordInteger), []ast.FactStmt{}, []ast.FactStmt{})
	env.InsertFnInFnTT(minusAtom, nil, minusTemplateZ)
	minusTemplateR := ast.NewFnTemplateNoName([]string{"x", "y"}, []ast.Fc{ast.FcAtom(glob.KeywordReal), ast.FcAtom(glob.KeywordReal)}, ast.FcAtom(glob.KeywordReal), []ast.FactStmt{}, []ast.FactStmt{})
	env.InsertFnInFnTT(minusAtom, nil, minusTemplateR)

	starAtom := ast.FcAtom(glob.KeySymbolStar)
	starTemplateQ := ast.NewFnTemplateNoName([]string{"x", "y"}, []ast.Fc{ast.FcAtom(glob.KeywordRational), ast.FcAtom(glob.KeywordRational)}, ast.FcAtom(glob.KeywordRational), []ast.FactStmt{}, []ast.FactStmt{})
	env.InsertFnInFnTT(starAtom, nil, starTemplateQ)
	starTemplateN := ast.NewFnTemplateNoName([]string{"x", "y"}, []ast.Fc{ast.FcAtom(glob.KeywordNatural), ast.FcAtom(glob.KeywordNatural)}, ast.FcAtom(glob.KeywordNatural), []ast.FactStmt{}, []ast.FactStmt{})
	env.InsertFnInFnTT(starAtom, nil, starTemplateN)
	starTemplateZ := ast.NewFnTemplateNoName([]string{"x", "y"}, []ast.Fc{ast.FcAtom(glob.KeywordInteger), ast.FcAtom(glob.KeywordInteger)}, ast.FcAtom(glob.KeywordInteger), []ast.FactStmt{}, []ast.FactStmt{})
	env.InsertFnInFnTT(starAtom, nil, starTemplateZ)
	starTemplateR := ast.NewFnTemplateNoName([]string{"x", "y"}, []ast.Fc{ast.FcAtom(glob.KeywordReal), ast.FcAtom(glob.KeywordReal)}, ast.FcAtom(glob.KeywordReal), []ast.FactStmt{}, []ast.FactStmt{})
	env.InsertFnInFnTT(starAtom, nil, starTemplateR)

	slashAtom := ast.FcAtom(glob.KeySymbolSlash)
	slashTemplateQ := ast.NewFnTemplateNoName([]string{"x", "y"}, []ast.Fc{ast.FcAtom(glob.KeywordRational), ast.FcAtom(glob.KeywordRational)}, ast.FcAtom(glob.KeywordRational), []ast.FactStmt{ast.NewSpecFactStmt(ast.FalsePure, ast.FcAtom(glob.KeySymbolEqual), []ast.Fc{ast.FcAtom("y"), ast.FcAtom("0")})}, []ast.FactStmt{})
	env.InsertFnInFnTT(slashAtom, nil, slashTemplateQ)
	slashTemplateN := ast.NewFnTemplateNoName([]string{"x", "y"}, []ast.Fc{ast.FcAtom(glob.KeywordNatural), ast.FcAtom(glob.KeywordNatural)}, ast.FcAtom(glob.KeywordNatural), []ast.FactStmt{ast.NewSpecFactStmt(ast.FalsePure, ast.FcAtom(glob.KeySymbolEqual), []ast.Fc{ast.FcAtom("y"), ast.FcAtom("0")})}, []ast.FactStmt{})
	env.InsertFnInFnTT(slashAtom, nil, slashTemplateN)
	slashTemplateZ := ast.NewFnTemplateNoName([]string{"x", "y"}, []ast.Fc{ast.FcAtom(glob.KeywordInteger), ast.FcAtom(glob.KeywordInteger)}, ast.FcAtom(glob.KeywordInteger), []ast.FactStmt{ast.NewSpecFactStmt(ast.FalsePure, ast.FcAtom(glob.KeySymbolEqual), []ast.Fc{ast.FcAtom("y"), ast.FcAtom("0")})}, []ast.FactStmt{})
	env.InsertFnInFnTT(slashAtom, nil, slashTemplateZ)
	slashTemplateR := ast.NewFnTemplateNoName([]string{"x", "y"}, []ast.Fc{ast.FcAtom(glob.KeywordReal), ast.FcAtom(glob.KeywordReal)}, ast.FcAtom(glob.KeywordReal), []ast.FactStmt{ast.NewSpecFactStmt(ast.FalsePure, ast.FcAtom(glob.KeySymbolEqual), []ast.Fc{ast.FcAtom("y"), ast.FcAtom("0")})}, []ast.FactStmt{})
	env.InsertFnInFnTT(slashAtom, nil, slashTemplateR)

	modAtom := ast.FcAtom(glob.KeySymbolPercent)
	modTemplate := ast.NewFnTemplateNoName([]string{"x", "y"}, []ast.Fc{ast.FcAtom(glob.KeywordInteger), ast.FcAtom(glob.KeywordInteger)}, ast.FcAtom(glob.KeywordInteger), []ast.FactStmt{ast.NewSpecFactStmt(ast.FalsePure, ast.FcAtom(glob.KeySymbolEqual), []ast.Fc{ast.FcAtom("y"), ast.FcAtom("0")})}, []ast.FactStmt{})
	env.InsertFnInFnTT(modAtom, nil, modTemplate)

	powerAtom := ast.FcAtom(glob.KeySymbolPower)
	powerTemplateR := ast.NewFnTemplateNoName([]string{"x", "y"}, []ast.Fc{ast.FcAtom(glob.KeywordReal), ast.FcAtom(glob.KeywordReal)}, ast.FcAtom(glob.KeywordComplex), []ast.FactStmt{}, []ast.FactStmt{})
	env.InsertFnInFnTT(powerAtom, nil, powerTemplateR)

	lenAtom := ast.FcAtom(glob.KeywordLen)
	lenTemplate := ast.NewFnTemplateNoName([]string{"x"}, []ast.Fc{ast.FcAtom(glob.KeywordSet)}, ast.FcAtom(glob.KeywordNatural), []ast.FactStmt{ast.NewInFactWithFc(ast.FcAtom("x"), ast.FcAtom(glob.KeywordFiniteSet))}, []ast.FactStmt{})
	env.InsertFnInFnTT(lenAtom, nil, lenTemplate)
}
