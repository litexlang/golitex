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

// template of arithmetic operations。 不知道是不是应该放在 pipeline_init.go 里
func (env *Env) Init() {
	// addAtom := ast.FcAtom(glob.KeySymbolPlus)
	// addTemplate := ast.NewFnTemplateStmt(ast.NewDefHeader(addAtom, []string{"x", "y"}, []ast.Fc{ast.FcAtom(glob.KeywordReal), ast.FcAtom(glob.KeywordReal)}), []ast.FactStmt{}, []ast.FactStmt{}, ast.FcAtom(glob.KeywordReal))
	// env.FcSatisfy_FreeTemplateFact_Store_DeriveFacts(addAtom, addTemplate)

	// minusAtom := ast.FcAtom(glob.KeySymbolMinus)
	// minusTemplate := ast.NewFnTemplateStmt(ast.NewDefHeader(minusAtom, []string{"x", "y"}, []ast.Fc{ast.FcAtom(glob.KeywordReal), ast.FcAtom(glob.KeywordReal)}), []ast.FactStmt{}, []ast.FactStmt{}, ast.FcAtom(glob.KeywordReal))
	// env.FcSatisfy_FreeTemplateFact_Store_DeriveFacts(minusAtom, minusTemplate)

	// starAtom := ast.FcAtom(glob.KeySymbolStar)
	// starTemplate := ast.NewFnTemplateStmt(ast.NewDefHeader(starAtom, []string{"x", "y"}, []ast.Fc{ast.FcAtom(glob.KeywordReal), ast.FcAtom(glob.KeywordReal)}), []ast.FactStmt{}, []ast.FactStmt{}, ast.FcAtom(glob.KeywordReal))
	// env.FcSatisfy_FreeTemplateFact_Store_DeriveFacts(starAtom, starTemplate)

	// slashAtom := ast.FcAtom(glob.KeySymbolSlash)
	// slashTemplate := ast.NewFnTemplateStmt(ast.NewDefHeader(slashAtom, []string{"x", "y"}, []ast.Fc{ast.FcAtom(glob.KeywordReal), ast.FcAtom(glob.KeywordReal)}), []ast.FactStmt{}, []ast.FactStmt{ast.NewSpecFactStmt(ast.FalsePure, ast.FcAtom(glob.KeySymbolEqual), []ast.Fc{ast.FcAtom("y"), ast.FcAtom("0")})}, ast.FcAtom(glob.KeywordReal))
	// env.FcSatisfy_FreeTemplateFact_Store_DeriveFacts(slashAtom, slashTemplate)

	// modAtom := ast.FcAtom(glob.KeySymbolPercent)
	// modTemplate := ast.NewFnTemplateStmt(ast.NewDefHeader(modAtom, []string{"x", "y"}, []ast.Fc{ast.FcAtom(glob.KeywordInteger), ast.FcAtom(glob.KeywordInteger)}), []ast.FactStmt{}, []ast.FactStmt{ast.NewSpecFactStmt(ast.FalsePure, ast.FcAtom(glob.KeySymbolEqual), []ast.Fc{ast.FcAtom("y"), ast.FcAtom("0")})}, ast.FcAtom(glob.KeywordInteger))
	// env.FcSatisfy_FreeTemplateFact_Store_DeriveFacts(modAtom, modTemplate)

	// lenAtom := ast.FcAtom(glob.KeywordLen)
	// lenTemplate := ast.NewFnTemplateStmt(ast.NewDefHeader(lenAtom, []string{"x"}, []ast.Fc{ast.FcAtom(glob.KeywordSet)}), []ast.FactStmt{ast.NewInFactWithFc(ast.FcAtom("x"), ast.FcAtom(glob.KeywordFiniteSet))}, []ast.FactStmt{}, ast.FcAtom(glob.KeywordNatural))
	// env.FcSatisfy_FreeTemplateFact_Store_DeriveFacts(lenAtom, lenTemplate)
}
