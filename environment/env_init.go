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

func (env *Env) Init() {
	// 求余数
	add_minus_star_slash_mod_in_template(env)
}

func add_minus_star_slash_mod_in_template(env *Env) {
	addAtom := ast.NewFcAtom(glob.KeySymbolPlus)
	addTemplate := ast.NewFnTemplateStmt(*ast.NewDefHeader(addAtom.String(), []string{"x", "y"}, []ast.Fc{ast.NewFcAtom(glob.KeywordReal), ast.NewFcAtom(glob.KeywordReal)}), []ast.FactStmt{}, []ast.FactStmt{}, ast.NewFcAtom(glob.KeywordReal))
	env.FcSatisfy_FreeTemplateFact_Store_DeriveFacts(addAtom, addTemplate)

	minusAtom := ast.NewFcAtom(glob.KeySymbolMinus)
	minusTemplate := ast.NewFnTemplateStmt(*ast.NewDefHeader(minusAtom.String(), []string{"x", "y"}, []ast.Fc{ast.NewFcAtom(glob.KeywordReal), ast.NewFcAtom(glob.KeywordReal)}), []ast.FactStmt{}, []ast.FactStmt{}, ast.NewFcAtom(glob.KeywordReal))
	env.FcSatisfy_FreeTemplateFact_Store_DeriveFacts(minusAtom, minusTemplate)

	starAtom := ast.NewFcAtom(glob.KeySymbolStar)
	starTemplate := ast.NewFnTemplateStmt(*ast.NewDefHeader(starAtom.String(), []string{"x", "y"}, []ast.Fc{ast.NewFcAtom(glob.KeywordReal), ast.NewFcAtom(glob.KeywordReal)}), []ast.FactStmt{}, []ast.FactStmt{}, ast.NewFcAtom(glob.KeywordReal))
	env.FcSatisfy_FreeTemplateFact_Store_DeriveFacts(starAtom, starTemplate)

	slashAtom := ast.NewFcAtom(glob.KeySymbolSlash)
	slashTemplate := ast.NewFnTemplateStmt(*ast.NewDefHeader(slashAtom.String(), []string{"x", "y"}, []ast.Fc{ast.NewFcAtom(glob.KeywordReal), ast.NewFcAtom(glob.KeywordReal)}), []ast.FactStmt{}, []ast.FactStmt{ast.NewSpecFactStmt(ast.FalsePure, ast.NewFcAtom(glob.KeySymbolEqual), []ast.Fc{ast.NewFcAtom("y"), ast.NewFcAtom("0")})}, ast.NewFcAtom(glob.KeywordReal))
	env.FcSatisfy_FreeTemplateFact_Store_DeriveFacts(slashAtom, slashTemplate)

	modAtom := ast.NewFcAtom(glob.KeySymbolPercent)
	modTemplate := ast.NewFnTemplateStmt(*ast.NewDefHeader(modAtom.String(), []string{"x", "y"}, []ast.Fc{ast.NewFcAtom(glob.KeywordInt), ast.NewFcAtom(glob.KeywordInt)}), []ast.FactStmt{}, []ast.FactStmt{ast.NewSpecFactStmt(ast.FalsePure, ast.NewFcAtom(glob.KeySymbolEqual), []ast.Fc{ast.NewFcAtom("y"), ast.NewFcAtom("0")})}, ast.NewFcAtom(glob.KeywordInt))
	env.FcSatisfy_FreeTemplateFact_Store_DeriveFacts(modAtom, modTemplate)

}
