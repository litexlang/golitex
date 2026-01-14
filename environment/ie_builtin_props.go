// Copyright Jiachen Shen.
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

package litex_env

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
)

func (ie *InferEngine) notEqualSetFactPostProcess(fact *ast.SpecFactStmt) *glob.ShortRet {
	if len(fact.Params) != 2 {
		return glob.NewShortRet(glob.StmtRetTypeError, []string{fmt.Sprintf("not_equal_set fact expect 2 parameters, get %d in %s", len(fact.Params), fact)})
	}

	derivedFacts := []string{}

	// Create a != b fact
	notEqualFact := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolNotEqual), []ast.Obj{fact.Params[0], fact.Params[1]}, fact.Line)
	ret := ie.EnvMgr.NewFactWithCheckingNameDefined(notEqualFact)
	if ret.IsErr() {
		return glob.ErrStmtMsgToShortRet(ret)
	}
	derivedFacts = append(derivedFacts, notEqualFact.String())

	// Collect any derived facts from the not equal fact
	derivedFacts = append(derivedFacts, ret.Infer...)

	// Derive: exist z x st not z $in y or exist z y st not z $in x
	// We'll create both exist facts and let the inference engine handle the or
	x := fact.Params[0]
	y := fact.Params[1]
	z1 := ie.EnvMgr.GenerateUndeclaredRandomName()
	z2 := ie.EnvMgr.GenerateUndeclaredRandomName()

	// Create exist z1 x st not z1 $in y
	existFact1 := ast.NewExistStFact(
		ast.TrueExist_St,
		ast.Atom(glob.KeywordIn),
		false, // isPropTrue = false means "not z1 $in y"
		[]string{z1},
		[]ast.Obj{x},
		[]ast.Obj{ast.Atom(z1), y},
		fact.Line,
	)

	ret1 := ie.EnvMgr.NewFactWithCheckingNameDefined(existFact1)
	if ret1.IsErr() {
		return glob.ErrStmtMsgToShortRet(ret1)
	}
	derivedFacts = append(derivedFacts, existFact1.String())
	derivedFacts = append(derivedFacts, ret1.Infer...)

	// Create exist z2 y st not z2 $in x
	existFact2 := ast.NewExistStFact(
		ast.TrueExist_St,
		ast.Atom(glob.KeywordIn),
		false, // isPropTrue = false means "not z2 $in x"
		[]string{z2},
		[]ast.Obj{y},
		[]ast.Obj{ast.Atom(z2), x},
		fact.Line,
	)

	ret2 := ie.EnvMgr.NewFactWithCheckingNameDefined(existFact2)
	if ret2.IsErr() {
		return glob.ErrStmtMsgToShortRet(ret2)
	}
	derivedFacts = append(derivedFacts, existFact2.String())
	derivedFacts = append(derivedFacts, ret2.Infer...)

	return glob.NewShortRet(glob.StmtRetTypeTrue, derivedFacts)
}
