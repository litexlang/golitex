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

package litex_executor

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
)

func (exec *Executor) implyTemplateStmt(stmt *ast.ImplyTemplateStmt) *glob.StmtRet {
	// Step 1: Verify like claim forall
	execRet := exec.implyTemplateStmtVerify(stmt)
	if execRet.IsNotTrue() {
		return execRet
	}

	// Step 2: Store facts in SpecFactInImplyTemplateMem
	execRet = exec.implyTemplateStmtStore(stmt)
	if execRet.IsNotTrue() {
		return execRet
	}

	return execRet
}

func (exec *Executor) implyTemplateStmtVerify(stmt *ast.ImplyTemplateStmt) *glob.StmtRet {
	exec.NewEnv()
	defer func() {
		exec.deleteEnv()
	}()

	innerStmtRets := []*glob.StmtRet{}

	// Declare parameters in the env
	objDefStmt := ast.NewDefLetStmt(stmt.Params, stmt.ParamSets, []ast.FactStmt{}, stmt.Line)

	execState := exec.defLetStmt(objDefStmt)
	if execState.IsNotTrue() {
		return execState.AddError(fmt.Sprintf("ImplyTemplate statement error: Failed to declare parameters:\n%s\n", objDefStmt))
	}
	innerStmtRets = append(innerStmtRets, execState)

	// Know dom facts
	for _, domFact := range stmt.DomFacts {
		// Convert Spec_OrFact to FactStmt
		var factStmt ast.FactStmt
		if specFact, ok := domFact.(*ast.SpecFactStmt); ok {
			factStmt = specFact
		} else if orStmt, ok := domFact.(*ast.OrStmt); ok {
			factStmt = orStmt
		} else {
			return glob.ErrRet(fmt.Sprintf("implyTemplate statement error: unsupported fact type in domFacts: %T", domFact))
		}
		ret := exec.Env.NewFactWithCheckingNameDefined(factStmt)
		if ret.IsErr() {
			return glob.ErrRet(ret.String())
		}
	}

	// Execute proof block if present
	if len(stmt.Proof) > 0 {
		execState = exec.execStmtsAtCurEnv(stmt.Proof)
		if execState.IsNotTrue() {
			return execState
		}
		innerStmtRets = append(innerStmtRets, execState.InnerStmtRetSlice...)
	}

	// Verify thenFacts
	thenFactsAsFactStmt := make([]ast.FactStmt, len(stmt.ThenFacts))
	for i, fact := range stmt.ThenFacts {
		// Convert Spec_OrFact to FactStmt
		if specFact, ok := fact.(*ast.SpecFactStmt); ok {
			thenFactsAsFactStmt[i] = specFact
		} else if orStmt, ok := fact.(*ast.OrStmt); ok {
			thenFactsAsFactStmt[i] = orStmt
		} else {
			return glob.ErrRet(fmt.Sprintf("implyTemplate statement error: unsupported fact type in thenFacts: %T", fact))
		}
	}

	execState, failedFact, err := exec.verifyFactsAtCurEnv(thenFactsAsFactStmt, Round0NoMsg())
	if err != nil {
		return glob.ErrRet(fmt.Sprintf("implyTemplate statement error: failed to verify fact:\n%s\n%s", failedFact, err))
	} else if execState.IsUnknown() {
		return glob.ErrRet(fmt.Sprintf("implyTemplate statement error: failed to verify fact:\n%s", failedFact))
	}

	return glob.NewStmtWithInnerStmtsRet(innerStmtRets, glob.StmtRetTypeTrue)
}

func (exec *Executor) implyTemplateStmtStore(stmt *ast.ImplyTemplateStmt) *glob.StmtRet {
	// Store each thenFact in appropriate memory
	for _, thenFact := range stmt.ThenFacts {
		if specFact, ok := thenFact.(*ast.SpecFactStmt); ok {
			// Store SpecFactStmt in SpecFactInImplyTemplateMem
			ret := exec.Env.StoreSpecFactInImplyTemplateMem(specFact, stmt)
			if ret.IsErr() {
				return ret
			}
		} else if orStmt, ok := thenFact.(*ast.OrStmt); ok {
			// Store OrStmt in SpecFact_InLogicExpr_InImplyTemplateMem
			ret := exec.Env.StoreSpecFactInImplyTemplateMem(orStmt.Facts[0], stmt)
			if ret.IsErr() {
				return ret
			}
		} else {
			return glob.ErrRet(fmt.Sprintf("implyTemplate statement error: unsupported fact type in thenFacts: %T", thenFact))
		}
	}

	return glob.NewEmptyStmtTrue()
}
