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

package litex_executor

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
	"strconv"
)

func (exec *Executor) proveInRangeStmt(stmt *ast.ProveInRangeStmt) (ExecRet, error) {
	intensionalSetGivenSetIsIn := exec.env.GetIntensionalSet(stmt.IntensionalSet)
	if intensionalSetGivenSetIsIn == nil {
		return NewExecErr(""), fmt.Errorf("intensional set %s not found", stmt.IntensionalSet)
	}

	startStr := strconv.FormatInt(stmt.Start, 10)
	endStr := strconv.FormatInt(stmt.End, 10)

	forallXInIntensionalSetTheyAreFromStartToEnd := ast.NewUniFact([]string{stmt.Param}, []ast.Fc{stmt.IntensionalSet}, []ast.FactStmt{}, []ast.FactStmt{ast.NewInFact(stmt.Param, ast.FcAtom(glob.KeywordInteger)), ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeySymbolLessEqual), []ast.Fc{ast.FcAtom(startStr), ast.FcAtom(stmt.Param)}, stmt.Line), ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeySymbolLess), []ast.Fc{ast.FcAtom(stmt.Param), ast.FcAtom(endStr)}, stmt.Line)}, stmt.Line)

	state, err := exec.factStmt(forallXInIntensionalSetTheyAreFromStartToEnd)
	if notOkExec(state, err) {
		return state, err
	}

	for i := stmt.Start; i < stmt.End; i++ {
		_, msg, err := exec.proveInRangeStmtWhenParamIsIndex(intensionalSetGivenSetIsIn, stmt, i)
		if err != nil {
			if msg != "" {
				exec.newMsg(msg)
			}
			return NewExecErr(""), err
		}
	}

	uniFact := stmt.UniFact()
	err = exec.env.NewFact(uniFact)
	if err != nil {
		return NewExecErr(""), err
	}

	return NewExecTrue(""), nil
}

func (exec *Executor) proveInRangeStmtWhenParamIsIndex(intensionalSetGivenSetIsIn *ast.IntensionalSetStmt, stmt *ast.ProveInRangeStmt, i int64) (bool, string, error) {
	indexAsFc := ast.FcAtom(fmt.Sprintf("%d", i))
	uniMap := map[string]ast.Fc{stmt.Param: indexAsFc}
	exec.NewEnv(exec.env)
	defer exec.deleteEnvAndGiveUpMsgs()

	defObjStmt := ast.NewDefObjStmt([]string{stmt.Param}, []ast.Fc{ast.FcAtom(glob.KeywordInteger)}, []ast.FactStmt{ast.NewEqualFact(ast.FcAtom(stmt.Param), indexAsFc)}, stmt.Line)
	err := exec.defObjStmt(defObjStmt)
	if err != nil {
		return false, "", err
	}

	indexInParamSetFact := ast.NewInFact(stmt.Param, intensionalSetGivenSetIsIn.ParentSet)
	instIndexInParamSetFact, err := indexInParamSetFact.Instantiate(uniMap)
	if err != nil {
		return false, "", err
	}

	execState, err := exec.factStmt(instIndexInParamSetFact)
	if err != nil {
		return false, "", err
	}
	// if notOkExec(execState, err) {
	// 	return false, "", err
	// }

	if execState.IsUnknown() {
		revInstDomFact := instIndexInParamSetFact.(*ast.SpecFactStmt).ReverseIsTrue()
		for _, fact := range revInstDomFact {
			instFact, err := fact.Instantiate(uniMap)
			if err != nil {
				return false, "", err
			}
			execState, err := exec.factStmt(instFact)
			if err != nil {
				return false, "", err
			}
			if execState.IsUnknown() {
				return false, "", fmt.Errorf("index in param set fact must be proved to be true or false, can not be unknown: %s", instFact.String())
			}
		}
		return false, "", fmt.Errorf("index in param set fact must be proved to be true or false, can not be unknown: %s", instIndexInParamSetFact.String())
	}

	for _, domFact := range intensionalSetGivenSetIsIn.Facts {
		instDomFact, err := domFact.Instantiate(uniMap)
		if err != nil {
			return false, "", err
		}
		execState, err := exec.factStmt(instDomFact)
		if err != nil {
			return false, "", err
		}

		if execState.IsUnknown() {
			// 如果 不OK，那必须证明是 false，绝对不能是 unknown
			revInstDomFact := domFact.ReverseIsTrue()
			for _, fact := range revInstDomFact {
				instFact, err := fact.Instantiate(uniMap)
				if err != nil {
					return false, "", err
				}
				execState, err := exec.factStmt(instFact)
				if err != nil {
					return false, "", err
				}
				if execState.IsUnknown() {
					return false, "", fmt.Errorf("dom facts in prove_in_range must be proved to be true or false, can not be unknown: %s", instFact.String())
				}
			}

			return false, "", nil
		}

		err = exec.env.NewFact(domFact)
		if err != nil {
			return false, "", err
		}
	}

	// exec proofs
	for _, curStmt := range stmt.Proofs {
		execState, _, err := exec.Stmt(curStmt)
		if err != nil {
			return false, "", err
		}
		if execState.IsUnknown() {
			// 如果是 fact， 那把数字代入一下，会方便非常多，比如 x > 1 ，把 x = 2直接代入就能直接验证出来了
			curStmtAsFact, err := curStmt.(ast.FactStmt).Instantiate(uniMap)
			if err != nil {
				return false, "", err
			}

			execState, err := exec.factStmt(curStmtAsFact)
			if err != nil {
				return false, "", err
			}
			if execState.IsUnknown() {
				return false, "", fmt.Errorf("proof in prove_in_range must be proved to be true or false, can not be unknown: %s", curStmtAsFact.String())
			}
		}
	}

	// 满足 then
	for _, thenFact := range stmt.ThenFacts {
		instThenFact, err := thenFact.Instantiate(uniMap)
		if err != nil {
			return false, "", err
		}

		execState, err := exec.factStmt(instThenFact)
		if notOkExec(execState, err) {
			return false, "", fmt.Errorf("then fact in prove_in_range must be proved to be true or false, can not be unknown: %s", instThenFact.String())
		}
	}

	return true, "", nil
}
