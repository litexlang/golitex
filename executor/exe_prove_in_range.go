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
)

func (exec *Executor) proveInRangeSetStmt(stmt *ast.ProveInRangeSetStmt) ExecRet {
	panic("not implemented")
	// intensionalSetGivenSetIsIn := exec.Env.GetIntensionalSet(stmt.IntensionalSet)
	// if intensionalSetGivenSetIsIn == nil {
	// 	return NewExecErr(fmt.Sprintf("intensional set %s not found", stmt.IntensionalSet))
	// }

	// startStr := strconv.FormatInt(stmt.Start, 10)
	// endStr := strconv.FormatInt(stmt.End, 10)

	// forallXInIntensionalSetTheyAreFromStartToEnd := ast.NewUniFact([]string{stmt.Param}, []ast.Obj{stmt.IntensionalSet}, []ast.FactStmt{}, []ast.FactStmt{ast.NewInFact(stmt.Param, ast.Atom(glob.KeywordInteger)), ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLessEqual), []ast.Obj{ast.Atom(startStr), ast.Atom(stmt.Param)}, stmt.Line), ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLess), []ast.Obj{ast.Atom(stmt.Param), ast.Atom(endStr)}, stmt.Line)}, stmt.Line)

	// state := exec.factStmt(forallXInIntensionalSetTheyAreFromStartToEnd)
	// if state.IsNotTrue() {
	// 	return state
	// }

	// for i := stmt.Start; i < stmt.End; i++ {
	// 	execRet := exec.proveInRangeSetStmtWhenParamIsIndex(intensionalSetGivenSetIsIn, stmt, i)
	// 	if execRet.IsNotTrue() {
	// 		return execRet
	// 	}
	// }

	// uniFact := stmt.UniFact()
	// ret := exec.Env.NewFact(uniFact)
	// if ret.IsErr() {
	// 	return NewExecErr(ret.String())
	// }

	// return NewExecTrue("")
}

// func (exec *Executor) proveInRangeSetStmtWhenParamIsIndex(intensionalSetGivenSetIsIn *ast.IntensionalSetStmt, stmt *ast.ProveInRangeSetStmt, i int64) ExecRet {
// 	indexAsFc := ast.Atom(fmt.Sprintf("%d", i))
// 	uniMap := map[string]ast.Obj{stmt.Param: indexAsFc}
// 	exec.NewEnv(exec.Env)
// 	defer exec.deleteEnv()

// 	defObjStmt := ast.NewDefLetStmt([]string{stmt.Param}, []ast.Obj{ast.Atom(glob.KeywordInteger)}, []ast.FactStmt{ast.NewEqualFact(ast.Atom(stmt.Param), indexAsFc)}, stmt.Line)
// 	execState := exec.defLetStmt(defObjStmt)
// 	if execState.IsNotTrue() {
// 		return execState
// 	}

// 	indexInParamSetFact := ast.NewInFact(stmt.Param, intensionalSetGivenSetIsIn.ParentSet)
// 	instIndexInParamSetFact, err := indexInParamSetFact.InstantiateFact(uniMap)
// 	if err != nil {
// 		return NewExecErr(err.Error())
// 	}

// 	execState = exec.factStmt(instIndexInParamSetFact)
// 	if execState.IsErr() {
// 		return execState
// 	}
// 	// if notOkExec(execState, err) {
// 	// 	return execState
// 	// }

// 	if execState.IsUnknown() {
// 		revInstDomFact := instIndexInParamSetFact.(*ast.SpecFactStmt).ReverseIsTrue()
// 		for _, fact := range revInstDomFact {
// 			instFact, err := fact.InstantiateFact(uniMap)
// 			if err != nil {
// 				return NewExecErr(err.Error())
// 			}
// 			execState = exec.factStmt(instFact)
// 			if execState.IsErr() {
// 				return execState
// 			}
// 			if execState.IsUnknown() {
// 				return NewExecErr(fmt.Sprintf("index in param set fact must be proved to be true or false, can not be unknown: %s", instFact.String()))
// 			}
// 		}
// 		return NewExecErr(fmt.Sprintf("index in param set fact must be proved to be true or false, can not be unknown: %s", instIndexInParamSetFact.String()))
// 	}

// 	for _, domFact := range intensionalSetGivenSetIsIn.Facts {
// 		instDomFact, err := domFact.InstantiateFact(uniMap)
// 		if err != nil {
// 			return NewExecErr(err.Error())
// 		}
// 		execState := exec.factStmt(instDomFact)
// 		if execState.IsErr() {
// 			return execState
// 		}

// 		if execState.IsUnknown() {
// 			// 如果 不OK，那必须证明是 false，绝对不能是 unknown
// 			revInstDomFact := domFact.ReverseIsTrue()
// 			for _, fact := range revInstDomFact {
// 				instFact, err := fact.InstantiateFact(uniMap)
// 				if err != nil {
// 					return NewExecErr(err.Error())
// 				}
// 				execState = exec.factStmt(instFact)
// 				if execState.IsErr() {
// 					return execState
// 				}
// 				if execState.IsUnknown() {
// 					return NewExecErr(fmt.Sprintf("dom facts in prove_in_range_set must be proved to be true or false, can not be unknown: %s", instFact.String()))
// 				}
// 			}

// 			return NewExecTrue("")
// 		}

// 		ret := exec.Env.NewFact(domFact)
// 		if ret.IsErr() {
// 			return NewExecErr(ret.String())
// 		}
// 	}

// 	// exec proofs
// 	for _, curStmt := range stmt.Proofs {
// 		execState := exec.Stmt(curStmt)
// 		if execState.IsNotTrue() {
// 			return execState
// 		}
// 		if execState.IsUnknown() {
// 			// 如果是 fact， 那把数字代入一下，会方便非常多，比如 x > 1 ，把 x = 2直接代入就能直接验证出来了
// 			curStmtAsFact, err := curStmt.(ast.FactStmt).InstantiateFact(uniMap)
// 			if err != nil {
// 				return NewExecErr(err.Error())
// 			}

// 			execState = exec.factStmt(curStmtAsFact)
// 			if execState.IsErr() {
// 				return execState
// 			}
// 			if execState.IsUnknown() {
// 				return NewExecErr(fmt.Sprintf("proof in prove_in_range_set must be proved to be true or false, can not be unknown: %s", curStmtAsFact.String()))
// 			}
// 		}
// 	}

// 	// 满足 then
// 	for _, thenFact := range stmt.ThenFacts {
// 		instThenFact, err := thenFact.InstantiateFact(uniMap)
// 		if err != nil {
// 			return NewExecErr(err.Error())
// 		}

// 		execState = exec.factStmt(instThenFact)
// 		if execState.IsErr() {
// 			return execState
// 		}
// 		if execState.IsUnknown() {
// 			return NewExecErr(fmt.Sprintf("then fact in prove_in_range_set must be proved to be true or false, can not be unknown: %s", instThenFact.String()))
// 		}
// 	}

// 	return NewExecTrue("")
// }

func (exec *Executor) proveInRangeStmtWhenParamIsIndex(stmt *ast.ProveInRangeStmt, i int64) ExecRet {
	indexAsFc := ast.Atom(fmt.Sprintf("%d", i))
	param := stmt.Param()
	uniMap := map[string]ast.Obj{param: indexAsFc}
	exec.NewEnv(exec.Env)
	defer exec.deleteEnv()

	defObjStmt := ast.NewDefLetStmt([]string{param}, []ast.Obj{ast.Atom(glob.KeywordInteger)}, []ast.FactStmt{ast.NewEqualFact(ast.Atom(param), indexAsFc)}, stmt.GetLine())
	execState := exec.defLetStmt(defObjStmt)
	if execState.IsNotTrue() {
		return execState
	}

	// Check dom facts
	for _, domFact := range stmt.GetDomFactsOrNil() {
		instDomFact, err := domFact.InstantiateFact(uniMap)
		if err != nil {
			return NewExecErr(err.Error())
		}
		execState := exec.factStmt(instDomFact)
		if execState.IsErr() {
			return execState
		}

		if execState.IsUnknown() {
			// 如果 不OK，那必须证明是 false，绝对不能是 unknown
			specFact, ok := domFact.(*ast.SpecFactStmt)
			if !ok {
				return NewExecErr(fmt.Sprintf("dom fact in prove_in_range must be a SpecFactStmt to reverse: %s", domFact.String()))
			}
			revInstDomFact := specFact.ReverseIsTrue()
			for _, fact := range revInstDomFact {
				instFact, err := fact.InstantiateFact(uniMap)
				if err != nil {
					return NewExecErr(err.Error())
				}
				execState = exec.factStmt(instFact)
				if execState.IsErr() {
					return execState
				}
				if execState.IsUnknown() {
					return NewExecErr(fmt.Sprintf("dom facts in prove_in_range must be proved to be true or false, can not be unknown: %s", instFact.String()))
				}
			}

			return NewExecTrue("")
		}

		ret := exec.Env.NewFact(domFact)
		if ret.IsErr() {
			return NewExecErr(ret.String())
		}
	}

	// exec proofs
	for _, curStmt := range stmt.GetProofsOrNil() {
		execState := exec.Stmt(curStmt)
		if execState.IsNotTrue() {
			return execState
		}
		if execState.IsUnknown() {
			// 如果是 fact， 那把数字代入一下，会方便非常多，比如 x > 1 ，把 x = 2直接代入就能直接验证出来了
			curStmtAsFact, ok := curStmt.(ast.FactStmt)
			if ok {
				instFact, err := curStmtAsFact.InstantiateFact(uniMap)
				if err != nil {
					return NewExecErr(err.Error())
				}

				execState = exec.factStmt(instFact)
				if execState.IsErr() {
					return execState
				}
				if execState.IsUnknown() {
					return NewExecErr(fmt.Sprintf("proof in prove_in_range must be proved to be true or false, can not be unknown: %s", instFact.String()))
				}
			} else {
				return NewExecErr(fmt.Sprintf("proof in prove_in_range must be proved to be true or false, can not be unknown: %s", curStmt.String()))
			}
		}
	}

	// 满足 then
	for _, thenFact := range stmt.GetThenFacts() {
		instThenFact, err := thenFact.InstantiateFact(uniMap)
		if err != nil {
			return NewExecErr(err.Error())
		}

		execState = exec.factStmt(instThenFact)
		if execState.IsErr() {
			return execState
		}
		if execState.IsUnknown() {
			return NewExecErr(fmt.Sprintf("then fact in prove_in_range must be proved to be true or false, can not be unknown: %s", instThenFact.String()))
		}
	}

	return NewExecTrue("")
}
