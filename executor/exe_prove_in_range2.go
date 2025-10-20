// // Copyright 2024 Jiachen Shen.
// //
// // Licensed under the Apache License, Version 2.0 (the "License");
// // you may not use this file except in compliance with the License.
// // You may obtain a copy of the License at
// //
// //     http://www.apache.org/licenses/LICENSE-2.0
// //
// // Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// // Litex email: <litexlang@outlook.com>
// // Litex website: https://litexlang.com
// // Litex github repository: https://github.com/litexlang/golitex
// // Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_executor

// import (
// 	"fmt"
// 	ast "golitex/ast"
// 	glob "golitex/glob"
// )

// func (exec *Executor) proveInRangeStmt2(stmt *ast.ProveInRange2tmt) (glob.ExecState, error) {
// 	for i := stmt.Start; i < stmt.End; i++ {
// 		_, msg, err := exec.proveInRangeStmtWhenParamIsIndex2(stmt, i)
// 		if err != nil {
// 			if msg != "" {
// 				exec.newMsg(msg)
// 			}
// 			return glob.ExecStateError, err
// 		}
// 	}

// 	uniFact := stmt.UniFact()
// 	err := exec.env.NewFact(uniFact)
// 	if err != nil {
// 		return glob.ExecStateError, err
// 	}

// 	return glob.ExecStateTrue, nil
// }

// func (exec *Executor) proveInRangeStmtWhenParamIsIndex2(stmt *ast.ProveInRange2tmt, i int64) (bool, string, error) {
// 	indexAsFc := ast.FcAtom(fmt.Sprintf("%d", i))
// 	uniMap := map[string]ast.Fc{stmt.Param: indexAsFc}
// 	exec.NewEnv(exec.env)
// 	defer exec.deleteEnvAndGiveUpMsgs()

// 	defObjStmt := ast.NewDefObjStmt([]string{stmt.Param}, []ast.Fc{ast.FcAtom(glob.KeywordInteger)}, []ast.FactStmt{ast.NewEqualFact(ast.FcAtom(stmt.Param), indexAsFc)}, stmt.Line)
// 	err := exec.defObjStmt(defObjStmt)
// 	if err != nil {
// 		return false, "", err
// 	}

// 	for _, domFact := range stmt.DomFacts {
// 		instDomFact, err := domFact.Instantiate(uniMap)
// 		if err != nil {
// 			return false, "", err
// 		}
// 		execState, err := exec.factStmt(instDomFact)
// 		if err != nil {
// 			return false, "", err
// 		}

// 		if execState != glob.ExecStateTrue {
// 			// 如果 不OK，那必须证明是 false，绝对不能是 unknown
// 			revInstDomFact := domFact.ReverseIsTrue()
// 			for _, fact := range revInstDomFact {
// 				instFact, err := fact.Instantiate(uniMap)
// 				if err != nil {
// 					return false, "", err
// 				}
// 				execState, err := exec.factStmt(instFact)
// 				if err != nil {
// 					return false, "", err
// 				}
// 				if execState != glob.ExecStateTrue {
// 					return false, "", fmt.Errorf("dom facts in prove_in_range must be proved to be true or false, can not be unknown: %s", instFact.String())
// 				}
// 			}

// 			return false, "", nil
// 		}

// 		err = exec.env.NewFact(domFact)
// 		if err != nil {
// 			return false, "", err
// 		}
// 	}

// 	// exec proofs
// 	for _, curStmt := range stmt.Proofs {
// 		execState, _, err := exec.Stmt(curStmt)
// 		if err != nil {
// 			return false, "", err
// 		}
// 		if execState != glob.ExecStateTrue {
// 			// 如果是 fact， 那把数字代入一下，会方便非常多，比如 x > 1 ，把 x = 2直接代入就能直接验证出来了
// 			curStmtAsFact, err := curStmt.(ast.FactStmt).Instantiate(uniMap)
// 			if err != nil {
// 				return false, "", err
// 			}

// 			execState, err := exec.factStmt(curStmtAsFact)
// 			if err != nil {
// 				return false, "", err
// 			}
// 			if execState != glob.ExecStateTrue {
// 				return false, "", fmt.Errorf("proof in prove_in_range must be proved to be true or false, can not be unknown: %s", curStmtAsFact.String())
// 			}
// 		}
// 	}

// 	return true, "", nil
// }
