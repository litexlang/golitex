package litexverifier

// import (
// 	env "golitex/litex_env"
// 	parser "golitex/litex_parser"
// )

// func (ver *Verifier) RelaFact(stmt *parser.RelaFactStmt) (bool, error) {
// 	// TODO:  : If there are symbols inside prop list that have  equals,we loop over all the possible equivalent situations and verify literally

// 	ok, err := ver.RelaFactSpec(stmt)
// 	if err != nil {
// 		return false, err
// 	}
// 	if ok {
// 		return true, nil
// 	}

// 	if !ver.round1() {
// 		return false, nil
// 	}

// 	panic("")
// 	// return verifier.FuncFactCond(stmt)
// }

// func (ver *Verifier) RelaFactSpec(stmt *parser.RelaFactStmt) (bool, error) {
// 	for curEnv := ver.env; curEnv != nil; curEnv = curEnv.Parent {
// 		ok, err := ver.RelaFactSpecAtEnv(curEnv, stmt)
// 		if err != nil {
// 			return false, err
// 		}
// 		if ok {
// 			return true, nil
// 		}
// 	}
// 	return false, nil
// }

// func (ver *Verifier) RelaFactSpecAtEnv(curEnv *env.Env, stmt *parser.RelaFactStmt) (bool, error) {
// 	if string(stmt.Opt.OptName) == parser.KeywordEqual {
// 		return ver.EqualFactSpecAtEnv(curEnv, stmt)
// 	}

// 	panic("not implemented")
// }
