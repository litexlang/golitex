package litexverifier

import (
	parser "golitex/litex_parser"
)

func (ver *Verifier) UniFact(stmt *parser.UniFactStmt) (bool, error) {
	// 默认不允许局部的变量名和外部的变量名冲突了。如果你冲突了，那我报错
	for _, param := range stmt.Params {
		ok, err := ver.isDeclared(param)
		if err != nil {
			return false, err
		}
		if ok {
			ver.unknownWithMsg("%s is already declared", param)
			return false, nil
		}
	}

	// 在局部环境声明新变量
	ver.newEnv(ver.env, nil)
	for _, param := range stmt.Params {
		// TODO: nil => concrete stuff
		ver.env.Declare(nil, param)
	}

	// know cond facts
	for _, condFact := range stmt.ParamCondFacts {
		err := ver.env.NewFact(condFact)
		if err != nil {
			return false, err
		}
	}

	// check then facts
	for _, thenFact := range stmt.ThenFacts {
		ok, err := ver.FactStmt(&thenFact)
		if err != nil {
			return false, nil
		}
		if !ok {
			ver.unknownMsg("%s is unknown", thenFact.String())
			return false, nil
		}
	}

	ver.newMsg("is true")
	return true, nil
}
