package litexverifier

import (
	"fmt"
	parser "golitex/litex_parser"
)

func (ver *Verifier) UniFact(stmt *parser.UniFactStmt, state VerState) (bool, error) {
	// 默认不允许局部的变量名和外部的变量名冲突了。如果你冲突了，那我报错
	for _, param := range stmt.Params {
		ok, err := ver.isDeclared(param)
		if err != nil {
			return false, verifyStageStmtErr(err, stmt)
		}
		if ok {
			if state.requireMsg() {
				ver.unknownWithMsg("%s is already declared", param)
			}
			return false, nil
		}
	}

	// 在局部环境声明新变量
	ver.newEnv(ver.env, nil)
	defer ver.parentEnv()
	for _, param := range stmt.Params {
		// TODO: nil => concrete stuff
		ver.env.Declare(nil, param)
	}

	// know cond facts
	for _, condFact := range stmt.DomFacts {
		err := ver.env.NewFact(condFact)
		if err != nil {
			return false, err
		}
	}

	// check then facts
	for _, thenFact := range stmt.ThenFacts {
		ok, err := ver.FactStmt(&thenFact, state)
		if err != nil {
			return false, err
		}
		if !ok {
			ver.unknownMsgEnd("%s is unknown", thenFact.String())
			return false, nil
		}
	}

	err := ver.newMsgAtParent(fmt.Sprintf("%s\nis true", stmt.String()))
	if err != nil {
		return false, err
	}
	return true, nil
}
