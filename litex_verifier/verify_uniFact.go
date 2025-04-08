package litex_verifier

import (
	"fmt"
	ast "golitex/litex_ast"
)

func (ver *Verifier) UniFact(stmt *ast.ConUniFactStmt, state VerState) (bool, error) {
	// 默认不允许局部的变量名和外部的变量名冲突了。如果你冲突了，那我报错
	for _, param := range stmt.Params {
		err := ver.env.IsInvalidName(ver.env.CurPkg, param)
		if err != nil {
			return false, verifyStageStmtErr(err, stmt)
		}
	}

	// 在局部环境声明新变量
	ver.newEnv(nil)
	defer ver.deleteEnvAndRetainMsg()
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
		ok, err := ver.FactStmt(thenFact, state) // 这个地方有点tricky，这里是可能读入state是any的，而且我要允许读入any
		if err != nil {
			return false, err
		}
		if !ok {
			ver.unknownMsgEnd("%s is unknown", thenFact.String())
			return false, nil
		}

		// if true, store it
		err = ver.env.NewFact(thenFact)
		if err != nil {
			return false, err
		}
	}

	if state.requireMsg() {
		err := ver.newMsgAtParent(fmt.Sprintf("%s\nis true", stmt.String()))
		if err != nil {
			return false, err
		}
	}

	return true, nil
}

// func (ver *Verifier) UniFact(stmt *ast.ConUniFactStmt, state VerState) (bool, error) {
// 	// 默认不允许局部的变量名和外部的变量名冲突了。如果你冲突了，那我报错
// 	for _, param := range stmt.Params {
// 		err := ver.env.IsInvalidName(ver.env.CurPkg, param)
// 		if err != nil {
// 			return false, verifyStageStmtErr(err, stmt)
// 		}
// 	}

// 	// 在局部环境声明新变量
// 	ver.newEnv(nil)
// 	defer ver.deleteEnvAndRetainMsg()
// 	for _, param := range stmt.Params {
// 		// TODO: nil => concrete stuff
// 		ver.env.Declare(nil, param)
// 	}

// 	// know cond facts
// 	for _, condFact := range stmt.DomFacts {
// 		err := ver.env.NewFact(condFact)
// 		if err != nil {
// 			return false, err
// 		}
// 	}

// 	// check then facts
// 	for _, thenFact := range stmt.ThenFacts {
// 		ok, err := ver.FactStmt(thenFact, state) // 这个地方有点tricky，这里是可能读入state是any的，而且我要允许读入any
// 		if err != nil {
// 			return false, err
// 		}
// 		if !ok {
// 			ver.unknownMsgEnd("%s is unknown", thenFact.String())
// 			return false, nil
// 		}

// 		// if true, store it
// 		err = ver.env.NewFact(thenFact)
// 		if err != nil {
// 			return false, err
// 		}
// 	}

// 	if state.requireMsg() {
// 		err := ver.newMsgAtParent(fmt.Sprintf("%s\nis true", stmt.String()))
// 		if err != nil {
// 			return false, err
// 		}
// 	}

// 	return true, nil
// }
