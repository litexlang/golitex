package litex_executor

import (
	ast "golitex/ast"
)

func (ver *Verifier) UseBuiltinRulesForSpecialSpecFact(stmt *ast.SpecFactStmt, state *VerState) ExecRet {
	return NewExecUnknown("")
	// // 如果是 >=，验证 > 或 =
	// if stmt.NameIs(glob.KeySymbolLargerEqual) && stmt.TypeEnum == ast.TruePure {
	// 	if len(stmt.Params) != 2 {
	// 		return BoolErrToExecRet(false, nil)
	// 	}

	// 	// 验证 >
	// 	greaterStmt := ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeySymbolGreater), stmt.Params, stmt.Line)
	// 	verRet := ver.VerFactStmt(greaterStmt, state)
	// 	if verRet.IsTrue() {
	// 		msg := fmt.Sprintf("%s is true by builtin rule: %s >= %s is true if %s > %s is true", stmt.String(), stmt.Params[0].String(), stmt.Params[1].String(), stmt.Params[0].String(), stmt.Params[1].String())
	// 		return ver.maybeAddSuccessMsg(state, stmt.String(), msg, NewExecTrue(msg))
	// 	}
	// 	if verRet.IsErr() {
	// 		return verRet
	// 	}

	// 	// 验证 =
	// 	equalStmt := ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeySymbolEqual), stmt.Params, stmt.Line)
	// 	verRet = ver.VerFactStmt(equalStmt, state)
	// 	if verRet.IsTrue() {
	// 		msg := fmt.Sprintf("%s is true by builtin rule: %s >= %s is true if %s = %s is true", stmt.String(), stmt.Params[0].String(), stmt.Params[1].String(), stmt.Params[0].String(), stmt.Params[1].String())
	// 		return ver.maybeAddSuccessMsg(state, stmt.String(), msg, NewExecTrue(msg))
	// 	}
	// 	if verRet.IsErr() {
	// 		return verRet
	// 	}

	// 	return BoolErrToExecRet(false, nil)
	// }

	// // 如果是 <=，验证 < 或 =
	// if stmt.NameIs(glob.KeySymbolLessEqual) && stmt.TypeEnum == ast.TruePure {
	// 	if len(stmt.Params) != 2 {
	// 		return BoolErrToExecRet(false, nil)
	// 	}

	// 	// 验证 <
	// 	lessStmt := ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeySymbolLess), stmt.Params, stmt.Line)
	// 	verRet := ver.VerFactStmt(lessStmt, state)
	// 	if verRet.IsTrue() {
	// 		msg := fmt.Sprintf("%s is true by builtin rule: %s <= %s is true if %s < %s is true", stmt.String(), stmt.Params[0].String(), stmt.Params[1].String(), stmt.Params[0].String(), stmt.Params[1].String())
	// 		return ver.maybeAddSuccessMsg(state, stmt.String(), msg, NewExecTrue(msg))
	// 	}
	// 	if verRet.IsErr() {
	// 		return verRet
	// 	}

	// 	// 验证 =
	// 	equalStmt := ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeySymbolEqual), stmt.Params, stmt.Line)
	// 	verRet = ver.VerFactStmt(equalStmt, state)
	// 	if verRet.IsTrue() {
	// 		msg := fmt.Sprintf("%s is true by builtin rule: %s <= %s is true if %s = %s is true", stmt.String(), stmt.Params[0].String(), stmt.Params[1].String(), stmt.Params[0].String(), stmt.Params[1].String())
	// 		return ver.maybeAddSuccessMsg(state, stmt.String(), msg, NewExecTrue(msg))
	// 	}
	// 	if verRet.IsErr() {
	// 		return verRet
	// 	}

	// 	return BoolErrToExecRet(false, nil)
	// }

	// if stmt.NameIs(glob.KeySymbolEqual) && stmt.TypeEnum == ast.FalsePure {
	// 	if len(stmt.Params) != 2 {
	// 		return BoolErrToExecRet(false, nil)
	// 	}

	// 	lessStmt := ast.NewSpecFactStmt(ast.FalsePure, ast.FcAtom(glob.KeySymbolLess), stmt.Params, stmt.Line)
	// 	verRet := ver.VerFactStmt(lessStmt, state)
	// 	if verRet.IsTrue() {
	// 		msg := fmt.Sprintf("%s is true by builtin rule: %s != %s is true if %s < %s is false", stmt.String(), stmt.Params[0].String(), stmt.Params[1].String(), stmt.Params[0].String(), stmt.Params[1].String())
	// 		return ver.maybeAddSuccessMsg(state, stmt.String(), msg, NewExecTrue(msg))
	// 	}
	// 	if verRet.IsErr() {
	// 		return verRet
	// 	}

	// 	greaterStmt := ast.NewSpecFactStmt(ast.FalsePure, ast.FcAtom(glob.KeySymbolGreater), stmt.Params, stmt.Line)
	// 	verRet = ver.VerFactStmt(greaterStmt, state)
	// 	if verRet.IsTrue() {
	// 		msg := fmt.Sprintf("%s is true by builtin rule: %s != %s is true if %s > %s is false", stmt.String(), stmt.Params[0].String(), stmt.Params[1].String(), stmt.Params[0].String(), stmt.Params[1].String())
	// 		return ver.maybeAddSuccessMsg(state, stmt.String(), msg, NewExecTrue(msg))
	// 	}
	// 	if verRet.IsErr() {
	// 		return verRet
	// 	}

	// 	return BoolErrToExecRet(false, nil)
	// }

	// return BoolErrToExecRet(false, nil)
}
