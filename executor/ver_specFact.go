package litex_executor

import (
	"fmt"
	ast "golitex/ast"
	cmp "golitex/cmp"
	glob "golitex/glob"
)

func (ver *Verifier) verSpecFactNotInFormOfTrueEqualAndCheckFnReq(stmt *ast.SpecFactStmt, state *VerState) *glob.VerRet {
	if !state.ReqOk {
		if verRet := ver.checkFnsReq(stmt, state); verRet.IsErr() || verRet.IsUnknown() {
			return verRet
		}

		state.UpdateReqOkToTrue()
	}

	ret := ver.verSpecFactWholeProcess(stmt, state)
	if ret.IsTrue() || ret.IsErr() {
		return ret
	}

	return glob.NewVerMsg(glob.StmtRetTypeUnknown, stmt.String(), glob.BuiltinLine0, []string{})
}

func (ver *Verifier) verSpecFactPreProcess(stmt *ast.SpecFactStmt, state *VerState) *glob.VerRet {
	verRet := ver.verSpecFactPreProcess_ReplaceSymbolsWithValues(stmt, state)
	if verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) verSpecFactPostProcess(stmt *ast.SpecFactStmt, state *VerState) *glob.VerRet {
	verRet := ver.verSpecFactPostProcess_UseCommutativity(stmt, state)
	if verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	verRet = ver.verSpecFactPostProcess_UseTransitivity(stmt, state)
	if verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	verRet = ver.verSpecFactPostProcess_WhenPropIsComparison(stmt, state)
	if verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) verSpecFactMainProcess(stmt *ast.SpecFactStmt, state *VerState) *glob.VerRet {
	if verRet := ver.verSpecFactByBuiltinRules(stmt, state); verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	if verRet := ver.verSpecFact_BySpecMem(stmt, state); verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	if verRet := ver.verSpecFact_ByDEF(stmt, state); verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	if !state.isFinalRound() {
		if verRet := ver.verSpecFact_ByLogicMem(stmt, state); verRet.IsErr() || verRet.IsTrue() {
			return verRet
		}

		if verRet := ver.verSpecFact_UniMem(stmt, state); verRet.IsErr() || verRet.IsTrue() {
			return verRet
		}
	}

	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) verSpecFactWholeProcess(stmt *ast.SpecFactStmt, state *VerState) *glob.VerRet {
	verRet := ver.verSpecFactPreProcess(stmt, state)
	if verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	verRet = ver.verSpecFactMainProcess(stmt, state)
	if verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	verRet = ver.verSpecFactPostProcess(stmt, state)
	if verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) verSpecFactByMainProcessAndPostProcess(stmt *ast.SpecFactStmt, state *VerState) *glob.VerRet {
	verRet := ver.verSpecFactMainProcess(stmt, state)
	if verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	verRet = ver.verSpecFactPostProcess(stmt, state)
	if verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) verSpecFactPreProcess_ReplaceSymbolsWithValues(stmt *ast.SpecFactStmt, state *VerState) *glob.VerRet {
	replaced, newStmt := ver.Env.ReplaceObjInSpecFactWithValue(stmt)
	if replaced {
		verRet := ver.verSpecFactByMainProcessAndPostProcess(newStmt, state)
		if verRet.IsErr() {
			return verRet
		}
		if verRet.IsTrue() {
			msg := fmt.Sprintf("%s is equivalent to %s by replacing the symbols with their values", stmt.String(), newStmt.String())
			if state.WithMsg {
				return glob.NewVerMsg(glob.StmtRetTypeTrue, stmt.String(), glob.BuiltinLine0, []string{msg})
			}
			return glob.NewEmptyVerRetTrue()
		}
	}

	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) verSpecFactPreProcessAndMainProcess(stmt *ast.SpecFactStmt, state *VerState) *glob.VerRet {
	verRet := ver.verSpecFactPreProcess(stmt, state)
	if verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	verRet = ver.verSpecFactMainProcess(stmt, state)
	if verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) verSpecFactPostProcess_UseCommutativity(stmt *ast.SpecFactStmt, state *VerState) *glob.VerRet {
	if ver.Env.IsCommutativeProp(stmt) {
		reverseParamsOrderStmt, err := stmt.ReverseParameterOrder()
		if err != nil {
			return glob.NewVerMsg(glob.StmtRetTypeError, stmt.String(), glob.BuiltinLine0, []string{err.Error()})
		}

		verRet := ver.verSpecFactPreProcessAndMainProcess(reverseParamsOrderStmt, state)
		if verRet.IsErr() || verRet.IsTrue() {
			return verRet
		}

		return glob.NewEmptyVerRetUnknown()
	}

	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) verSpecFactPostProcess_UseTransitivity(stmt *ast.SpecFactStmt, state *VerState) *glob.VerRet {
	if stmt.FactType == ast.TruePure && ver.Env.IsTransitiveProp(string(stmt.PropName)) {
		relatedObjSlice := ver.Env.GetRelatedObjSliceOfTransitiveProp(string(stmt.PropName), stmt.Params[0])
		if len(relatedObjSlice) == 0 {
			return glob.NewEmptyVerRetUnknown()
		}

		for _, relatedObj := range relatedObjSlice {
			relatedObjStmt := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(stmt.PropName), []ast.Obj{relatedObj, stmt.Params[1]}, stmt.Line)
			verRet := ver.verSpecFactPreProcessAndMainProcess(relatedObjStmt, state)
			if verRet.IsErr() {
				return verRet
			}
			if verRet.IsTrue() {
				msg := fmt.Sprintf("%s is true by %s is a transitive prop and %s is true", stmt.String(), string(stmt.PropName), relatedObjStmt.String())
				if state.WithMsg {
					return glob.NewVerMsg(glob.StmtRetTypeTrue, stmt.String(), glob.BuiltinLine0, []string{msg})
				}
				return glob.NewEmptyVerRetTrue()
			}
		}
	}

	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) verSpecFactPostProcess_WhenPropIsComparison(stmt *ast.SpecFactStmt, state *VerState) *glob.VerRet {
	if ast.IsTrueSpecFactWithPropName(stmt, glob.KeySymbolGreater) {
		// a > b <=> b < a
		lessThanStmt := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLess), []ast.Obj{stmt.Params[1], stmt.Params[0]}, stmt.Line)
		verRet := ver.verSpecFactPreProcessAndMainProcess(lessThanStmt, state)
		if verRet.IsErr() || verRet.IsTrue() {
			return verRet
		}

		return glob.NewEmptyVerRetUnknown()
	} else if ast.IsTrueSpecFactWithPropName(stmt, glob.KeySymbolLess) {
		// a < b <=> b > a
		greaterThanStmt := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolGreater), []ast.Obj{stmt.Params[1], stmt.Params[0]}, stmt.Line)
		verRet := ver.verSpecFactPreProcessAndMainProcess(greaterThanStmt, state)
		if verRet.IsErr() || verRet.IsTrue() {
			return verRet
		}

		return glob.NewEmptyVerRetUnknown()
	} else if ast.IsTrueSpecFactWithPropName(stmt, glob.KeySymbolLargerEqual) {
		// a >= b <=> b <= a
		lessEqualThanStmt := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLessEqual), []ast.Obj{stmt.Params[1], stmt.Params[0]}, stmt.Line)
		verRet := ver.verSpecFactPreProcessAndMainProcess(lessEqualThanStmt, state)
		if verRet.IsErr() || verRet.IsTrue() {
			return verRet
		}

		return glob.NewEmptyVerRetUnknown()
	} else if ast.IsTrueSpecFactWithPropName(stmt, glob.KeySymbolLessEqual) {
		// a <= b <=> b >= a
		greaterEqualThanStmt := ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolLargerEqual), []ast.Obj{stmt.Params[1], stmt.Params[0]}, stmt.Line)
		verRet := ver.verSpecFactPreProcessAndMainProcess(greaterEqualThanStmt, state)
		if verRet.IsErr() || verRet.IsTrue() {
			return verRet
		}

		return glob.NewEmptyVerRetUnknown()
	}

	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) verSpecFact_UniMem(stmt *ast.SpecFactStmt, state *VerState) *glob.VerRet {
	nextState := state.GetAddRound()

	verRet := ver.verSpecFact_InSpecFact_UniMem(stmt, nextState)
	if verRet.IsErr() || verRet.IsTrue() {
		return verRet
	}

	return ver.verSpecFact_InLogicExpr_InUniFactMem(stmt, nextState)
}

func (ver *Verifier) verNotTrueEqualFact_BuiltinRules_WithState(stmt *ast.SpecFactStmt, state *VerState) *glob.VerRet {
	if stmt.IsTrue() {
		return glob.NewEmptyVerRetUnknown()
	}

	// 如果右侧是0，且左边是减号，那就证明左边这两个东西不等
	// if ret := ver.whenRightIsZeroAndLeftFnIsMinus(stmt, state); ret.IsNotUnknown() {
	// 	return ret
	// }

	var leftValue, rightValue ast.Obj
	if cmp.IsNumExprLitObj(stmt.Params[0]) {
		leftValue = stmt.Params[0]
	} else {
		leftValue = ver.Env.GetSymbolSimplifiedValue(stmt.Params[0])
		if leftValue == nil {
			return glob.NewEmptyVerRetUnknown()
		}
	}
	if cmp.IsNumExprLitObj(stmt.Params[1]) {
		rightValue = stmt.Params[1]
	} else {
		rightValue = ver.Env.GetSymbolSimplifiedValue(stmt.Params[1])
		if rightValue == nil {
			return glob.NewEmptyVerRetUnknown()
		}
	}

	_, areEqual, err := cmp.NumLitEqual_ByEval(leftValue, rightValue)
	if err != nil {
		return glob.NewVerMsg(glob.StmtRetTypeError, stmt.String(), glob.BuiltinLine0, []string{err.Error()})
	}
	if !areEqual {
		if state != nil && state.WithMsg {
			return glob.NewVerMsg(glob.StmtRetTypeTrue, stmt.String(), glob.BuiltinLine0, []string{"builtin rules"})
		}
		return glob.NewEmptyVerRetTrue()
	}

	// // 如果左右两边能是能被处理的数字
	// areBothNumLit, areEqual, err := cmp.NumLitEqual_ByEval(stmt.Params[0], stmt.Params[1])
	// if err != nil {
	// 	return glob.ErrRet(err.Error())
	// }
	// if areBothNumLit {
	// 	if !areEqual { // 这里是在证明两边不相等
	// 		ver.processOkMsg(state, stmt.String(), "builtin rules")
	// 		return NewExecEmptyTrue()
	// 	}
	// }

	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) verIsCartByBuiltinRules(stmt *ast.SpecFactStmt, state *VerState) *glob.VerRet {
	// 如果参数数量是1，且参数的函数名是cart，那自动成立
	if len(stmt.Params) == 1 {
		if cartObj, ok := stmt.Params[0].(*ast.FnObj); ok && ast.IsAtomObjAndEqualToStr(cartObj.FnHead, glob.KeywordCart) {
			if state.WithMsg {
				return glob.NewVerMsg(glob.StmtRetTypeTrue, stmt.String(), glob.BuiltinLine0, []string{"definition"})
			}
			return glob.NewEmptyVerRetTrue()
		}
	}
	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) verNotPureSpecFact_ByDef(stmt *ast.SpecFactStmt, state *VerState) *glob.VerRet {
	nextState := state.GetAddRound()

	curDefinedStuff, ok := ver.Env.GetPropDef(stmt.PropName)
	if !ok {
		// 这里可能是因为这个propName是exist prop，所以没有定义
		return glob.NewEmptyVerRetUnknown()
	}

	defStmt := curDefinedStuff.Defined

	if len(defStmt.IffFactsOrNil) == 0 {
		// REMARK: 如果IFFFacts不存在，那我们认为是 没有iff能验证prop，而不是prop自动成立
		return glob.NewEmptyVerRetUnknown()
	}

	iffToProp := defStmt.IffToPropUniFact()
	paramArrMap := map[string]ast.Obj{}
	for i, param := range stmt.Params {
		paramArrMap[defStmt.DefHeader.Params[i]] = param
	}

	// TODO: ? 这里还需要检查吗？或者说是在这里检查吗？难道prop的关于参数的检查不应该在更顶层的函数里？
	paramSetFacts, err := defStmt.DefHeader.GetInstantiatedParamInParamSetFact(paramArrMap)
	if err != nil {
		return glob.NewVerMsg(glob.StmtRetTypeError, stmt.String(), glob.BuiltinLine0, []string{err.Error()})
	}

	for _, paramSetFact := range paramSetFacts {
		verRet := ver.VerFactStmt(paramSetFact, state)
		if verRet.IsErr() || verRet.IsUnknown() {
			return verRet
		}
	}

	// 本质上不需要把所有的参数都instantiate，只需要instantiate在dom里的就行
	instantiatedIffToProp, err := ast.InstantiateUniFact(iffToProp, paramArrMap)
	if err != nil {
		return glob.NewVerMsg(glob.StmtRetTypeError, stmt.String(), glob.BuiltinLine0, []string{err.Error()})
	}

	// 某个fact是false的，那就OK了
	for _, domFact := range instantiatedIffToProp.DomFacts {
		domFactAsSpecFact, ok := domFact.(*ast.SpecFactStmt)
		if !ok {
			continue
		}
		reversedDomFact := domFactAsSpecFact.ReverseTrue()

		verRet := ver.VerFactStmt(reversedDomFact, nextState)
		if verRet.IsErr() {
			return verRet
		}
		if verRet.IsTrue() {
			if state.WithMsg {
				return glob.NewVerMsg(glob.StmtRetTypeTrue, stmt.String(), glob.BuiltinLine0, []string{defStmt.String()})
			}
			return glob.NewEmptyVerRetTrue()
		}
	}

	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) verSpecFact_ByDEF(stmt *ast.SpecFactStmt, state *VerState) *glob.VerRet {
	if stmt.IsPureFact() {
		if !stmt.IsTrue() {
			return ver.verNotPureSpecFact_ByDef(stmt, state)
		}

		return ver.verPureSpecFact_ByDefinition(stmt, state)
	}

	// if stmt.IsExist_St_Fact() {
	// 	return ver.verExistSpecFact_ByDefinition(stmt, state)
	// }

	return glob.NewEmptyVerRetUnknown()
}

func (ver *Verifier) verPureSpecFact_ByDefinition(stmt *ast.SpecFactStmt, state *VerState) *glob.VerRet {
	// nextState := state.GetAddRound()

	curDefinedStuff, ok := ver.Env.GetPropDef(stmt.PropName)
	// defStmt := curDefStmt
	if !ok {
		// 这里可能是因为这个propName是exist prop，所以没有定义
		return glob.NewEmptyVerRetUnknown()
	}

	curDefStmt := curDefinedStuff.Defined

	if len(curDefStmt.IffFactsOrNil) == 0 {
		// REMARK: 如果IFFFacts不存在，那我们认为是 没有iff能验证prop，而不是prop自动成立
		return glob.NewEmptyVerRetUnknown()
	}

	defStmt := ver.Env.MakeUniFactParamsInThisDefPropDoNotConflictWithEnv(curDefStmt)

	iffToProp := defStmt.IffToPropUniFact()
	paramArrMap := map[string]ast.Obj{}
	for i, param := range stmt.Params {
		paramArrMap[defStmt.DefHeader.Params[i]] = param
	}

	// TODO: ? 这里还需要检查吗？或者说是在这里检查吗？难道prop的关于参数的检查不应该在更顶层的函数里？
	paramSetFacts, err := defStmt.DefHeader.GetInstantiatedParamInParamSetFact(paramArrMap)
	if err != nil {
		return glob.NewVerMsg(glob.StmtRetTypeError, stmt.String(), glob.BuiltinLine0, []string{err.Error()})
	}

	for _, paramSetFact := range paramSetFacts {
		verRet := ver.VerFactStmt(paramSetFact, state)
		if verRet.IsErr() || verRet.IsUnknown() {
			return verRet
		}
	}

	// 本质上不需要把所有的参数都instantiate，只需要instantiate在dom里的就行
	instantiatedIffToProp, err := ast.InstantiateUniFact(iffToProp, paramArrMap)
	if err != nil {
		return glob.NewVerMsg(glob.StmtRetTypeError, stmt.String(), glob.BuiltinLine0, []string{err.Error()})
	}
	// prove all domFacts are true
	for _, domFact := range instantiatedIffToProp.DomFacts {
		// verRet := ver.VerFactStmt(domFact, nextState)
		verRet := ver.VerFactStmt(domFact, state)
		if verRet.IsErr() || verRet.IsUnknown() {
			return verRet
		}
	}

	if state.WithMsg {
		return glob.NewVerMsg(glob.StmtRetTypeTrue, stmt.String(), glob.BuiltinLine0, []string{defStmt.String()})
	}
	return glob.NewEmptyVerRetTrue()
}
