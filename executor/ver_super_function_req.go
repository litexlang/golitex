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

func (ver *Verifier) verSuperFunctionReq(fnObj *ast.FnObj, state *VerState) *glob.VerRet {
	switch fnObj.FnHead.String() {
	case glob.KeywordUnion:
		return ver.verUnionReq(fnObj, state)
	case glob.KeywordIntersect:
		return ver.verIntersectReq(fnObj, state)
	case glob.KeywordPowerSet:
		return ver.verPowerSetReq(fnObj, state)
	case glob.KeywordCup:
		return ver.verCupReq(fnObj, state)
	case glob.KeywordCap:
		return ver.verCapReq(fnObj, state)
	case glob.KeywordSetMinus:
		return ver.verSetMinusReq(fnObj, state)
	case glob.KeywordSetDiff:
		return ver.verSymmetricDifferenceReq(fnObj, state)
	case glob.KeywordProj:
		return ver.verProjReq(fnObj, state)
	case glob.KeywordDim:
		return ver.verDimReq(fnObj, state)

	default:
		return glob.NewVerMsg(glob.StmtRetTypeError, fnObj.String(), 0, []string{fmt.Sprintf("unknown super function: %s", fnObj.FnHead)})
	}
}

func (ver *Verifier) verUnionReq(fnObj *ast.FnObj, state *VerState) *glob.VerRet {
	if len(fnObj.Params) != 2 {
		return glob.NewVerMsg(glob.StmtRetTypeError, fnObj.String(), 0, []string{fmt.Sprintf("union expects 2 parameters, got %d", len(fnObj.Params))})
	}

	_ = state

	return glob.NewEmptyVerRetTrue()
}

func (ver *Verifier) verIntersectReq(fnObj *ast.FnObj, state *VerState) *glob.VerRet {
	if len(fnObj.Params) != 2 {
		return glob.NewVerMsg(glob.StmtRetTypeError, fnObj.String(), 0, []string{fmt.Sprintf("intersect expects 2 parameters, got %d", len(fnObj.Params))})
	}

	_ = state

	return glob.NewEmptyVerRetTrue()
}

func (ver *Verifier) verPowerSetReq(fnObj *ast.FnObj, state *VerState) *glob.VerRet {
	if len(fnObj.Params) != 1 {
		return glob.NewVerMsg(glob.StmtRetTypeError, fnObj.String(), 0, []string{fmt.Sprintf("power_set expects 1 parameter, got %d", len(fnObj.Params))})
	}

	_ = state

	return glob.NewEmptyVerRetTrue()
}

func (ver *Verifier) verCupReq(fnObj *ast.FnObj, state *VerState) *glob.VerRet {
	if len(fnObj.Params) != 1 {
		return glob.NewVerMsg(glob.StmtRetTypeError, fnObj.String(), 0, []string{fmt.Sprintf("cup expects 1 parameter, got %d", len(fnObj.Params))})
	}

	_ = state

	return glob.NewEmptyVerRetTrue()
}

func (ver *Verifier) verCapReq(fnObj *ast.FnObj, state *VerState) *glob.VerRet {
	if len(fnObj.Params) != 1 {
		return glob.NewVerMsg(glob.StmtRetTypeError, fnObj.String(), 0, []string{fmt.Sprintf("cap expects 1 parameter, got %d", len(fnObj.Params))})
	}

	_ = state

	return glob.NewEmptyVerRetTrue()
}

func (ver *Verifier) verSetMinusReq(fnObj *ast.FnObj, state *VerState) *glob.VerRet {
	if len(fnObj.Params) != 2 {
		return glob.NewVerMsg(glob.StmtRetTypeError, fnObj.String(), 0, []string{fmt.Sprintf("set_minus expects 2 parameters, got %d", len(fnObj.Params))})
	}

	_ = state

	return glob.NewEmptyVerRetTrue()
}

func (ver *Verifier) verSymmetricDifferenceReq(fnObj *ast.FnObj, state *VerState) *glob.VerRet {
	if len(fnObj.Params) != 2 {
		return glob.NewVerMsg(glob.StmtRetTypeError, fnObj.String(), 0, []string{fmt.Sprintf("set_diff expects 2 parameters, got %d", len(fnObj.Params))})
	}

	_ = state

	return glob.NewEmptyVerRetTrue()
}

func (ver *Verifier) verProjReq(fnObj *ast.FnObj, state *VerState) *glob.VerRet {
	if len(fnObj.Params) != 2 {
		return glob.NewVerMsg(glob.StmtRetTypeError, fnObj.String(), 0, []string{fmt.Sprintf("proj expects 2 parameters, got %d", len(fnObj.Params))})
	}

	_ = state

	return glob.NewEmptyVerRetTrue()
}

func (ver *Verifier) verDimReq(fnObj *ast.FnObj, state *VerState) *glob.VerRet {
	if len(fnObj.Params) != 1 {
		return glob.NewVerMsg(glob.StmtRetTypeError, fnObj.String(), 0, []string{fmt.Sprintf("dim expects 1 parameter, got %d", len(fnObj.Params))})
	}

	_ = state

	return glob.NewEmptyVerRetTrue()
}
