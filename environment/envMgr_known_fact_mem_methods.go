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

package litex_env

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
)

func (envMgr *EnvMgr) GetSpecFactMem() (*SpecFactMem, bool) {
	return &envMgr.CurEnv().KnownFactsStruct.SpecFactMem, true
}

func (envMgr *EnvMgr) GetSpecFactInLogicExprMem() (*SpecFactInLogicExprMem, bool) {
	return &envMgr.CurEnv().KnownFactsStruct.SpecFactInLogicExprMem, true
}

func (envMgr *EnvMgr) GetSpecFactInUniFactMem() (*SpecFactInUniFactMem, bool) {
	return &envMgr.CurEnv().KnownFactsStruct.SpecFactInUniFactMem, true
}

func (envMgr *EnvMgr) GetSpecFact_InLogicExpr_InUniFactMem() (*SpecFact_InLogicExpr_InUniFactMem, bool) {
	return &envMgr.CurEnv().KnownFactsStruct.SpecFact_InLogicExpr_InUniFactMem, true
}

func (envMgr *EnvMgr) IsFnDeclared(obj ast.Atom) (*FnInFnTMemItem, bool) {
	// TODO 这里需要更严格检查一下是否是正常的函数名，但是目前没有
	if _, ok := glob.BuiltinKeywordsSet[string(obj)]; ok {
		return nil, true
	}

	// TODO 这里需要更严格检查一下是否是正常的函数名
	if glob.IsKeySymbol(string(obj)) {
		return nil, true
	}

	fnDef := envMgr.GetLatestFnT_GivenNameIsIn(string(obj))
	if fnDef == nil {
		return nil, false
	}
	return fnDef, true
}

func (envMgr *EnvMgr) StoreFnSatisfyFnTemplateFact_PassInInstTemplateNoName(fn ast.Obj, fnTemplateFnObj *ast.FnObj, fnTStruct *ast.AnonymousFn) *glob.StmtRet {
	if fnTemplateFnObj != nil {
		fnTStruct, ret := envMgr.GetFnStructFromFnTName(fnTemplateFnObj)
		if ret.IsErr() {
			return ret
		}

		ret = envMgr.InsertFnInFnTT(fn, fnTStruct)
		if ret.IsErr() {
			return ret
		}

		return glob.NewEmptyStmtTrue()
	} else {
		ret := envMgr.InsertFnInFnTT(fn, fnTStruct)
		if ret.IsErr() {
			return ret
		}

		return glob.NewEmptyStmtTrue()
	}
}

func (envMgr *EnvMgr) getInstantiatedFnTTOfFnObj(fnObj *ast.FnObj) (*ast.AnonymousFn, bool, *glob.StmtRet) {
	if ast.IsFnTemplate_ObjFn(fnObj) {
		fnTNoName, err := fnObj.FnTObj_ToFnTNoName()
		if err != nil {
			return nil, false, glob.ErrRetWithErr(err)
		}
		return fnTNoName, true, glob.NewEmptyStmtTrue()
	}

	def := envMgr.GetFnTemplateDef(fnObj.FnHead.(ast.Atom))
	if def == nil {
		return nil, false, glob.NewEmptyStmtTrue()
	}

	fnTNoName, err := def.Instantiate_GetFnTemplateNoName(fnObj)
	if err != nil {
		return nil, false, glob.ErrRetWithErr(err)
	}

	return fnTNoName, true, glob.NewEmptyStmtTrue()
}

func (envMgr *EnvMgr) NewFnTemplateInEnvMem(stmt *ast.DefFnSetStmt) *glob.StmtRet {
	// 确保template name 没有被声明过
	ret := envMgr.IsValidAndAvailableName(string(stmt.TemplateDefHeader.Name))
	if ret.IsNotTrue() {
		return glob.ErrRet(fmt.Sprintf("fn template name %s is already declared", stmt.TemplateDefHeader.Name))
	}

	ret = envMgr.AtomsInFnTemplateFnTemplateDeclared(ast.Atom(stmt.TemplateDefHeader.Name), stmt)
	if ret.IsErr() {
		return ret
	}

	// Store in AllDefinedFnTemplateNames
	envMgr.AllDefinedFnSetNames[string(stmt.TemplateDefHeader.Name)] = stmt

	// Mark in current EnvSlice
	envMgr.CurEnv().FnTemplateDefMem[string(stmt.TemplateDefHeader.Name)] = struct{}{}

	return glob.NewEmptyStmtTrue()
}
