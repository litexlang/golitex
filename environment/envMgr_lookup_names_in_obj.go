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

package litex_env

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
)

func (envMgr *EnvMgr) LookupNamesInObj(obj ast.Obj, extraParams map[string]struct{}) glob.GlobRet {
	switch asObj := obj.(type) {
	case ast.Atom:
		return envMgr.lookupAtomObjName(asObj, extraParams)
	case *ast.FnObj:
		return envMgr.lookupNamesInFnObj(asObj, extraParams)
	default:
		return glob.ErrRet(fmt.Errorf("unknown object type: %T", obj))
	}
}

// TODO: 目前只是检查了在当前的envMgr中是否定义了，没有检查在parent envMgr中是否定义了
func (envMgr *EnvMgr) lookupAtomObjName(atom ast.Atom, extraParams map[string]struct{}) glob.GlobRet {
	if _, ok := extraParams[string(atom)]; ok {
		return glob.NewEmptyGlobTrue()
	}

	// Check if it's a builtin atom
	if glob.IsBuiltinAtomName(string(atom)) {
		return glob.NewEmptyGlobTrue()
	}

	// Check if it's a number literal
	if _, ok := ast.IsNumLitAtomObj(atom); ok {
		return glob.NewEmptyGlobTrue()
	}

	// Check if it's defined by user
	defined := envMgr.IsAtomNameDefinedByUser(string(atom))
	if !defined {
		if glob.IsKeywordSetOrNonEmptySetOrFiniteSet(string(atom)) {
			return glob.NewGlobErr(fmt.Sprintf("undefined atom name: %s. Be careful, %s, %s, %s are syntax sugar for %s, %s, %s respectively. They are not objects.", string(atom), glob.KeywordSet, glob.KeywordNonEmptySet, glob.KeywordFiniteSet, glob.KeywordSet, glob.KeywordNonEmptySet, glob.KeywordFiniteSet))
		} else {
			return glob.ErrRet(fmt.Errorf("undefined atom name: %s", atom))
		}
	} else {
		return glob.NewEmptyGlobTrue()
	}
}

func (envMgr *EnvMgr) lookupNamesInFnObj(fnObj *ast.FnObj, extraParams map[string]struct{}) glob.GlobRet {
	// Special handling for setBuilder
	if ast.IsSetBuilder(fnObj) {
		return envMgr.lookupNamesInSetBuilder(fnObj, extraParams)
	}

	for _, param := range fnObj.Params {
		if ret := envMgr.LookupNamesInObj(param, extraParams); ret.IsNotTrue() {
			return ret
		}
	}

	// 如果head是fn,那直接成立了
	if fnObj.IsAtomHeadEqualToStr(glob.KeywordFn) {
		return glob.NewEmptyGlobTrue()
	}

	// 如果head 是 fn_template 那也OK了
	if envMgr.FnObjHeadIsAtomAndIsFnSet(fnObj) {
		return glob.NewEmptyGlobTrue()
	}

	return envMgr.LookupNamesInObj(fnObj.FnHead, extraParams)
}

func (envMgr *EnvMgr) lookupNamesInSetBuilder(obj ast.Obj, extraParams map[string]struct{}) glob.GlobRet {
	setBuilderObj := obj.(*ast.FnObj)
	setBuilder, err := setBuilderObj.ToSetBuilderStruct()
	if err != nil {
		return glob.ErrRet(fmt.Errorf("failed to parse setBuilder: %s", err.Error()))
	}

	// Check parentSet
	if ret := envMgr.LookupNamesInObj(setBuilder.ParentSet, extraParams); ret.IsNotTrue() {
		return ret
	}

	// Merge setBuilder param into extraParams (it's a bound variable)
	combinedParams := make(map[string]struct{})
	for k, v := range extraParams {
		combinedParams[k] = v
	}
	combinedParams[setBuilder.Param] = struct{}{}

	// Check facts in setBuilder
	for _, fact := range setBuilder.Facts {
		if ret := envMgr.LookupNamesInSpecFact(fact, combinedParams); ret.IsNotTrue() {
			return ret
		}
	}

	return glob.NewEmptyGlobTrue()
}
