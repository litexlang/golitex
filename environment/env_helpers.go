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

func (e *Env) GenerateUndeclaredRandomName() string {
	i := 4
	var randomStr string
	for {
		randomStr = glob.RandomString(i)
		// check if the string is undeclared
		ret := e.IsNameDefinedOrBuiltin((randomStr), map[string]struct{}{})
		if ret.IsErr() {
			return randomStr
		}
		i++
	}
}

func (e *Env) GenerateUndeclaredRandomName_AndNotInMap(m map[string]struct{}) string {
	i := 4
	var randomStr string
	for {
		randomStr = glob.RandomString(i)
		// check if the string is undeclared
		ret := e.IsNameDefinedOrBuiltin(randomStr, map[string]struct{}{})
		if ret.IsErr() {
			_, ok := m[randomStr]
			if !ok {
				return randomStr
			}
		}
		i++
	}
}

func (e *Env) GetFnStructFromFnTName(fnTName *ast.FnObj) (*ast.FnTStruct, glob.GlobRet) {
	if objFnTypeToFnTStruct, ok := ast.ObjFnT_To_FnTStruct(fnTName); ok {
		return objFnTypeToFnTStruct, glob.NewGlobTrue("")
	} else {
		fnTNameHeadAsAtom, ok := fnTName.FnHead.(ast.Atom)
		if !ok {
			return nil, glob.ErrRet(fmt.Errorf("fnTNameHead is not an atom"))
		}

		return e.getFnTDef_InstFnTStructOfIt(fnTNameHeadAsAtom, fnTName.Params)
	}
}

func (e *Env) getFnTDef_InstFnTStructOfIt(fnTDefName ast.Atom, templateParams []ast.Obj) (*ast.FnTStruct, glob.GlobRet) {
	defOfT := e.GetFnTemplateDef(fnTDefName)
	if defOfT == nil {
		return nil, glob.ErrRet(fmt.Errorf("fnTNameHead %s is not a fn template", fnTDefName))
	}

	uniMap, err := ast.MakeUniMap(defOfT.TemplateDefHeader.Params, templateParams)
	if err != nil {
		return nil, glob.ErrRet(err)
	}

	fnTStruct, err := defOfT.Fn.Instantiate(uniMap)
	if err != nil {
		return nil, glob.ErrRet(err)
	}

	return fnTStruct, glob.NewGlobTrue("")
}

func (e *Env) AutoDerivedFactsMsg(originalFact string, derivedFacts []string) glob.GlobRet {
	msgs := []string{originalFact, "-- Automatically derived facts --"}
	msgs = append(msgs, derivedFacts...)
	return glob.NewGlobTrueWithMsgs(msgs)
}

func (env *Env) storeSpecFactInMemAndCollect(fact *ast.SpecFactStmt, derivedFacts *[]string) glob.GlobRet {
	ret := env.storeSpecFactInMem(fact)
	if ret.IsErr() {
		return ret
	}
	*derivedFacts = append(*derivedFacts, fact.String())
	return glob.NewGlobTrue("")
}
