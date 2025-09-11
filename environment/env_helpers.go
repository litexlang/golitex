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
// Litex website: https://litexlang.org
// Litex github repository: https://github.com/litexlang/golitex
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_env

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
)

func (e *Env) GetFactsFromKnownFactInMatchEnv(envFact *ast.SpecFactStmt) (*KnownFactsStruct, bool) {
	knownFacts, ok := e.KnownFactInMatchEnv[string(envFact.PropName)]
	if !ok {
		return nil, false
	}
	return &knownFacts, true
}

func (e *Env) isSetFnRetValue(fc ast.Fc) (*ast.HaveSetFnStmt, bool) {
	asFn, ok := fc.(*ast.FcFn)
	if !ok {
		return nil, false
	}

	// name
	fnName := asFn.FnHead
	fnNameAsAtom, ok := fnName.(ast.FcAtom)
	if !ok {
		return nil, false
	}
	haveSetFn, ok := e.GetHaveSetFnDef(fnNameAsAtom)
	return haveSetFn, ok
}

func (e *Env) GenerateUndeclaredRandomName() string {
	i := 4
	var randomStr string
	for {
		randomStr = glob.RandomString(i)
		// check if the string is undeclared
		if !e.IsAtomDeclared(ast.FcAtom(randomStr), map[string]struct{}{}) {
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
		if !e.IsAtomDeclared(ast.FcAtom(randomStr), map[string]struct{}{}) {
			_, ok := m[randomStr]
			if !ok {
				return randomStr
			}
		}
		i++
	}
}

func (e *Env) GetFnStructFromFnTName(fnTName *ast.FcFn) (*ast.FnTStruct, error) {
	if fcFnTypeToFnTStruct, ok := ast.FcFnTypeTToFnStruct(fnTName); ok {
		return fcFnTypeToFnTStruct, nil
	} else {
		fnTNameHeadAsAtom, ok := fnTName.FnHead.(ast.FcAtom)
		if !ok {
			return nil, fmt.Errorf("fnTNameHead is not an atom")
		}

		return e.getFnTDef_InstFnTStructOfIt(fnTNameHeadAsAtom, fnTName.Params)
	}
}

func (e *Env) getFnTDef_InstFnTStructOfIt(fnTDefName ast.FcAtom, templateParams []ast.Fc) (*ast.FnTStruct, error) {
	defOfT, ok := e.GetFnTemplateDef(fnTDefName)
	if !ok {
		return nil, fmt.Errorf("fnTNameHead %s is not a fn template", fnTDefName)
	}

	uniMap, err := ast.MakeUniMap(defOfT.TemplateDefHeader.Params, templateParams)
	if err != nil {
		return nil, err
	}

	return defOfT.Fn.Instantiate(uniMap)
}
