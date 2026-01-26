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
	ast "golitex/ast"
)

func (ver *Verifier) matchParamWithFreeParamsWithInstParam(freeParams []string, knownParam ast.Obj, givenParam ast.Obj) (bool, map[string]ast.Obj) {
	switch asKnownParam := knownParam.(type) {
	case ast.Atom:
		switch asGivenParam := givenParam.(type) {
		case ast.Atom:
			return ver.matchParamWithFreeParamsAsAtomWithInstParamAsAtom(freeParams, asKnownParam, asGivenParam)
		case *ast.FnObj:
			return ver.matchParamWithFreeParamsAsAtomWithInstParamAsFnObj(freeParams, asKnownParam, asGivenParam)
		}
	case *ast.FnObj:
		switch asGivenParam := givenParam.(type) {
		case ast.Atom:
			return ver.matchParamWithFreeParamsAsFnObjWithInstParamAsAtom(freeParams, asKnownParam, asGivenParam)
		case *ast.FnObj:
			return ver.matchParamWithFreeParamsAsFnObjWithInstParamAsFnObj(freeParams, asKnownParam, asGivenParam)
		}
	}

	return false, nil
}

func (ver *Verifier) matchParamWithFreeParamsAsAtomWithInstParamAsAtom(freeParams []string, knownParam ast.Atom, givenParam ast.Atom) (bool, map[string]ast.Obj) {
	return false, nil
}

func (ver *Verifier) matchParamWithFreeParamsAsAtomWithInstParamAsFnObj(freeParams []string, knownParam ast.Atom, givenParam *ast.FnObj) (bool, map[string]ast.Obj) {
	return false, nil
}

func (ver *Verifier) matchParamWithFreeParamsAsFnObjWithInstParamAsAtom(freeParams []string, knownParam *ast.FnObj, givenParam ast.Atom) (bool, map[string]ast.Obj) {
	return false, nil
}

func (ver *Verifier) matchParamWithFreeParamsAsFnObjWithInstParamAsFnObj(freeParams []string, knownParam *ast.FnObj, givenParam *ast.FnObj) (bool, map[string]ast.Obj) {
	return false, nil
}
