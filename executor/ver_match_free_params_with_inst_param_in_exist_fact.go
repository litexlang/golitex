package litex_executor

import (
	ast "golitex/ast"
	"slices"
)

func (ver *Verifier) matchParamWithFreeParamsWithInstParamInExistFact(freeParams []string, existFreeParams []string, knownParam ast.Obj, givenParam ast.Obj) (bool, map[string]ast.Obj) {
	switch asKnownParam := knownParam.(type) {
	case ast.Atom:
		switch asGivenParam := givenParam.(type) {
		case ast.Atom:
			return ver.matchParamWithFreeParamsAsAtomWithInstParamAsAtomInExistFact(freeParams, existFreeParams, asKnownParam, asGivenParam)
		case *ast.FnObj:
			return ver.matchParamWithFreeParamsAsAtomWithInstParamAsFnObjInExistFact(freeParams, existFreeParams, asKnownParam, asGivenParam)
		}
	case *ast.FnObj:
		switch asGivenParam := givenParam.(type) {
		case ast.Atom:
			return ver.matchParamWithFreeParamsAsFnObjWithInstParamAsAtomInExistFact(freeParams, existFreeParams, asKnownParam, asGivenParam)
		case *ast.FnObj:
			return ver.matchParamWithFreeParamsAsFnObjWithInstParamAsFnObjInExistFact(freeParams, existFreeParams, asKnownParam, asGivenParam)
		}
	}

	return false, nil
}

func (ver *Verifier) matchParamWithFreeParamsAsAtomWithInstParamAsAtomInExistFact(freeParams []string, existFreeParams []string, knownParam ast.Atom, givenParam ast.Atom) (bool, map[string]ast.Obj) {
	if slices.Contains(freeParams, string(knownParam)) {
		return true, map[string]ast.Obj{string(knownParam): givenParam}
	}

	if slices.Contains(existFreeParams, string(knownParam)) {
		panic("")
	}

	panic("")
}

func (ver *Verifier) matchParamWithFreeParamsAsAtomWithInstParamAsFnObjInExistFact(freeParams []string, existFreeParams []string, knownParam ast.Atom, givenParam *ast.FnObj) (bool, map[string]ast.Obj) {
	panic("")
}

func (ver *Verifier) matchParamWithFreeParamsAsFnObjWithInstParamAsAtomInExistFact(freeParams []string, existFreeParams []string, knownParam *ast.FnObj, givenParam ast.Atom) (bool, map[string]ast.Obj) {
	panic("")
}

func (ver *Verifier) matchParamWithFreeParamsAsFnObjWithInstParamAsFnObjInExistFact(freeParams []string, existFreeParams []string, knownParam *ast.FnObj, givenParam *ast.FnObj) (bool, map[string]ast.Obj) {
	panic("")
}
