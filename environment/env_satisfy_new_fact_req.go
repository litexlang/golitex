package litex_env

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
)

func (env *Env) AtomObjsInFactProperlyDefined(stmt ast.FactStmt, extraParams map[string]struct{}) glob.GlobRet {
	// 检查所有的参数是否都定义了
	switch s := stmt.(type) {
	case *ast.SpecFactStmt:
		return env.AtomsInSpecFactDefined(s, extraParams)
	case *ast.UniFactStmt:
		return env.AtomObjsInUniFactDefined(s, extraParams)
	case *ast.UniFactWithIffStmt:
		return env.AtomsInUniFactWithIffDefined(s, extraParams)
	case *ast.OrStmt:
		return env.AtomsInOrDefined(s, extraParams)
	case *ast.EqualsFactStmt:
		return env.AtomsInEqualsFactDefined(s, extraParams)
	default:
		return glob.ErrRet(fmt.Errorf("unknown fact type: %T", stmt))
	}
}

func (env *Env) AtomsInSpecFactDefined(stmt *ast.SpecFactStmt, extraParams map[string]struct{}) glob.GlobRet {
	if ret := env.IsPropDefinedOrBuiltinProp(stmt); ret.IsNotTrue() {
		return ret
	}

	for _, param := range stmt.Params {
		if ret := env.AtomsInObjDefinedOrBuiltin(param, extraParams); ret.IsNotTrue() {
			return ret
		}
	}

	return glob.TrueRet("")
}

func (env *Env) IsPropDefinedOrBuiltinProp(stmt *ast.SpecFactStmt) glob.GlobRet {
	// Check if it's an exist_prop defined by user
	if stmt.TypeEnum == ast.TrueExist_St || stmt.TypeEnum == ast.FalseExist_St {
		existPropDef := env.GetExistPropDef(stmt.PropName)
		if existPropDef != nil {
			return glob.TrueRet("")
		}
		return glob.ErrRet(fmt.Errorf("undefined exist_prop: %s", stmt.PropName))
	} else {
		if glob.IsBuiltinPropName(string(stmt.PropName)) {
			return glob.TrueRet("")
		}

		// Check if it's a regular prop defined by user
		propDef := env.GetPropDef(stmt.PropName)
		if propDef != nil {
			return glob.TrueRet("")
		}

		existPropDef := env.GetExistPropDef(stmt.PropName)
		if existPropDef != nil {
			return glob.TrueRet("")
		}

		return glob.ErrRet(fmt.Errorf("undefined prop or exist_prop: %s", stmt.PropName))
	}
}

func (env *Env) IsAtomDefinedByOrBuiltinOrSetNonemptySetFiniteSet(atom ast.Atom, extraParams map[string]struct{}) glob.GlobRet {
	if glob.IsKeywordSetOrNonEmptySetOrFiniteSet(string(atom)) {
		return glob.TrueRet("")
	} else {
		return env.IsAtomObjDefinedOrBuiltin(atom, extraParams)
	}
}

func (env *Env) IsAtomObjDefinedOrBuiltin(atom ast.Atom, extraParams map[string]struct{}) glob.GlobRet {
	if _, ok := extraParams[string(atom)]; ok {
		return glob.TrueRet("")
	}

	// Check if it's a builtin atom
	if glob.IsBuiltinAtom(string(atom)) {
		return glob.TrueRet("")
	}

	// Check if it's a number literal
	if _, ok := ast.IsNumLitAtomObj(atom); ok {
		return glob.TrueRet("")
	}

	// Check if it's defined by user
	ret := env.IsAtomDefinedByUser(atom)
	if ret.IsTrue() {
		return glob.TrueRet("")
	}

	// Check if it's a keyword that's not an object
	if glob.IsKeywordSetOrNonEmptySetOrFiniteSet(string(atom)) {
		return glob.NewGlobErr(fmt.Sprintf("%s keyword is not an object.", string(atom)))
	} else {
		return glob.ErrRet(fmt.Errorf("undefined atom: %s", atom))
	}
}

func (env *Env) AtomObjsInUniFactDefined(stmt *ast.UniFactStmt, extraParams map[string]struct{}) glob.GlobRet {
	// Merge stmt.Params into extraParams for this uni fact
	combinedParams := make(map[string]struct{})
	for k, v := range extraParams {
		combinedParams[k] = v
	}

	// Check param sets
	for i, paramSet := range stmt.ParamSets {
		atoms := ast.GetAtomObjsInObj(paramSet)
		for _, atom := range atoms {
			if ret := env.IsAtomDefinedByOrBuiltinOrSetNonemptySetFiniteSet(atom, combinedParams); ret.IsNotTrue() {
				return ret
			}
		}

		if _, ok := combinedParams[stmt.Params[i]]; ok {
			return glob.NewGlobErr(fmt.Sprintf("duplicate free parameter: %s", stmt.Params[i]))
		}
		combinedParams[stmt.Params[i]] = struct{}{}
	}

	for _, stmt := range stmt.DomFacts {
		if ret := env.AtomObjsInFactProperlyDefined(stmt, combinedParams); ret.IsNotTrue() {
			return ret
		}
	}

	for _, stmt := range stmt.ThenFacts {
		if ret := env.AtomObjsInFactProperlyDefined(stmt, combinedParams); ret.IsNotTrue() {
			return ret
		}
	}

	return glob.TrueRet("")
}

func (env *Env) AtomsInUniFactWithIffDefined(stmt *ast.UniFactWithIffStmt, extraParams map[string]struct{}) glob.GlobRet {
	if ret := env.AtomObjsInUniFactDefined(stmt.UniFact, extraParams); ret.IsNotTrue() {
		return ret
	}

	combinedParams := map[string]struct{}{}
	for k, v := range extraParams {
		combinedParams[k] = v
	}

	for _, v := range stmt.UniFact.Params {
		combinedParams[v] = struct{}{}
	}

	for _, stmt := range stmt.IffFacts {
		if ret := env.AtomObjsInFactProperlyDefined(stmt, combinedParams); ret.IsNotTrue() {
			return ret
		}
	}

	return glob.TrueRet("")
}

func (env *Env) AtomsInOrDefined(stmt *ast.OrStmt, extraParams map[string]struct{}) glob.GlobRet {
	for _, stmt := range stmt.Facts {
		if ret := env.AtomObjsInFactProperlyDefined(stmt, extraParams); ret.IsNotTrue() {
			return ret
		}
	}

	return glob.TrueRet("")
}

func (env *Env) AtomsInEqualsFactDefined(stmt *ast.EqualsFactStmt, extraParams map[string]struct{}) glob.GlobRet {
	for _, obj := range stmt.Params {
		if ret := env.AtomsInObjDefinedOrBuiltin(obj, extraParams); ret.IsNotTrue() {
			return ret
		}
	}

	return glob.TrueRet("")
}

func (env *Env) AtomsInSetBuilderDefined(obj ast.Obj, extraParams map[string]struct{}) glob.GlobRet {
	setBuilderObj := obj.(*ast.FnObj)
	setBuilder, err := setBuilderObj.ToSetBuilderStruct()
	if err != nil {
		return glob.ErrRet(fmt.Errorf("failed to parse setBuilder: %s", err.Error()))
	}

	// Merge setBuilder param into extraParams (it's a bound variable)
	combinedParams := make(map[string]struct{})
	for k, v := range extraParams {
		combinedParams[k] = v
	}
	combinedParams[setBuilder.Param] = struct{}{}

	// Check parentSet
	if ret := env.AtomsInObjDefinedOrBuiltin(setBuilder.ParentSet, combinedParams); ret.IsNotTrue() {
		return ret
	}

	// Check facts in setBuilder
	for _, fact := range setBuilder.Facts {
		if ret := env.AtomObjsInFactProperlyDefined(fact, combinedParams); ret.IsNotTrue() {
			return ret
		}
	}

	return glob.TrueRet("")
}

func (env *Env) AtomsInObjDefinedOrBuiltin(obj ast.Obj, extraParams map[string]struct{}) glob.GlobRet {
	// Special handling for setBuilder
	if ast.IsSetBuilder(obj) {
		return env.AtomsInSetBuilderDefined(obj, extraParams)
	}

	// Regular object handling
	atoms := ast.GetAtomObjsInObj(obj)
	for _, atom := range atoms {
		if ret := env.IsAtomObjDefinedOrBuiltin(atom, extraParams); ret.IsNotTrue() {
			return ret
		}
	}
	return glob.TrueRet("")
}

func (env *Env) AtomsInObjDefinedOrBuiltinOrSetNonemptySetFiniteSet(obj ast.Obj, extraParams map[string]struct{}) glob.GlobRet {
	if ast.IsSetBuilder(obj) {
		return env.AtomsInSetBuilderDefined(obj, extraParams)
	}

	atoms := ast.GetAtomObjsInObj(obj)
	for _, atom := range atoms {
		if ret := env.IsAtomDefinedByOrBuiltinOrSetNonemptySetFiniteSet(atom, extraParams); ret.IsNotTrue() {
			return ret
		}
	}
	return glob.TrueRet("")
}
