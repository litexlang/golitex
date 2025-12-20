package litex_env

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
	"strings"
)

func (e *Env) AtomsInObjDefinedOrBuiltin(obj ast.Obj, extraParams map[string]struct{}) glob.GlobRet {
	switch asObj := obj.(type) {
	case ast.Atom:
		return e.AtomDefinedOrBuiltin(asObj, extraParams)
	case *ast.FnObj:
		return e.AtomsInFnObjDefinedOrBuiltin(asObj, extraParams)
	default:
		return glob.ErrRet(fmt.Errorf("unknown object type: %T", obj))
	}
}

func (env *Env) AtomDefinedOrBuiltin(atom ast.Atom, extraParams map[string]struct{}) glob.GlobRet {
	if _, ok := extraParams[string(atom)]; ok {
		return glob.NewGlobTrue("")
	}

	// Check if it's a builtin atom
	if glob.IsBuiltinAtom(string(atom)) {
		return glob.NewGlobTrue("")
	}

	// Check if it's a number literal
	if _, ok := ast.IsNumLitAtomObj(atom); ok {
		return glob.NewGlobTrue("")
	}

	// Check if it's defined by user
	ret := env.IsAtomObjDefinedByUser(atom)
	if ret.IsTrue() {
		return glob.NewGlobTrue("")
	}

	// Check if it's a keyword that's not an object
	if glob.IsKeywordSetOrNonEmptySetOrFiniteSet(string(atom)) {
		return glob.NewGlobErr(fmt.Sprintf("%s keyword is not an object.", string(atom)))
	} else {
		return glob.ErrRet(fmt.Errorf("undefined atom: %s", atom))
	}
}

func (e *Env) AtomsInFnObjDefinedOrBuiltin(fnObj *ast.FnObj, extraParams map[string]struct{}) glob.GlobRet {
	// Special handling for setBuilder
	if ast.IsSetBuilder(fnObj) {
		return e.AtomsInSetBuilderDefined(fnObj, extraParams)
	}

	for _, param := range fnObj.Params {
		if ret := e.AtomsInObjDefinedOrBuiltin(param, extraParams); ret.IsNotTrue() {
			return ret
		}
	}

	return e.AtomsInObjDefinedOrBuiltin(fnObj.FnHead, extraParams)
}

func (env *Env) AtomsInSetBuilderDefined(obj ast.Obj, extraParams map[string]struct{}) glob.GlobRet {
	setBuilderObj := obj.(*ast.FnObj)
	setBuilder, err := setBuilderObj.ToSetBuilderStruct()
	if err != nil {
		return glob.ErrRet(fmt.Errorf("failed to parse setBuilder: %s", err.Error()))
	}

	// Check parentSet
	if ret := env.AtomsInObjDefinedOrBuiltin(setBuilder.ParentSet, extraParams); ret.IsNotTrue() {
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
		if ret := env.AtomsInSpecFactDefined(fact, combinedParams); ret.IsNotTrue() {
			return ret
		}
	}

	return glob.NewGlobTrue("")
}

// 在def时，检查fact中的所有atom是否都定义了
func (env *Env) AtomObjsInFactProperlyDefined(stmt ast.FactStmt, extraParams map[string]struct{}) glob.GlobRet {
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

	return glob.NewGlobTrue("")
}

func (env *Env) IsPropDefinedOrBuiltinProp(stmt *ast.SpecFactStmt) glob.GlobRet {
	// Check if it's an exist_prop defined by user
	if stmt.TypeEnum == ast.TrueExist_St || stmt.TypeEnum == ast.FalseExist_St {
		if glob.IsBuiltinExistPropName(string(stmt.PropName)) {
			return glob.NewGlobTrue("")
		}

		existPropDef := env.GetExistPropDef(stmt.PropName)
		if existPropDef != nil {
			return glob.NewGlobTrue("")
		}
		return glob.ErrRet(fmt.Errorf("undefined exist_prop: %s", stmt.PropName))
	} else {
		if glob.IsBuiltinPropName(string(stmt.PropName)) {
			return glob.NewGlobTrue("")
		}

		if glob.IsBuiltinExistPropName(string(stmt.PropName)) {
			return glob.NewGlobTrue("")
		}

		// Check if it's a regular prop defined by user
		propDef := env.GetPropDef(stmt.PropName)
		if propDef != nil {
			return glob.NewGlobTrue("")
		}

		existPropDef := env.GetExistPropDef(stmt.PropName)
		if existPropDef != nil {
			return glob.NewGlobTrue("")
		}

		return glob.ErrRet(fmt.Errorf("undefined prop or exist_prop: %s", stmt.PropName))
	}
}

func (env *Env) IsAtomDefinedByOrBuiltinOrSetNonemptySetFiniteSet(atom ast.Atom, extraParams map[string]struct{}) glob.GlobRet {
	if glob.IsKeywordSetOrNonEmptySetOrFiniteSet(string(atom)) {
		return glob.NewGlobTrue("")
	} else {
		return env.AtomDefinedOrBuiltin(atom, extraParams)
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
		ret := env.AtomsInObjDefinedOrBuiltinOrSetNonemptySetFiniteSet(paramSet, combinedParams)
		if ret.IsNotTrue() {
			return ret
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

	return glob.NewGlobTrue("")
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

	return glob.NewGlobTrue("")
}

func (env *Env) AtomsInOrDefined(stmt *ast.OrStmt, extraParams map[string]struct{}) glob.GlobRet {
	for _, stmt := range stmt.Facts {
		if ret := env.AtomObjsInFactProperlyDefined(stmt, extraParams); ret.IsNotTrue() {
			return ret
		}
	}

	return glob.NewGlobTrue("")
}

func (env *Env) AtomsInEqualsFactDefined(stmt *ast.EqualsFactStmt, extraParams map[string]struct{}) glob.GlobRet {
	for _, obj := range stmt.Params {
		if ret := env.AtomsInObjDefinedOrBuiltin(obj, extraParams); ret.IsNotTrue() {
			return ret
		}
	}

	return glob.NewGlobTrue("")
}

func (e *Env) IsAtomObjDefinedByUser(AtomObjName ast.Atom) glob.GlobRet {
	if strings.Contains(string(AtomObjName), glob.PkgNameAtomSeparator) {
		PkgNameAndAtomName := strings.Split(string(AtomObjName), glob.PkgNameAtomSeparator)
		PkgName := PkgNameAndAtomName[0]
		AtomName := PkgNameAndAtomName[1]
		pkgPath, ok := e.PackageManager.PkgPathNameMgr.NamePathMap[PkgName]
		if !ok {
			return glob.ErrRet(fmt.Errorf("package %s is not found", PkgName))
		}
		pkgPathEnv, ok := e.PackageManager.PkgPathEnvPairs[pkgPath]
		if !ok {
			return glob.ErrRet(fmt.Errorf("package environment for %s is not found", PkgName))
		}
		ret := pkgPathEnv.isAtomDefinedAtCurEnv(ast.Atom(AtomName))
		if ret.IsTrue() {
			return glob.NewGlobTrue("")
		}
		return ret
	}

	for env := e; env != nil; env = env.Parent {
		ret := env.isAtomDefinedAtCurEnv(AtomObjName)
		if ret.IsTrue() {
			return glob.NewGlobTrue("")
		}
	}
	return glob.ErrRet(fmt.Errorf("undefined: %s", AtomObjName))
}

func (e *Env) isAtomDefinedAtCurEnv(AtomObjName ast.Atom) glob.GlobRet {
	_, ok := e.ObjDefMem[string(AtomObjName)]
	if ok {
		return glob.NewGlobTrue("")
	}

	_, ok = e.FnTemplateDefMem[string(AtomObjName)]
	if ok {
		return glob.NewGlobTrue("")
	}

	return glob.ErrRet(fmt.Errorf("undefined: %s", AtomObjName))
}

func (env *Env) AtomsInObjDefinedOrBuiltinOrSetNonemptySetFiniteSet(obj ast.Obj, extraParams map[string]struct{}) glob.GlobRet {
	if asAtom, ok := obj.(ast.Atom); ok && glob.IsKeywordSetOrNonEmptySetOrFiniteSet(string(asAtom)) {
		return glob.NewGlobTrue("")
	}

	return env.AtomsInObjDefinedOrBuiltin(obj, extraParams)
}

func (e *Env) IsNameDefinedOrBuiltin(name string, extraParams map[string]struct{}) glob.GlobRet {
	if _, ok := extraParams[name]; ok {
		return glob.NewGlobTrue("")
	}

	if glob.IsBuiltinAtom(name) {
		return glob.NewGlobTrue("")
	}

	if e.IsPkgName(name) {
		return glob.NewGlobTrue("")
	}

	if _, ok := ast.IsNumLitAtomObj(ast.Atom(name)); ok {
		return glob.NewGlobTrue("")
	}

	ret := e.IsAtomObjDefinedByUser(ast.Atom(name))
	if ret.IsTrue() {
		return glob.NewGlobTrue("")
	}

	existPropDef := e.GetExistPropDef(ast.Atom(name))
	if existPropDef != nil {
		return glob.NewGlobTrue("")
	}

	propDef := e.GetPropDef(ast.Atom(name))
	if propDef != nil {
		return glob.NewGlobTrue("")
	}

	return glob.ErrRet(fmt.Errorf("undefined: %s", name))
}

func (env *Env) IsValidIdentifierAvailable(name string) glob.GlobRet {
	err := glob.IsValidUseDefinedAtomObj(name)
	if err != nil {
		return glob.ErrRet(err)
	}

	ret := env.IsAtomObjDefinedByUser(ast.Atom(name))
	if ret.IsTrue() {
		return glob.ErrRet(duplicateDefError(name))
	}

	return glob.NewGlobTrue("")
}
