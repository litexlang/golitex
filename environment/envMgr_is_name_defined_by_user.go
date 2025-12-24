package litex_env

import (
	ast "golitex/ast"
	glob "golitex/glob"
)

func (envMgr *EnvMgr) IsAtomObjDefinedByUser(AtomObjName ast.Atom) bool {
	withPkgName, pkgName, _ := glob.GetPkgNameAndName(string(AtomObjName))

	if withPkgName && pkgName != envMgr.EnvPkgMgr.PkgMgr.CurPkgDefaultName {
		pkgEnvMgr := envMgr.GetEnvMgrOfPkgName(pkgName)
		if pkgEnvMgr == nil {
			return false
		}

		_, ok := pkgEnvMgr.AllDefinedAtomObjNames[string(AtomObjName)]
		return ok
	} else {
		_, ok := envMgr.AllDefinedAtomObjNames[string(AtomObjName)]
		return ok
	}
}

func (envMgr *EnvMgr) IsPropDefinedByUser(PropName ast.Atom) bool {
	withPkgName, pkgName, _ := glob.GetPkgNameAndName(string(PropName))

	if withPkgName && pkgName != envMgr.EnvPkgMgr.PkgMgr.CurPkgDefaultName {
		pkgEnvMgr := envMgr.GetEnvMgrOfPkgName(pkgName)
		if pkgEnvMgr == nil {
			return false
		}

		_, ok := pkgEnvMgr.AllDefinedPropNames[string(PropName)]
		return ok
	} else {
		_, ok := envMgr.AllDefinedPropNames[string(PropName)]
		return ok
	}
}

func (envMgr *EnvMgr) IsExistPropDefinedByUser(ExistPropName ast.Atom) bool {
	withPkgName, pkgName, _ := glob.GetPkgNameAndName(string(ExistPropName))

	if withPkgName && pkgName != envMgr.EnvPkgMgr.PkgMgr.CurPkgDefaultName {
		pkgEnvMgr := envMgr.GetEnvMgrOfPkgName(pkgName)
		if pkgEnvMgr == nil {
			return false
		}

		_, ok := pkgEnvMgr.AllDefinedExistPropNames[string(ExistPropName)]
		return ok
	} else {
		_, ok := envMgr.AllDefinedExistPropNames[string(ExistPropName)]
		return ok
	}
}

func (envMgr *EnvMgr) IsFnSetDefinedByUser(FnSetName ast.Atom) bool {
	withPkgName, pkgName, _ := glob.GetPkgNameAndName(string(FnSetName))

	if withPkgName && pkgName != envMgr.EnvPkgMgr.PkgMgr.CurPkgDefaultName {
		pkgEnvMgr := envMgr.GetEnvMgrOfPkgName(pkgName)
		if pkgEnvMgr == nil {
			return false
		}

		_, ok := pkgEnvMgr.AllDefinedFnSetNames[string(FnSetName)]
		return ok
	} else {
		_, ok := envMgr.AllDefinedFnSetNames[string(FnSetName)]
		return ok
	}
}

func (envMgr *EnvMgr) IsAlgoDefinedByUser(AlgoName ast.Atom) bool {
	withPkgName, pkgName, _ := glob.GetPkgNameAndName(string(AlgoName))

	if withPkgName && pkgName != envMgr.EnvPkgMgr.PkgMgr.CurPkgDefaultName {
		pkgEnvMgr := envMgr.GetEnvMgrOfPkgName(pkgName)
		if pkgEnvMgr == nil {
			return false
		}

		_, ok := pkgEnvMgr.AllDefinedAlgoNames[string(AlgoName)]
		return ok
	} else {
		_, ok := envMgr.AllDefinedAlgoNames[string(AlgoName)]
		return ok
	}
}

func (envMgr *EnvMgr) IsProveAlgoDefinedByUser(ProveAlgoName ast.Atom) bool {
	withPkgName, pkgName, _ := glob.GetPkgNameAndName(string(ProveAlgoName))

	if withPkgName && pkgName != envMgr.EnvPkgMgr.PkgMgr.CurPkgDefaultName {
		pkgEnvMgr := envMgr.GetEnvMgrOfPkgName(pkgName)
		if pkgEnvMgr == nil {
			return false
		}

		_, ok := pkgEnvMgr.AllDefinedProveAlgoNames[string(ProveAlgoName)]
		return ok
	} else {
		_, ok := envMgr.AllDefinedProveAlgoNames[string(ProveAlgoName)]
		return ok
	}
}
