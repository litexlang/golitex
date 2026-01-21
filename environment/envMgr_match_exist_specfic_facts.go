package litex_env

import (
	ast "golitex/ast"
	glob "golitex/glob"
)

func (envMgr *EnvMgr) GenerateNoDuplicateNames(length int) []string {
	usedNames := map[string]struct{}{}
	names := make([]string, length)
	for i := 0; i < length; i++ {
		names[i] = envMgr.GenerateUndeclaredRandomName_AndNotInMap(usedNames)
	}
	return names
}

func (e *EnvMgr) MatchExistSpecificFacts(given *ast.ExistSpecificFactStmt, stored *ast.ExistSpecificFactStmt, newExistFreeParams []string) *glob.StmtRet {
	if len(stored.ExistFreeParams) != len(given.ExistFreeParams) {
		return glob.NewEmptyStmtUnknown()
	}

	if given.IsTrue != stored.IsTrue {
		return glob.NewEmptyStmtUnknown()
	}

	if given.PureFact.IsTrue != stored.PureFact.IsTrue {
		return glob.NewEmptyStmtUnknown()
	}

	newExistSpecificFactStmt, err := given.ReplaceFreeParamsWithNewParams(newExistFreeParams)
	if err != nil {
		return glob.StmtRetFromErr(err)
	}

	newStoredExistSpecificFactStmt, err := stored.ReplaceFreeParamsWithNewParams(newExistFreeParams)
	if err != nil {
		return glob.StmtRetFromErr(err)
	}

	if newExistSpecificFactStmt.String() == newStoredExistSpecificFactStmt.String() {
		return glob.NewEmptyStmtTrue()
	}

	return glob.NewEmptyStmtUnknown()
}
