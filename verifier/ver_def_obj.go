package litex_verifier

import (
	"fmt"
	ast "golitex/ast"
	env "golitex/environment"
)

func (ver *Verifier) NewDefObj_InsideAtomsDeclared(stmt *ast.DefObjStmt) error {
	err := ver.env.NonDuplicateParam_NoUndeclaredParamSet(stmt.Objs, stmt.ObjSets, true)
	if err != nil {
		return err
	}

	extraAtomNames := map[string]struct{}{}
	for _, objName := range stmt.Objs {
		extraAtomNames[objName] = struct{}{}
	}

	for _, fact := range stmt.NewInFacts() {
		if !ver.env.AreAtomsInFactAreDeclared(fact, extraAtomNames) {
			return fmt.Errorf(env.AtomsInFactNotDeclaredMsg(fact))
		}
		err := ver.env.NewFact(fact)
		if err != nil {
			return err
		}
	}

	for _, fact := range stmt.Facts {
		if !ver.env.AreAtomsInFactAreDeclared(fact, extraAtomNames) {
			return fmt.Errorf(env.AtomsInFactNotDeclaredMsg(fact))
		}
		err := ver.env.NewFact(fact)
		if err != nil {
			return err
		}
	}

	for _, objName := range stmt.Objs {
		err := ver.env.IsInvalidName(objName)
		if err != nil {
			return err
		}
	}

	// 如果这个obj是fn，那么要插入到fn def mem中
	for i, objName := range stmt.Objs {
		if ast.IsFnDeclarationFc(stmt.ObjSets[i]) {
			fnDefStmt := ast.FromFnDeclFcToDefFnStmt(objName, stmt.ObjSets[i])
			err = ver.env.NewDefFn_InsideAtomsDeclared(fnDefStmt)
			if err != nil {
				return err
			}
		} else {
			err = ver.env.ObjDefMem.InsertItem(objName)
			if err != nil {
				return err
			}
		}
	}

	return nil
}
