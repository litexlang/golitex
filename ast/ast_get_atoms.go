package litex_ast

import "slices"

func (stmt *SpecFactStmt) GetAtoms() []FcAtom {
	atoms := []FcAtom{stmt.PropName}
	for _, param := range stmt.Params {
		atoms = append(atoms, GetAtomsInFc(param)...)
	}
	return atoms
}

func (stmt *EnumStmt) GetAtoms() []FcAtom {
	atomsOfName := GetAtomsInFc(stmt.EnumName)

	atoms := []FcAtom{}
	atoms = append(atoms, atomsOfName...)
	for _, value := range stmt.EnumValues {
		atoms = append(atoms, GetAtomsInFc(value)...)
	}
	return atoms
}

func (stmt *UniFactStmt) GetAtoms() []FcAtom {
	atoms := []FcAtom{}
	for _, param := range stmt.ParamSets {
		atoms = append(atoms, GetAtomsInFc(param)...)
	}
	for _, fact := range stmt.DomFacts {
		atoms = append(atoms, fact.GetAtoms()...)
	}
	for _, fact := range stmt.ThenFacts {
		atoms = append(atoms, fact.GetAtoms()...)
	}
	// for _, fact := range stmt.IffFacts {
	// 	atoms = append(atoms, fact.GetAtoms()...)
	// }

	// 如果这个atom是param，那把这项扔了
	ret := []FcAtom{}
	for _, atom := range atoms {
		// if slices.Contains(stmt.Params, atom.Name) && atom.PkgName == glob.EmptyPkg {
		if slices.Contains(stmt.Params, string(atom)) {
			continue
		} else {
			ret = append(ret, atom)
		}
	}

	return ret
}

func (stmt *UniFactWithIffStmt) GetAtoms() []FcAtom {
	atoms := stmt.UniFact.GetAtoms()
	for _, fact := range stmt.IffFacts {
		atoms = append(atoms, fact.GetAtoms()...)
	}
	return atoms
}

func (stmt *OrStmt) GetAtoms() []FcAtom {
	atoms := []FcAtom{}
	for _, fact := range stmt.Facts {
		atoms = append(atoms, fact.GetAtoms()...)
	}
	return atoms
}

func (stmt *SetEqualStmt) GetAtoms() []FcAtom {
	panic("not implemented")
}
