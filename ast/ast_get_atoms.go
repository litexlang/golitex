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

package litex_ast

import "slices"

func (stmt *SpecFactStmt) GetAtoms() []Atom {
	atoms := []Atom{stmt.PropName}
	for _, param := range stmt.Params {
		atoms = append(atoms, GetAtomsInObj(param)...)
	}
	return atoms
}

// func (stmt *EnumStmt) GetAtoms() []Atom {
// 	atomsOfName := GetAtomsInObj(stmt.CurSet)

// 	atoms := []Atom{}
// 	atoms = append(atoms, atomsOfName...)
// 	for _, value := range stmt.Items {
// 		atoms = append(atoms, GetAtomsInObj(value)...)
// 	}
// 	return atoms
// }

func (stmt *UniFactStmt) GetAtoms() []Atom {
	atoms := []Atom{}
	for _, param := range stmt.ParamSets {
		atoms = append(atoms, GetAtomsInObj(param)...)
	}
	for _, fact := range stmt.DomFacts {
		atoms = append(atoms, fact.GetAtoms()...)
	}
	for _, fact := range stmt.ThenFacts {
		atoms = append(atoms, fact.GetAtoms()...)
	}

	// 如果这个atom是param，那把这项扔了
	ret := []Atom{}
	for _, atom := range atoms {
		if slices.Contains(stmt.Params, string(atom)) {
			continue
		} else {
			ret = append(ret, atom)
		}
	}

	return ret
}

func (stmt *UniFactWithIffStmt) GetAtoms() []Atom {
	atoms := stmt.UniFact.GetAtoms()
	for _, fact := range stmt.IffFacts {
		atoms = append(atoms, fact.GetAtoms()...)
	}
	return atoms
}

func (stmt *OrStmt) GetAtoms() []Atom {
	atoms := []Atom{}
	for _, fact := range stmt.Facts {
		atoms = append(atoms, fact.GetAtoms()...)
	}
	return atoms
}

func (stmt *IntensionalSetStmt) GetAtoms() []Atom {
	atoms := []Atom{}
	atoms = append(atoms, GetAtomsInObj(stmt.CurSet)...)
	atoms = append(atoms, GetAtomsInObj(stmt.ParentSet)...)
	for _, proof := range stmt.Facts {
		atoms = append(atoms, proof.GetAtoms()...)
	}
	return atoms
}

func (stmt *EqualsFactStmt) GetAtoms() []Atom {
	atoms := []Atom{}
	for _, param := range stmt.Params {
		atoms = append(atoms, GetAtomsInObj(param)...)
	}
	return atoms
}
