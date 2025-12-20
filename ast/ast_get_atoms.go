// // Copyright 2024 Jiachen Shen.
// //
// // Licensed under the Apache License, Version 2.0 (the "License");
// // you may not use this file except in compliance with the License.
// // You may obtain a copy of the License at
// //
// //     http://www.apache.org/licenses/LICENSE-2.0
// //
// // Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// // Litex email: <litexlang@outlook.com>
// // Litex website: https://litexlang.com
// // Litex github repository: https://github.com/litexlang/golitex
// // Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_ast

// import "slices"

// func (stmt *SpecFactStmt) GetAtoms() []Atom {
// 	atoms := []Atom{stmt.PropName}
// 	for _, param := range stmt.Params {
// 		atoms = append(atoms, GetAtomObjsInObj(param)...)
// 	}
// 	return atoms
// }

// // func (stmt *EnumStmt) GetAtoms() []Atom {
// // 	atomsOfName := GetAtomsInObj(stmt.CurSet)

// // 	atoms := []Atom{}
// // 	atoms = append(atoms, atomsOfName...)
// // 	for _, value := range stmt.Items {
// // 		atoms = append(atoms, GetAtomsInObj(value)...)
// // 	}
// // 	return atoms
// // }

// func GetAtomObjsInObj(obj Obj) []Atom {
// 	ret := []Atom{}

// 	switch asObj := obj.(type) {
// 	case Atom:
// 		ret = append(ret, asObj)
// 	case *FnObj:
// 		if IsSetBuilder(asObj) {
// 			atomsFromSetBuilder := GetAtomsInSetBuilder(asObj)
// 			ret = append(ret, atomsFromSetBuilder...)
// 		} else {
// 			for _, param := range asObj.Params {
// 				atoms := GetAtomObjsInObj(param)
// 				ret = append(ret, atoms...)
// 			}
// 		}
// 	}
// 	return ret
// }

// func (stmt *UniFactStmt) GetAtoms() []Atom {
// 	atoms := []Atom{}
// 	for _, param := range stmt.ParamSets {
// 		atoms = append(atoms, GetAtomObjsInObj(param)...)
// 	}
// 	for _, fact := range stmt.DomFacts {
// 		atoms = append(atoms, fact.GetAtoms()...)
// 	}
// 	for _, fact := range stmt.ThenFacts {
// 		atoms = append(atoms, fact.GetAtoms()...)
// 	}

// 	// 如果这个atom是param，那把这项扔了
// 	ret := []Atom{}
// 	for _, atom := range atoms {
// 		if slices.Contains(stmt.Params, string(atom)) {
// 			continue
// 		} else {
// 			ret = append(ret, atom)
// 		}
// 	}

// 	return ret
// }

// func (stmt *UniFactWithIffStmt) GetAtoms() []Atom {
// 	atoms := stmt.UniFact.GetAtoms()
// 	for _, fact := range stmt.IffFacts {
// 		atoms = append(atoms, fact.GetAtoms()...)
// 	}
// 	return atoms
// }

// func (stmt *OrStmt) GetAtoms() []Atom {
// 	atoms := []Atom{}
// 	for _, fact := range stmt.Facts {
// 		atoms = append(atoms, fact.GetAtoms()...)
// 	}
// 	return atoms
// }

// // func (stmt *IntensionalSetStmt) GetAtoms() []Atom {
// // 	atoms := []Atom{}
// // 	atoms = append(atoms, GetAtomsInObj(stmt.CurSet)...)
// // 	atoms = append(atoms, GetAtomsInObj(stmt.ParentSet)...)
// // 	for _, proof := range stmt.Facts {
// // 		atoms = append(atoms, proof.GetAtoms()...)
// // 	}
// // 	return atoms
// // }

// func (stmt *EqualsFactStmt) GetAtoms() []Atom {
// 	atoms := []Atom{}
// 	for _, param := range stmt.Params {
// 		atoms = append(atoms, GetAtomObjsInObj(param)...)
// 	}
// 	return atoms
// }

// func GetAtomsInObjIncludingParamInSetBuilder(obj Obj) []Atom {
// 	ret := []Atom{}

// 	switch asObj := obj.(type) {
// 	case Atom:
// 		ret = append(ret, asObj)
// 	case *FnObj:
// 		if IsSetBuilder(asObj) {
// 			atomsFromSetBuilder := GetAtomsInSetBuilderIncludingParamInSetBuilder(asObj)
// 			ret = append(ret, atomsFromSetBuilder...)
// 		} else {
// 			for _, param := range asObj.Params {
// 				atoms := GetAtomObjsInObj(param)
// 				ret = append(ret, atoms...)
// 			}
// 		}
// 	}
// 	return ret
// }

// func GetAtomsInSetBuilder(f *FnObj) []Atom {
// 	// Convert FnObj to SetBuilderStruct for easier processing
// 	setBuilder, err := f.ToSetBuilderStruct()
// 	if err != nil {
// 		panic(err)
// 	}

// 	ret := []Atom{}

// 	// Extract atoms from parentSet (skip the bound parameter)
// 	atoms := GetAtomObjsInObj(setBuilder.ParentSet)
// 	ret = append(ret, atoms...)

// 	// Extract atoms from facts
// 	for _, fact := range setBuilder.Facts {
// 		atoms := fact.GetAtoms()
// 		ret = append(ret, atoms...)
// 	}

// 	// remove the bound parameter itself from the collected atoms
// 	filtered := make([]Atom, 0, len(ret))
// 	for _, param := range ret {
// 		if string(param) == setBuilder.Param {
// 			continue
// 		}
// 		filtered = append(filtered, param)
// 	}

// 	return filtered
// }

// func GetAtomsInSetBuilderIncludingParamInSetBuilder(f *FnObj) []Atom {
// 	// Convert FnObj to SetBuilderStruct for easier processing
// 	setBuilder, err := f.ToSetBuilderStruct()
// 	if err != nil {
// 		panic(err)
// 	}

// 	ret := []Atom{Atom(setBuilder.Param)}

// 	// Extract atoms from parentSet (skip the bound parameter)
// 	atoms := GetAtomObjsInObj(setBuilder.ParentSet)
// 	ret = append(ret, atoms...)

// 	// Extract atoms from facts
// 	for _, fact := range setBuilder.Facts {
// 		atoms := fact.GetAtoms()
// 		ret = append(ret, atoms...)
// 	}

// 	return ret
// }
