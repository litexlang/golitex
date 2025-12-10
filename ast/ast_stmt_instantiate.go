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

import (
	"fmt"
)

func InstantiateObjAtom(obj Atom, uniMap map[string]Obj) (Obj, error) {
	instance, ok := uniMap[string(obj)]
	if ok {
		return instance, nil
	}
	return obj, nil
}

func (obj Atom) Instantiate(uniMap map[string]Obj) (Obj, error) {
	return InstantiateObjAtom(obj, uniMap)
}

func InstantiateObjFn(obj *FnObj, uniMap map[string]Obj) (Obj, error) {
	if IsSetBuilder(obj) {
		return InstantiateIntensionalSetObj(obj, uniMap)
	}

	newHead, err := obj.FnHead.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}

	newParamSegs := make([]Obj, len(obj.Params))
	for i, seg := range obj.Params {
		newSeg, err := seg.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		newParamSegs[i] = newSeg
	}

	return NewFnObj(newHead, newParamSegs), nil
}

func (obj *FnObj) Instantiate(uniMap map[string]Obj) (Obj, error) {
	return InstantiateObjFn(obj, uniMap)
}

func InstantiateSpecFact(stmt *SpecFactStmt, uniMap map[string]Obj) (*SpecFactStmt, error) {
	newParams := []Obj{}
	for _, param := range stmt.Params {
		newParam, err := param.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		newParams = append(newParams, newParam)
	}

	return NewSpecFactStmt(stmt.TypeEnum, stmt.PropName, newParams, stmt.Line), nil
}

func (stmt *SpecFactStmt) InstantiateFact(uniMap map[string]Obj) (FactStmt, error) {
	return InstantiateSpecFact(stmt, uniMap)
}

func InstantiateUniFact(stmt *UniFactStmt, uniMap map[string]Obj) (*UniFactStmt, error) {
	newParams := []string{}
	newParams = append(newParams, stmt.Params...)

	newDomFacts := []FactStmt{}
	for _, fact := range stmt.DomFacts {
		newFact, err := fact.InstantiateFact(uniMap)
		if err != nil {
			return nil, err
		}
		newDomFacts = append(newDomFacts, newFact)
	}

	newThenFacts := []FactStmt{}
	for _, fact := range stmt.ThenFacts {
		newFact, err := fact.InstantiateFact(uniMap)
		if err != nil {
			return nil, err
		}
		newThenFacts = append(newThenFacts, newFact)
	}

	newSetParams := []Obj{}
	for _, setParam := range stmt.ParamSets {
		newSetParam, err := setParam.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		newSetParams = append(newSetParams, newSetParam)
	}

	return NewUniFact(newParams, newSetParams, newDomFacts, newThenFacts, stmt.Line), nil
}

func (stmt *UniFactStmt) InstantiateFact(uniMap map[string]Obj) (FactStmt, error) {
	return InstantiateUniFact(stmt, uniMap)
}

func (defHeader *DefHeader) Instantiate(uniMap map[string]Obj) (*DefHeader, error) {
	newDefHeader := NewDefHeader(defHeader.Name, defHeader.Params, make([]Obj, len(defHeader.ParamSets)))

	for i, setParam := range defHeader.ParamSets {
		newSetParam, err := setParam.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		newDefHeader.ParamSets[i] = newSetParam
	}

	return newDefHeader, nil
}

func (defPropStmt *DefPropStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	newDefHeader, err := defPropStmt.DefHeader.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}

	newDomFacts := []FactStmt{}
	for _, fact := range defPropStmt.DomFacts {
		newFact, err := fact.InstantiateFact(uniMap)
		if err != nil {
			return nil, err
		}
		newDomFacts = append(newDomFacts, newFact)
	}

	newIffFacts := []FactStmt{}
	for _, fact := range defPropStmt.IffFacts {
		newFact, err := fact.InstantiateFact(uniMap)
		if err != nil {
			return nil, err
		}
		newIffFacts = append(newIffFacts, newFact)
	}

	newThenFacts := []FactStmt{}
	for _, fact := range defPropStmt.ThenFacts {
		newFact, err := fact.InstantiateFact(uniMap)
		if err != nil {
			return nil, err
		}
		newThenFacts = append(newThenFacts, newFact)
	}
	return NewDefPropStmt(newDefHeader, newDomFacts, newIffFacts, newThenFacts, defPropStmt.Line), nil
}

func (stmt *DefExistPropStmtBody) Instantiate(uniMap map[string]Obj) (*DefExistPropStmtBody, error) {
	newDefHeader, err := stmt.DefHeader.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}

	newDomFacts := []FactStmt{}
	for _, fact := range stmt.DomFacts {
		newFact, err := fact.InstantiateFact(uniMap)
		if err != nil {
			return nil, err
		}
		newDomFacts = append(newDomFacts, newFact)
	}

	newIffFacts := []FactStmt{}
	for _, fact := range stmt.IffFacts {
		newFact, err := fact.InstantiateFact(uniMap)
		if err != nil {
			return nil, err
		}
		newIffFacts = append(newIffFacts, newFact)
	}

	newThenFacts := []FactStmt{}
	for _, fact := range stmt.ThenFacts {
		newFact, err := fact.InstantiateFact(uniMap)
		if err != nil {
			return nil, err
		}
		newIffFacts = append(newThenFacts, newFact)
	}

	return NewDefExistPropBodyStmt(newDefHeader, newDomFacts, newIffFacts, newThenFacts, stmt.Line), nil
}

func (stmt *DefExistPropStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	newDefExistPropBody, err := stmt.DefBody.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}

	newExistParamSets := []Obj{}
	for _, setParam := range stmt.ExistParamSets {
		newSetParam, err := setParam.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		newExistParamSets = append(newExistParamSets, newSetParam)
	}

	return NewDefExistPropStmt(newDefExistPropBody, stmt.ExistParams, newExistParamSets, stmt.Line), nil
}

func (stmt *DefExistPropStmt) ExistParamInSetsFacts() []FactStmt {
	facts := []FactStmt{}
	for i, param := range stmt.ExistParams {
		facts = append(facts, NewInFact(param, stmt.ExistParamSets[i]))
	}
	return facts
}

func (stmt *OrStmt) InstantiateFact(uniMap map[string]Obj) (FactStmt, error) {
	newOrFacts := make([]*SpecFactStmt, len(stmt.Facts))
	for i, fact := range stmt.Facts {
		newFact, err := fact.InstantiateFact(uniMap)
		if err != nil {
			return nil, err
		}
		newOrFacts[i] = newFact.(*SpecFactStmt)
	}

	return NewOrStmt(newOrFacts, stmt.Line), nil
}

func (stmt *UniFactWithIffStmt) InstantiateFact(uniMap map[string]Obj) (FactStmt, error) {
	newUniFact, err := stmt.UniFact.InstantiateFact(uniMap)
	if err != nil {
		return nil, err
	}

	instantiatedIffFacts := []FactStmt{}
	for _, fact := range stmt.IffFacts {
		newFact, err := fact.InstantiateFact(uniMap)
		if err != nil {
			return nil, err
		}
		instantiatedIffFacts = append(instantiatedIffFacts, newFact)
	}

	return NewUniFactWithIff(newUniFact.(*UniFactStmt), instantiatedIffFacts, stmt.Line), nil
}

// func (stmt *EnumStmt) InstantiateFact(uniMap map[string]Obj) (FactStmt, error) {
// 	enumName, err := stmt.CurSet.Instantiate(uniMap)
// 	if err != nil {
// 		return nil, err
// 	}

// 	newEnumValues := []Obj{}
// 	for _, value := range stmt.Items {
// 		newValue, err := value.Instantiate(uniMap)
// 		if err != nil {
// 			return nil, err
// 		}
// 		newEnumValues = append(newEnumValues, newValue)
// 	}

// 	return NewEnumStmt(enumName, newEnumValues, stmt.Line), nil
// }

// func (stmt *IntensionalSetStmt) InstantiateFact(uniMap map[string]Obj) (FactStmt, error) {
// 	newCurSet, err := stmt.CurSet.Instantiate(uniMap)
// 	if err != nil {
// 		return nil, err
// 	}

// 	newParentSet, err := stmt.ParentSet.Instantiate(uniMap)
// 	if err != nil {
// 		return nil, err
// 	}

// 	newProofs := make([]*SpecFactStmt, len(stmt.Facts))
// 	for i, proof := range stmt.Facts {
// 		newProof, err := proof.InstantiateFact(uniMap)
// 		if err != nil {
// 			return nil, err
// 		}
// 		newProofs[i] = newProof.(*SpecFactStmt)
// 	}

// 	return NewIntensionalSetStmt(newCurSet, stmt.Param, newParentSet, newProofs, stmt.Line), nil
// }

func (stmt *EqualsFactStmt) InstantiateFact(uniMap map[string]Obj) (FactStmt, error) {
	newParams := []Obj{}
	for _, param := range stmt.Params {
		newParam, err := param.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		newParams = append(newParams, newParam)
	}
	return NewEqualsFactStmt(newParams, stmt.Line), nil
}

func (objSlice ObjSlice) Instantiate(uniMap map[string]Obj) (ObjSlice, error) {
	newObjSlice := make([]Obj, len(objSlice))
	for i, obj := range objSlice {
		newObj, err := obj.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		newObjSlice[i] = newObj
	}
	return newObjSlice, nil
}

func (s SpecFactPtrSlice) Instantiate(uniMap map[string]Obj) (SpecFactPtrSlice, error) {
	newSpecFactPtrSlice := make([]*SpecFactStmt, len(s))
	for i, specFactPtr := range s {
		newSpecFactPtr, err := specFactPtr.InstantiateFact(uniMap)
		if err != nil {
			return nil, err
		}
		newSpecFactPtrSlice[i] = newSpecFactPtr.(*SpecFactStmt)
	}
	return newSpecFactPtrSlice, nil
}

func (stmt *DefLetStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	newObjSets := []Obj{}
	for _, objSet := range stmt.ObjSets {
		newObjSet, err := objSet.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		newObjSets = append(newObjSets, newObjSet)
	}
	return NewDefLetStmt(stmt.Objs, newObjSets, stmt.Facts, stmt.Line), nil
}

func (stmt *DefFnStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	fnTemplateInstantiated, err := stmt.FnTemplate.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	return NewDefFnStmt(stmt.Name, fnTemplateInstantiated, stmt.Line), nil
}

func (s StmtSlice) Instantiate(uniMap map[string]Obj) (StmtSlice, error) {
	newStmts := make([]Stmt, len(s))
	for i, stmt := range s {
		newStmt, err := stmt.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		newStmts[i] = newStmt
	}
	return newStmts, nil
}

func (stmt *ClaimProveStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	newToCheckFact, err := stmt.ToCheckFact.InstantiateFact(uniMap)
	if err != nil {
		return nil, err
	}
	newProofs, err := stmt.Proofs.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	return NewClaimProveStmt(newToCheckFact, newProofs, stmt.Line), nil
}

func (stmt *ClaimProveByContradictionStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	newClaimProveStmt, err := stmt.ClaimProveStmt.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	return NewClaimProveByContradictionStmt(newClaimProveStmt.(*ClaimProveStmt), stmt.Line), nil
}

func (stmt *ClaimPropStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	newProp, err := stmt.Prop.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	newProofs, err := stmt.Proofs.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	return NewClaimPropStmt(newProp.(*DefPropStmt), newProofs, stmt.Line), nil
}

func (stmt CanBeKnownStmtSlice) Instantiate(uniMap map[string]Obj) (CanBeKnownStmtSlice, error) {
	newFacts := []CanBeKnownStmt{}
	for _, fact := range stmt {
		newFact, err := fact.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		newFacts = append(newFacts, newFact.(CanBeKnownStmt))
	}
	return newFacts, nil
}

func (stmt *KnowFactStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	newFacts, err := stmt.Facts.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	return NewKnowStmt(newFacts, stmt.Line), nil
}

func (stmt *KnowPropStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	newProp, err := stmt.Prop.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	return NewKnowPropStmt(newProp.(*DefPropStmt), stmt.Line), nil
}

func (stmt *ClaimExistPropStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	newExistProp, err := stmt.ExistPropWithoutDom.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	newProofs, err := stmt.Proofs.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	haveObjInstantiated, err := stmt.HaveObj.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	return NewClaimExistPropStmt(newExistProp.(*DefExistPropStmt), newProofs, haveObjInstantiated, stmt.Line), nil
}

func (stmt *HaveObjStStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	newFact, err := stmt.Fact.InstantiateFact(uniMap)
	if err != nil {
		return nil, err
	}
	return NewHaveStmt(stmt.ObjNames, newFact.(*SpecFactStmt), stmt.Line), nil
}

func (stmt *ProveInEachCaseStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	newOrFact, err := stmt.OrFact.InstantiateFact(uniMap)
	if err != nil {
		return nil, err
	}
	newThenFacts, err := stmt.ThenFacts.InstantiateFact(uniMap)
	if err != nil {
		return nil, err
	}
	newProofs := StmtSliceSlice{}
	for _, proof := range stmt.Proofs {
		newProof, err := proof.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		newProofs = append(newProofs, newProof)
	}
	return NewProveInEachCaseStmt(newOrFact.(*OrStmt), newThenFacts, newProofs, stmt.Line), nil
}

func (stmt *ProveCaseByCaseStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	newCaseFacts := []*SpecFactStmt{}
	for _, caseFact := range stmt.CaseFacts {
		newCaseFact, err := caseFact.InstantiateFact(uniMap)
		if err != nil {
			return nil, err
		}
		newCaseFacts = append(newCaseFacts, newCaseFact.(*SpecFactStmt))
	}

	newThenFacts := []FactStmt{}
	for _, thenFact := range stmt.ThenFacts {
		newThenFact, err := thenFact.InstantiateFact(uniMap)
		if err != nil {
			return nil, err
		}
		newThenFacts = append(newThenFacts, newThenFact)
	}

	newProofs := StmtSliceSlice{}
	for _, proof := range stmt.Proofs {
		newProof := StmtSlice{}
		for _, stmt := range proof {
			newStmt, err := stmt.Instantiate(uniMap)
			if err != nil {
				return nil, err
			}
			newProof = append(newProof, newStmt)
		}
		newProofs = append(newProofs, newProof)
	}
	return NewProveCaseByCaseStmt(newCaseFacts, newThenFacts, newProofs, stmt.Line), nil
}

func (stmt *ImportDirStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	return stmt, nil
}

func (stmt *ImportFileStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	return stmt, nil
}

func (stmt *ProveStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	newProofs, err := stmt.Proof.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	return NewProveStmt(newProofs, stmt.Line), nil
}

func (stmt *ProveByEnumStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	newFact, err := stmt.Fact.InstantiateFact(uniMap)
	if err != nil {
		return nil, err
	}
	newProofs, err := stmt.Proof.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	return NewProveByEnumStmt(newFact.(*UniFactStmt), newProofs, stmt.Line), nil
}

func (stmt *HaveObjInNonEmptySetStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	newObjSets, err := stmt.ObjSets.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	return NewHaveObjInNonEmptySetStmt(stmt.Objs, newObjSets, stmt.Line), nil
}

func (stmt *HaveEnumSetStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	newEnumSetObj, err := stmt.EnumSetObj.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	return NewHaveEnumSetStmt(stmt.Name, newEnumSetObj.(*FnObj), stmt.Line), nil
}

func (stmt *HaveIntensionalSetStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	newParentSet, err := stmt.ParentSet.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	newFacts, err := stmt.Facts.InstantiateFact(uniMap)
	if err != nil {
		return nil, err
	}

	return NewHaveIntensionalSetStmt(stmt.Param, newParentSet, newFacts, stmt.Line), nil
}

func (stmt *HaveCartSetStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	newCartObj, err := stmt.CartObj.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	cartObj, ok := newCartObj.(*FnObj)
	if !ok {
		return nil, fmt.Errorf("expected cart object to be FnObj after instantiation")
	}
	return NewHaveCartSetStmt(stmt.Name, cartObj, stmt.Line), nil
}

func (stmt *HaveObjFromCartSetStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	newCartSet, err := stmt.CartSet.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	cartSet, ok := newCartSet.(*FnObj)
	if !ok {
		return nil, fmt.Errorf("expected cart set to be FnObj after instantiation")
	}
	newEqualTo, err := stmt.EqualTo.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	return NewHaveObjFromCartSetStmt(stmt.ObjName, cartSet, newEqualTo, stmt.Line), nil
}

func (stmt *HaveCartWithDimStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	newCartDim, err := stmt.CartDim.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	newFacts := make(FactStmtSlice, len(stmt.Facts))
	for i, fact := range stmt.Facts {
		newFact, err := fact.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		newFacts[i] = newFact.(FactStmt)
	}
	newProofs := make(StmtSlice, len(stmt.Proofs))
	for i, proof := range stmt.Proofs {
		newProof, err := proof.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		newProofs[i] = newProof
	}
	newEqualTo, err := stmt.EqualTo.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	return NewHaveCartWithDimStmt(stmt.ObjName, newCartDim, stmt.Param, newFacts, newProofs, newEqualTo, stmt.Line), nil
}

func (stmt *NamedUniFactStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	newProp, err := stmt.DefPropStmt.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	return NewNamedUniFactStmt(newProp.(*DefPropStmt), stmt.Line), nil
}

func (stmt *EqualsFactStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	newParams, err := stmt.Params.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	return NewEqualsFactStmt(newParams, stmt.Line), nil
}

func (stmt *KnowExistPropStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	newExistProp, err := stmt.ExistProp.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	return NewKnowExistPropStmt(newExistProp.(*DefExistPropStmt), stmt.Line), nil
}

// func (stmt *LatexStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
// 	return stmt, nil
// }

func (stmt *FnTemplateDefStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	newTemplateDefHeader, err := stmt.TemplateDefHeader.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	newTemplateDomFacts, err := stmt.TemplateDomFacts.InstantiateFact(uniMap)
	if err != nil {
		return nil, err
	}
	newFn, err := stmt.Fn.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	return NewFnTemplateStmt(newTemplateDefHeader, newTemplateDomFacts, newFn, stmt.Line), nil
}

func (stmt *ClearStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	return stmt, nil
}

func (stmt *DoNothingStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	return stmt, nil
}

func (stmt *InlineFactsStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	newFacts, err := stmt.Facts.InstantiateFact(uniMap)
	if err != nil {
		return nil, err
	}
	return NewInlineFactsStmt(newFacts, stmt.Line), nil
}

func (stmt *ProveByInductionStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	newFact, err := stmt.Fact.InstantiateFact(uniMap)
	if err != nil {
		return nil, err
	}
	newStart, err := stmt.Start.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	return NewProveByInductionStmt(newFact.(*SpecFactStmt), stmt.Param, newStart, stmt.Line), nil
}

func (stmt *HaveObjEqualStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	newObjEqualTos, err := stmt.ObjEqualTos.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	newObjSets, err := stmt.ObjSets.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	return NewHaveObjEqualStmt(stmt.ObjNames, newObjEqualTos, newObjSets, stmt.Line), nil
}

func (stmt *HaveFnEqualStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	newDefHeader, err := stmt.DefHeader.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	newRetSet, err := stmt.RetSet.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	newEqualTo, err := stmt.EqualTo.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	return NewHaveFnEqualStmt(newDefHeader, newRetSet, newEqualTo, stmt.Line), nil
}

// func (stmt *HaveFnLiftStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
// 	newOpt, err := stmt.Opt.Instantiate(uniMap)
// 	if err != nil {
// 		return nil, err
// 	}
// 	newDomainOfEachParamOfGivenFn, err := stmt.DomainOfEachParamOfGivenFn.Instantiate(uniMap)
// 	if err != nil {
// 		return nil, err
// 	}
// 	return NewHaveFnLiftStmt(stmt.FnName, newOpt, newDomainOfEachParamOfGivenFn, stmt.Line), nil
// }

func (stmt *HaveFnStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	newDefFnStmt, err := stmt.DefFnStmt.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	newProofs, err := stmt.Proofs.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	newHaveObjSatisfyFn, err := stmt.HaveObjSatisfyFn.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	return NewClaimHaveFnStmt(newDefFnStmt.(*DefFnStmt), newProofs, newHaveObjSatisfyFn, stmt.Line), nil
}

func (stmt *HaveFnCaseByCaseStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	newDefFnStmt, err := stmt.DefFnStmt.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	newCaseByCaseFacts, err := stmt.CaseByCaseFacts.InstantiateFact(uniMap)
	if err != nil {
		return nil, err
	}
	newProofs := make(StmtSliceSlice, len(stmt.Proofs))
	for i, proof := range stmt.Proofs {
		newProof, err := proof.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		newProofs[i] = newProof
	}
	newHaveObjSatisfyFn := make([]Obj, len(stmt.EqualToObjs))
	for i, obj := range stmt.EqualToObjs {
		newObj, err := obj.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		newHaveObjSatisfyFn[i] = newObj
	}
	return NewHaveFnCaseByCaseStmt(newDefFnStmt.(*DefFnStmt), newCaseByCaseFacts, newProofs, newHaveObjSatisfyFn, stmt.Line), nil
}

// func (stmt *MarkdownStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
// 	return stmt, nil
// }

// func (stmt *ProveInRangeSetStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
// 	newIntensionalSet, err := stmt.IntensionalSet.Instantiate(uniMap)
// 	if err != nil {
// 		return nil, err
// 	}
// 	newThenFacts, err := stmt.ThenFacts.InstantiateFact(uniMap)
// 	if err != nil {
// 		return nil, err
// 	}
// 	newProofs, err := stmt.Proofs.Instantiate(uniMap)
// 	if err != nil {
// 		return nil, err
// 	}
// 	return NewProveInRangeSetStmt(stmt.Start, stmt.End, stmt.Param, newIntensionalSet, newThenFacts, newProofs, stmt.Line), nil
// }

func (stmt *ProveInRangeStmt2) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	newStart, err := stmt.start.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	newEnd, err := stmt.end.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	newDomFacts, err := stmt.DomFactsOrNil.InstantiateFact(uniMap)
	if err != nil {
		return nil, err
	}
	newThenFacts, err := stmt.ThenFacts.InstantiateFact(uniMap)
	if err != nil {
		return nil, err
	}
	newProofs, err := stmt.ProofsOrNil.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	return NewProveInRangeStmt(stmt.param, newStart, newEnd, newDomFacts, newThenFacts, newProofs, stmt.Line), nil
}

func (stmt *ClaimIffStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	newUniFactWithIffStmt, err := stmt.UniFactWithIffStmt.InstantiateFact(uniMap)
	if err != nil {
		return nil, err
	}
	newProofThenToIff, err := stmt.ProofThenToIff.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	newProofIffToThen, err := stmt.ProofIffToThen.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	return NewClaimIffStmt(newUniFactWithIffStmt.(*UniFactWithIffStmt), newProofThenToIff, newProofIffToThen, stmt.Line), nil
}

func (stmt *ProveIsTransitivePropStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	newProofs, err := stmt.Proofs.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	return NewProveIsTransitivePropStmt(stmt.Prop, stmt.Params, newProofs, stmt.Line), nil
}

func (stmt *ProveIsCommutativePropStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	newProofs, err := stmt.Proofs.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	newProofsRightToLeft, err := stmt.ProofsRightToLeft.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	return NewProveIsCommutativePropStmt(stmt.SpecFact, newProofs, newProofsRightToLeft, stmt.Line), nil
}

func InstantiateAlgoStmt(stmt AlgoStmt, uniMap map[string]Obj) (AlgoStmt, error) {
	switch stmt := stmt.(type) {
	case *AlgoIfStmt:
		return stmt.InstantiateAlgo(uniMap)
	case *AlgoReturnStmt:
		return stmt.InstantiateAlgo(uniMap)
	case Stmt:
		return stmt.Instantiate(uniMap)
	}
	return nil, fmt.Errorf("unknown algo statement type: %T", stmt)
}

func InstantiateProveAlgoStmt(stmt ProveAlgoStmt, uniMap map[string]Obj) (ProveAlgoStmt, error) {
	switch stmt := stmt.(type) {
	case *ProveAlgoIfStmt:
		return stmt.InstantiateProveAlgo(uniMap)
	case *ProveAlgoReturnStmt:
		return stmt.InstantiateProveAlgo(uniMap)
	}
	return nil, fmt.Errorf("unknown prove algo statement type: %T", stmt)
}

func (s AlgoStmtSlice) Instantiate(uniMap map[string]Obj) (AlgoStmtSlice, error) {
	newStmts := make([]AlgoStmt, len(s))
	for i, stmt := range s {
		newStmt, err := InstantiateAlgoStmt(stmt, uniMap)
		if err != nil {
			return nil, err
		}
		newStmts[i] = newStmt
	}
	return newStmts, nil
}

func (stmt *AlgoIfStmt) InstantiateAlgo(uniMap map[string]Obj) (AlgoStmt, error) {
	newConditions, err := stmt.Conditions.InstantiateFact(uniMap)
	if err != nil {
		return nil, err
	}
	newThenStmts, err := stmt.ThenStmts.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	return NewAlgoIfStmt(newConditions, newThenStmts, stmt.Line), nil
}

func (stmt *AlgoReturnStmt) InstantiateAlgo(uniMap map[string]Obj) (AlgoStmt, error) {
	newValue, err := stmt.Value.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	return NewAlgoReturnStmt(newValue, stmt.Line), nil
}

func (stmt *DefAlgoStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	newStmts, err := stmt.Stmts.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	return NewAlgoDefStmt(stmt.FuncName, stmt.Params, newStmts, stmt.Line), nil
}

func (stmt *EvalStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	obj, err := stmt.ObjToEval.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	return NewEvalStmt(obj, stmt.Line), nil
}

func (stmt *SpecFactStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	return stmt.InstantiateFact(uniMap)
}

func (stmt *UniFactStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	return stmt.InstantiateFact(uniMap)
}

func (stmt *UniFactWithIffStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	return stmt.InstantiateFact(uniMap)
}

func (stmt *OrStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	return stmt.InstantiateFact(uniMap)
}

// func (stmt *EnumStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
// 	return stmt.InstantiateFact(uniMap)
// }

// func (stmt *IntensionalSetStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
// 	return stmt.InstantiateFact(uniMap)
// }

func (stmt *DefProveAlgoStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	newStmts, err := stmt.Stmts.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	return NewDefProveAlgoStmt(stmt.ProveAlgoName, stmt.Params, newStmts, stmt.Line), nil
}

func (s ProveAlgoStmtSlice) Instantiate(uniMap map[string]Obj) (ProveAlgoStmtSlice, error) {
	newStmts := make([]ProveAlgoStmt, len(s))
	for i, stmt := range s {
		newStmt, err := InstantiateProveAlgoStmt(stmt, uniMap)
		if err != nil {
			return nil, err
		}
		newStmts[i] = newStmt
	}
	return newStmts, nil
}

func (stmt *ProveAlgoIfStmt) InstantiateProveAlgo(uniMap map[string]Obj) (ProveAlgoStmt, error) {
	newConditions, err := stmt.Conditions.InstantiateFact(uniMap)
	if err != nil {
		return nil, err
	}
	newThenStmts, err := stmt.ThenStmts.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	return NewProveAlgoIfStmt(newConditions, newThenStmts, stmt.Line), nil
}

func (stmt *ByStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	newProveAlgoParams, err := stmt.Params.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	return NewByStmt(stmt.ProveAlgoName, newProveAlgoParams, stmt.Line), nil
}

func (stmt *ProveAlgoReturnStmt) InstantiateProveAlgo(uniMap map[string]Obj) (ProveAlgoStmt, error) {
	instFacts := FactOrByStmtSlice{}
	for _, factOrBy := range stmt.Facts {
		instFactOrBy, err := factOrBy.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		// instFactOrBy is a Stmt, need to convert to FactOrByStmt
		switch item := instFactOrBy.(type) {
		case FactStmt:
			instFacts = append(instFacts, item)
		case *ByStmt:
			instFacts = append(instFacts, item)
		default:
			return nil, fmt.Errorf("unexpected type after instantiate: %T", instFactOrBy)
		}
	}
	return NewProveAlgoReturnStmt(instFacts, stmt.GetLine()), nil
}

func (specFactPtrSlice SpecFactPtrSlice) InstantiateFact(uniMap map[string]Obj) (SpecFactPtrSlice, error) {
	newSpecFactPtrSlice := make([]*SpecFactStmt, len(specFactPtrSlice))
	for i, specFactPtr := range specFactPtrSlice {
		newSpecFactPtr, err := specFactPtr.InstantiateFact(uniMap)
		if err != nil {
			return nil, err
		}
		newSpecFactPtrSlice[i] = newSpecFactPtr.(*SpecFactStmt)
	}
	return newSpecFactPtrSlice, nil
}

// TODO: 在eval时，这里的token可能因为没有实例化而有问题
func (stmt *PrintStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	return stmt, nil
}

func (stmt *HelpStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	return stmt, nil
}

func (stmt *HaveFnEqualCaseByCaseStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	newDefHeader, err := stmt.DefHeader.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	newRetSet, err := stmt.RetSet.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	newCaseByCaseFacts, err := stmt.CaseByCaseFacts.InstantiateFact(uniMap)
	if err != nil {
		return nil, err
	}
	newCaseByCaseEqualTo, err := stmt.CaseByCaseEqualTo.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	return &HaveFnEqualCaseByCaseStmt{newDefHeader, newRetSet, newCaseByCaseFacts, newCaseByCaseEqualTo, stmt.Line}, nil
}

func InstantiateIntensionalSetObj(obj *FnObj, uniMap map[string]Obj) (Obj, error) {
	// Convert FnObj to IntensionalSetObj
	intensionalSet, err := obj.ToSetBuilderStruct()
	if err != nil {
		return nil, err
	}

	// Avoid capturing the bound parameter during instantiation.
	// If uniMap contains the param, create a new map without it to prevent substitution.
	innerUniMap := uniMap
	if _, ok := uniMap[intensionalSet.Param]; ok {
		innerUniMap = make(map[string]Obj, len(uniMap)-1)
		for k, v := range uniMap {
			if k == intensionalSet.Param {
				continue
			}
			innerUniMap[k] = v
		}
	}

	// Instantiate parent set
	instParentSet, err := intensionalSet.ParentSet.Instantiate(innerUniMap)
	if err != nil {
		return nil, err
	}

	// Instantiate facts
	instFacts := make(SpecFactPtrSlice, len(intensionalSet.Facts))
	for i, fact := range intensionalSet.Facts {
		instFact, err := fact.InstantiateFact(innerUniMap)
		if err != nil {
			return nil, err
		}
		specFact, ok := instFact.(*SpecFactStmt)
		if !ok {
			return nil, fmt.Errorf("expected SpecFactStmt, got %T", instFact)
		}
		instFacts[i] = specFact
	}

	// Create new IntensionalSetObj with instantiated components
	instIntensionalSet := &SetBuilderStruct{
		Param:     intensionalSet.Param, // Keep the bound parameter unchanged
		ParentSet: instParentSet,
		Facts:     instFacts,
	}

	// Convert back to FnObj
	return instIntensionalSet.ToFnObj()
}
