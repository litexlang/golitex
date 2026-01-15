// Copyright Jiachen Shen.
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
		return InstantiateSetBuilderObjWithoutChangingParam(obj, uniMap)
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

	return NewSpecFactStmt(stmt.FactType, stmt.PropName, newParams, stmt.Line), nil
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
	for _, fact := range defPropStmt.DomFactsOrNil {
		newFact, err := fact.InstantiateFact(uniMap)
		if err != nil {
			return nil, err
		}
		newDomFacts = append(newDomFacts, newFact)
	}

	newIffFacts := []FactStmt{}
	for _, fact := range defPropStmt.IffFactsOrNil {
		newFact, err := fact.InstantiateFact(uniMap)
		if err != nil {
			return nil, err
		}
		newIffFacts = append(newIffFacts, newFact)
	}

	newThenFacts := []FactStmt{}
	for _, fact := range defPropStmt.ImplicationFactsOrNil {
		newFact, err := fact.InstantiateFact(uniMap)
		if err != nil {
			return nil, err
		}
		newThenFacts = append(newThenFacts, newFact)
	}
	return NewDefPropStmt(newDefHeader, newDomFacts, newIffFacts, newThenFacts, defPropStmt.Line), nil
}

// func (stmt *DefExistPropStmtBody) Instantiate(uniMap map[string]Obj) (*DefExistPropStmtBody, error) {
// 	newDefHeader, err := stmt.DefHeader.Instantiate(uniMap)
// 	if err != nil {
// 		return nil, err
// 	}

// 	newDomFacts := []FactStmt{}
// 	for _, fact := range stmt.DomFactsOrNil {
// 		newFact, err := fact.InstantiateFact(uniMap)
// 		if err != nil {
// 			return nil, err
// 		}
// 		newDomFacts = append(newDomFacts, newFact)
// 	}

// 	newIffFacts := []FactStmt{}
// 	for _, fact := range stmt.IffFactsOrNil {
// 		newFact, err := fact.InstantiateFact(uniMap)
// 		if err != nil {
// 			return nil, err
// 		}
// 		newIffFacts = append(newIffFacts, newFact)
// 	}

// 	newThenFacts := []FactStmt{}
// 	for _, fact := range stmt.ImplicationFactsOrNil {
// 		newFact, err := fact.InstantiateFact(uniMap)
// 		if err != nil {
// 			return nil, err
// 		}
// 		newIffFacts = append(newThenFacts, newFact)
// 	}

// 	return NewDefExistPropBodyStmt(newDefHeader, newDomFacts, newIffFacts, newThenFacts, stmt.Line), nil
// }

// func (stmt *DefExistPropStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
// 	newDefExistPropBody, err := stmt.DefBody.Instantiate(uniMap)
// 	if err != nil {
// 		return nil, err
// 	}

// 	newExistParamSets := []Obj{}
// 	for _, setParam := range stmt.ExistParamSets {
// 		newSetParam, err := setParam.Instantiate(uniMap)
// 		if err != nil {
// 			return nil, err
// 		}
// 		newExistParamSets = append(newExistParamSets, newSetParam)
// 	}

// 	return NewDefExistPropStmt(newDefExistPropBody, stmt.ExistParams, newExistParamSets, stmt.Line), nil
// }

// func (stmt *DefExistPropStmt) ExistParamInSetsFacts() []FactStmt {
// 	facts := []FactStmt{}
// 	for i, param := range stmt.ExistParams {
// 		facts = append(facts, NewInFact(param, stmt.ExistParamSets[i]))
// 	}
// 	return facts
// }

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

func (stmt *LetFnStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	fnTemplateInstantiated, err := stmt.FnTemplate.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	return NewLetFnStmt(stmt.Name, fnTemplateInstantiated, stmt.Line), nil
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

func (stmt *ImpossibleStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	newFact, err := stmt.Fact.InstantiateFact(uniMap)
	if err != nil {
		return nil, err
	}
	return NewImpossibleStmt(newFact.(*SpecFactStmt), stmt.Line), nil
}

func (stmt *ClaimProveByContradictionStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	newClaimProveStmt, err := stmt.ClaimProveStmt.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	return NewClaimProveByContradictionStmt(newClaimProveStmt.(*ClaimProveStmt), stmt.Line), nil
}

func (stmt *ClaimImplicationStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	newImplication, err := stmt.Implication.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	newProofs, err := stmt.Proofs.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	return NewClaimPropStmt(newImplication.(*DefPropStmt), newProofs, stmt.Line), nil
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

func (stmt *KnowPropInferStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	newProp, err := stmt.DefProp.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	return NewKnowPropInferStmt(newProp.(*DefPropStmt), stmt.Line), nil
}

func (stmt *KnowInferStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	// Instantiate ParamSets
	newParamSets, err := stmt.ParamSets.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}

	domFacts := ReversibleFacts{}
	for _, fact := range stmt.DomFacts {
		newFact, err := fact.InstantiateFact(uniMap)
		if err != nil {
			return nil, err
		}
		domFacts = append(domFacts, newFact.(Spec_OrFact))
	}

	// Instantiate DomFacts
	// Instantiate ThenFacts
	thenFacts := ReversibleFacts{}
	for _, fact := range stmt.ThenFacts {
		newFact, err := fact.InstantiateFact(uniMap)
		if err != nil {
			return nil, err
		}
		thenFacts = append(thenFacts, newFact.(Spec_OrFact))
	}

	// Instantiate IfFacts
	newIfFacts, err := stmt.IfFacts.InstantiateFact(uniMap)
	if err != nil {
		return nil, err
	}

	return NewKnowInferStmt(stmt.Params, newParamSets, domFacts, thenFacts, newIfFacts, stmt.Line), nil
}

// func (stmt *ClaimExistPropStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
// 	newExistProp, err := stmt.ExistPropWithoutDom.Instantiate(uniMap)
// 	if err != nil {
// 		return nil, err
// 	}
// 	newProofs, err := stmt.Proofs.Instantiate(uniMap)
// 	if err != nil {
// 		return nil, err
// 	}
// 	haveObjInstantiated, err := stmt.HaveObj.Instantiate(uniMap)
// 	if err != nil {
// 		return nil, err
// 	}
// 	return NewClaimExistPropStmt(newExistProp.(*DefExistPropStmt), newProofs, haveObjInstantiated, stmt.Line), nil
// }

// func (stmt *HaveObjStStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
// 	newFact, err := stmt.Fact.InstantiateFact(uniMap)
// 	if err != nil {
// 		return nil, err
// 	}
// 	return NewHaveObjStStmt(stmt.ObjNames, newFact.(*SpecFactStmt), stmt.Line), nil
// }

func (stmt *HaveObjStStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	newFact, err := stmt.Fact.InstantiateFact(uniMap)
	if err != nil {
		return nil, err
	}
	newObjSets, err := stmt.ObjSets.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	return NewHaveObjStWithParamSetsStmt(stmt.ObjNames, newObjSets, newFact.(*SpecFactStmt), stmt.Line), nil
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
	newProveOr, err := stmt.ProveCases.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	return NewProveCaseByCaseStmt(newCaseFacts, newThenFacts, newProofs, newProveOr, stmt.Line), nil
}

func (stmt *ImportDirStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	return stmt, nil
}

func (stmt *RunFileStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
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

// func (stmt *HaveObjFromCartSetStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
// 	newCartSet, err := stmt.CartSet.Instantiate(uniMap)
// 	if err != nil {
// 		return nil, err
// 	}
// 	cartSet, ok := newCartSet.(*FnObj)
// 	if !ok {
// 		return nil, fmt.Errorf("expected cart set to be FnObj after instantiation")
// 	}
// 	newEqualTo, err := stmt.EqualTo.Instantiate(uniMap)
// 	if err != nil {
// 		return nil, err
// 	}
// 	return NewHaveObjFromCartSetStmt(stmt.ObjName, cartSet, newEqualTo, stmt.Line), nil
// }

// func (stmt *NamedUniFactStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
// 	newProp, err := stmt.DefPropStmt.Instantiate(uniMap)
// 	if err != nil {
// 		return nil, err
// 	}
// 	return NewNamedUniFactStmt(newProp.(*DefPropStmt), stmt.Line), nil
// }

func (stmt *EqualsFactStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	newParams, err := stmt.Params.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	return NewEqualsFactStmt(newParams, stmt.Line), nil
}

// func (stmt *KnowExistPropStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
// 	newExistProp, err := stmt.ExistProp.Instantiate(uniMap)
// 	if err != nil {
// 		return nil, err
// 	}
// 	return NewKnowExistPropStmt(newExistProp.(*DefExistPropStmt), stmt.Line), nil
// }

// func (stmt *LatexStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
// 	return stmt, nil
// }

func (stmt *DefFnSetStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	newTemplateDefHeader, err := stmt.TemplateDefHeader.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	newTemplateDomFacts, err := stmt.TemplateDomFacts.InstantiateFact(uniMap)
	if err != nil {
		return nil, err
	}
	newFn, err := stmt.AnonymousFn.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	return NewDefFnSetStmt(newTemplateDefHeader, newTemplateDomFacts, newFn, stmt.Line), nil
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
	newProof := make(StmtSlice, len(stmt.Proof))
	for i, proofStmt := range stmt.Proof {
		newProofStmt, err := proofStmt.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		newProof[i] = newProofStmt
	}
	return NewProveByInductionStmt(newFact, stmt.Param, newProof, stmt.Line), nil
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
	newProofs, err := stmt.Proofs.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	return NewHaveFnEqualStmt(newDefHeader, newRetSet, newEqualTo, newProofs, stmt.Line), nil
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
	return NewClaimHaveFnStmt(newDefFnStmt.(*LetFnStmt), newProofs, newHaveObjSatisfyFn, stmt.Line), nil
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
	newProveOr, err := stmt.ProveCases.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	return NewHaveFnCaseByCaseStmt(newDefFnStmt.(*LetFnStmt), newCaseByCaseFacts, newProofs, newHaveObjSatisfyFn, newProveOr, stmt.Line), nil
}

func (stmt *ProveForStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	newLefts := make([]Obj, len(stmt.Lefts))
	for i, left := range stmt.Lefts {
		newLeft, err := left.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		newLefts[i] = newLeft
	}

	newRights := make([]Obj, len(stmt.Rights))
	for i, right := range stmt.Rights {
		newRight, err := right.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		newRights[i] = newRight
	}

	newDomFacts, err := stmt.DomFacts.InstantiateFact(uniMap)
	if err != nil {
		return nil, err
	}
	newThenFacts, err := stmt.ThenFacts.InstantiateFact(uniMap)
	if err != nil {
		return nil, err
	}
	newProofs, err := stmt.Proofs.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	return NewProveForStmt(stmt.Params, newLefts, newRights, stmt.IsProveIRange, newDomFacts, newThenFacts, newProofs, stmt.Line), nil
}

func (stmt *ProveInferStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	newImplicationFacts, err := stmt.ImplicationFact.InstantiateFact(uniMap)
	if err != nil {
		return nil, err
	}
	newProofs, err := stmt.Proofs.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	return NewProveImplicationStmt(stmt.SpecFact, newImplicationFacts, newProofs, stmt.Line), nil
}

// func (stmt *DefImplicationStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
// 	newDefHeader, err := stmt.DefHeader.Instantiate(uniMap)
// 	if err != nil {
// 		return nil, err
// 	}

// 	newDomFacts := []FactStmt{}
// 	for _, fact := range stmt.DomFacts {
// 		newFact, err := fact.InstantiateFact(uniMap)
// 		if err != nil {
// 			return nil, err
// 		}
// 		newDomFacts = append(newDomFacts, newFact)
// 	}

// 	newImplicationFacts := []FactStmt{}
// 	for _, fact := range stmt.ImplicationFacts {
// 		newFact, err := fact.InstantiateFact(uniMap)
// 		if err != nil {
// 			return nil, err
// 		}
// 		newImplicationFacts = append(newImplicationFacts, newFact)
// 	}

// 	return NewImplicationStmt(newDefHeader, newDomFacts, newImplicationFacts, stmt.Line), nil
// }

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

// func InstantiateProveAlgoStmt(stmt ProveAlgoStmt, uniMap map[string]Obj) (ProveAlgoStmt, error) {
// 	switch stmt := stmt.(type) {
// 	case *ProveAlgoIfStmt:
// 		return stmt.InstantiateProveAlgo(uniMap)
// 	case *ProveAlgoReturnStmt:
// 		return stmt.InstantiateProveAlgo(uniMap)
// 	}
// 	return nil, fmt.Errorf("unknown prove algo statement type: %T", stmt)
// }

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

func (stmt *InferStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	newDomFacts := make([]Spec_OrFact, len(stmt.DomFacts))
	for i, fact := range stmt.DomFacts {
		newFact, err := fact.InstantiateFact(uniMap)
		if err != nil {
			return nil, err
		}
		if specOrFact, ok := newFact.(Spec_OrFact); ok {
			newDomFacts[i] = specOrFact
		} else {
			return nil, fmt.Errorf("instantiated fact is not Spec_OrFact")
		}
	}

	newThenFacts := make([]Spec_OrFact, len(stmt.ThenFacts))
	for i, fact := range stmt.ThenFacts {
		newFact, err := fact.InstantiateFact(uniMap)
		if err != nil {
			return nil, err
		}
		if specOrFact, ok := newFact.(Spec_OrFact); ok {
			newThenFacts[i] = specOrFact
		} else {
			return nil, fmt.Errorf("instantiated fact is not Spec_OrFact")
		}
	}

	return NewImplyStmt(newDomFacts, newThenFacts, stmt.Line), nil
}

func (stmt *InferTemplateStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	// Instantiate ParamSets
	newParamSets, err := stmt.ParamSets.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}

	// Instantiate DomFacts
	newDomFacts := make([]Spec_OrFact, len(stmt.DomFacts))
	for i, fact := range stmt.DomFacts {
		newFact, err := fact.InstantiateFact(uniMap)
		if err != nil {
			return nil, err
		}
		if specOrFact, ok := newFact.(Spec_OrFact); ok {
			newDomFacts[i] = specOrFact
		} else {
			return nil, fmt.Errorf("instantiated fact is not Spec_OrFact")
		}
	}

	// Instantiate ThenFacts
	newThenFacts := make([]Spec_OrFact, len(stmt.ThenFacts))
	for i, fact := range stmt.ThenFacts {
		newFact, err := fact.InstantiateFact(uniMap)
		if err != nil {
			return nil, err
		}
		if specOrFact, ok := newFact.(Spec_OrFact); ok {
			newThenFacts[i] = specOrFact
		} else {
			return nil, fmt.Errorf("instantiated fact is not Spec_OrFact")
		}
	}

	// Instantiate Proof
	newProof, err := stmt.Proof.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}

	// Instantiate IfFacts
	newIfFacts, err := stmt.IfFacts.InstantiateFact(uniMap)
	if err != nil {
		return nil, err
	}

	return &InferTemplateStmt{
		Params:    stmt.Params, // Params are strings, no need to instantiate
		ParamSets: newParamSets,
		DomFacts:  newDomFacts,
		ThenFacts: newThenFacts,
		Proof:     newProof,
		IfFacts:   newIfFacts,
		Line:      stmt.Line,
	}, nil
}

// func (stmt *DefProveAlgoStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
// 	newStmts, err := stmt.Stmts.Instantiate(uniMap)
// 	if err != nil {
// 		return nil, err
// 	}
// 	return NewDefProveAlgoStmt(stmt.ProveAlgoName, stmt.Params, newStmts, stmt.Line), nil
// }

// func (s ProveAlgoStmtSlice) Instantiate(uniMap map[string]Obj) (ProveAlgoStmtSlice, error) {
// 	newStmts := make([]ProveAlgoStmt, len(s))
// 	for i, stmt := range s {
// 		newStmt, err := InstantiateProveAlgoStmt(stmt, uniMap)
// 		if err != nil {
// 			return nil, err
// 		}
// 		newStmts[i] = newStmt
// 	}
// 	return newStmts, nil
// }

// func (stmt *ProveAlgoIfStmt) InstantiateProveAlgo(uniMap map[string]Obj) (ProveAlgoStmt, error) {
// 	newConditions, err := stmt.Conditions.InstantiateFact(uniMap)
// 	if err != nil {
// 		return nil, err
// 	}
// 	newThenStmts, err := stmt.ThenStmts.Instantiate(uniMap)
// 	if err != nil {
// 		return nil, err
// 	}
// 	return NewProveAlgoIfStmt(newConditions, newThenStmts, stmt.Line), nil
// }

// func (stmt *ByStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
// 	newProveAlgoParams, err := stmt.Params.Instantiate(uniMap)
// 	if err != nil {
// 		return nil, err
// 	}
// 	return NewByStmt(stmt.ProveAlgoName, newProveAlgoParams, stmt.Line), nil
// }

// func (stmt *ProveAlgoReturnStmt) InstantiateProveAlgo(uniMap map[string]Obj) (ProveAlgoStmt, error) {
// 	instFacts := FactOrByStmtSlice{}
// 	for _, factOrBy := range stmt.Facts {
// 		instFactOrBy, err := factOrBy.Instantiate(uniMap)
// 		if err != nil {
// 			return nil, err
// 		}
// 		// instFactOrBy is a Stmt, need to convert to FactOrByStmt
// 		switch item := instFactOrBy.(type) {
// 		case FactStmt:
// 			instFacts = append(instFacts, item)
// 		case *ByStmt:
// 			instFacts = append(instFacts, item)
// 		default:
// 			return nil, fmt.Errorf("unexpected type after instantiate: %T", instFactOrBy)
// 		}
// 	}
// 	return NewProveAlgoReturnStmt(instFacts, stmt.GetLine()), nil
// }

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
	newProofs := StmtSliceSlice{}
	for _, proof := range stmt.Proofs {
		newProof, err := proof.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		newProofs = append(newProofs, newProof)
	}
	newProveOr, err := stmt.ProveCases.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	return &HaveFnEqualCaseByCaseStmt{newDefHeader, newRetSet, newCaseByCaseFacts, newCaseByCaseEqualTo, newProofs, newProveOr, stmt.Line}, nil
}

func InstantiateSetBuilderObjWithoutChangingParam(obj *FnObj, uniMap map[string]Obj) (Obj, error) {
	setBuilderStruct, err := obj.ToSetBuilderStruct()
	if err != nil {
		return nil, err
	}

	if _, ok := uniMap[setBuilderStruct.Param]; ok {
		return nil, fmt.Errorf("parameter %s in set builder %s conflicts with a free parameter in the outer scope", setBuilderStruct.Param, obj.String())
	}

	// Instantiate parent set
	instParentSet, err := setBuilderStruct.ParentSet.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}

	// Instantiate facts
	instFacts := make(SpecFactPtrSlice, len(setBuilderStruct.Facts))
	for i, fact := range setBuilderStruct.Facts {
		instFact, err := fact.InstantiateFact(uniMap)
		if err != nil {
			return nil, err
		}
		specFact, ok := instFact.(*SpecFactStmt)
		if !ok {
			return nil, fmt.Errorf("expected SpecFactStmt, got %T", instFact)
		}
		instFacts[i] = specFact
	}

	return MakeSetBuilderObj(setBuilderStruct.Param, instParentSet, instFacts)
}

func (stmt *ProveExistStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	panic("TODO: Implement ProveExistStmt Instantiate")
}

func (stmt *EqualSetStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	left, err := stmt.Left.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	right, err := stmt.Right.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	proofs := make(StmtSlice, len(stmt.Proofs))
	for i, proof := range stmt.Proofs {
		instProof, err := proof.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		proofs[i] = instProof
	}
	return NewEqualSetStmt(left, right, proofs, stmt.Line), nil
}

func (stmt *WitnessNonemptyStmt) Instantiate(uniMap map[string]Obj) (Stmt, error) {
	obj, err := stmt.Obj.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	objSet, err := stmt.ObjSet.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}
	proofs := make(StmtSlice, len(stmt.Proofs))
	for i, proof := range stmt.Proofs {
		instProof, err := proof.Instantiate(uniMap)
		if err != nil {
			return nil, err
		}
		proofs[i] = instProof
	}
	return NewWitnessNonemptyStmt(obj, objSet, proofs, stmt.Line), nil
}
