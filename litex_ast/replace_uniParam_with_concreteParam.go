package litex_ast

func (fc *FcAtom) Instantiate(uniParamConParamMap map[string]Fc) Fc {
	if fc.PkgName == "" {
		instance, ok := uniParamConParamMap[fc.Value]
		if ok {
			return instance
		}
	}
	return fc
}

func (fc *FcFn) Instantiate(uniParamConParamMap map[string]Fc) Fc {
	newFc := FcFn{FcAtom{}, []*FcFnSeg{}}

	newHead := fc.FnHead.Instantiate(uniParamConParamMap)

	if newHeadAsAtom, ok := newHead.(*FcAtom); ok {
		newFc.FnHead = *newHeadAsAtom
	} else {
		newHeadAsFcFn, _ := newHead.(*FcFn)
		newFc.FnHead = newHeadAsFcFn.FnHead
		newFc.ParamSegs = append(newFc.ParamSegs, newHeadAsFcFn.ParamSegs...)
	}

	for _, seg := range fc.ParamSegs {
		newSeg := FcFnSeg{[]Fc{}}
		for _, param := range seg.Params {
			newParam := param.Instantiate(uniParamConParamMap)
			newSeg.Params = append(newSeg.Params, newParam)
		}
		newFc.ParamSegs = append(newFc.ParamSegs, &newSeg)
	}

	return &newFc
}

func (stmt *SpecFactStmt) Instantiate(uniParamConParamMap map[string]Fc) FactStmt {
	newParams := []Fc{}
	for _, param := range stmt.Params {
		newParam := param.Instantiate(uniParamConParamMap)
		newParams = append(newParams, newParam)
	}

	// TODO 把PropName 也换了
	return NewSpecFactStmt(stmt.IsTrue, stmt.PropName, newParams)
}

func (stmt *ConUniFactStmt) Instantiate(uniParamConParamMap map[string]Fc) FactStmt {
	newParamTypes := []Fc{}
	for _, param := range stmt.ParamTypes {
		newParam := param.Instantiate(uniParamConParamMap)
		newParamTypes = append(newParamTypes, newParam)
	}

	newDomFacts := []FactStmt{}
	for _, fact := range stmt.DomFacts {
		newFact := fact.Instantiate(uniParamConParamMap)
		newDomFacts = append(newDomFacts, newFact)
	}

	newThenFacts := []*SpecFactStmt{}
	for _, fact := range stmt.ThenFacts {
		newFact := fact.Instantiate(uniParamConParamMap)
		newThenFacts = append(newThenFacts, newFact.(*SpecFactStmt))
	}

	return NewUniFactStmt(stmt.Params, newParamTypes, newDomFacts, newThenFacts)
}

func (stmt *CondFactStmt) Instantiate(uniParamConParamMap map[string]Fc) FactStmt {
	newCondFacts := []FactStmt{}
	for _, fact := range stmt.CondFacts {
		newFact := fact.Instantiate(uniParamConParamMap)
		newCondFacts = append(newCondFacts, newFact)
	}

	newThenFacts := []*SpecFactStmt{}
	for _, fact := range stmt.ThenFacts {
		newFact := fact.Instantiate(uniParamConParamMap)
		newThenFacts = append(newThenFacts, newFact.(*SpecFactStmt))
	}
	return NewCondFactStmt(newCondFacts, newThenFacts)
}

func (stmt *GenUniStmt) Instantiate(uniParamConParamMap map[string]Fc) FactStmt {
	panic("TODO")
}
