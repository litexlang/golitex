package litex_ast

func (stmt *FcFn) isAdd() bool {
	asAtom, ok := stmt.FnHead.(*FcAtom)
	if !ok {
		return false
	}
	return asAtom.Name == "+"
}

func (stmt *FcFn) isMul() bool {
	asAtom, ok := stmt.FnHead.(*FcAtom)
	if !ok {
		return false
	}
	return asAtom.Name == "*"
}

func (stmt *FcFn) isSub() bool {
	asAtom, ok := stmt.FnHead.(*FcAtom)
	if !ok {
		return false
	}
	return asAtom.Name == "-"
}

func (stmt *FcFn) isDiv() bool {
	asAtom, ok := stmt.FnHead.(*FcAtom)
	if !ok {
		return false
	}
	return asAtom.Name == "/"
}

func (stmt *FcAtom) orderAddition() []Fc {
	return []Fc{stmt}
}

func (stmt *FcFn) orderAddition() []Fc {
	asAtom, ok := stmt.FnHead.(*FcAtom)
	if !ok {
		return nil
	}
	orderedLeft := stmt.ParamSegs[0].orderAddition()
	orderedRight := stmt.ParamSegs[1].orderAddition()

	orderedLeft = append(orderedLeft, asAtom)
	orderedRight = append(orderedRight, asAtom)

	// TODO
	return []Fc{}
}
