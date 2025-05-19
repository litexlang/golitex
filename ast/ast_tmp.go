package litex_ast

import "fmt"

func (stmt *FcFn) isAdd() (bool, error) {
	asAtom, ok := stmt.FnHead.(*FcAtom)
	if !ok {
		return false, nil
	}
	if asAtom.Name == "+" {
		if len(stmt.ParamSegs) != 2 {
			return false, fmt.Errorf("add must have 2 params, but got %d", len(stmt.ParamSegs))
		}
		return true, nil
	}
	return false, nil
}

func (stmt *FcFn) isMul() (bool, error) {
	asAtom, ok := stmt.FnHead.(*FcAtom)
	if !ok {
		return false, nil
	}
	if asAtom.Name == "*" {
		if len(stmt.ParamSegs) != 2 {
			return false, fmt.Errorf("mul must have 2 params, but got %d", len(stmt.ParamSegs))
		}
		return true, nil
	}
	return false, nil
}

func (stmt *FcFn) isMinusAsInfix() (bool, error) {
	asAtom, ok := stmt.FnHead.(*FcAtom)
	if !ok {
		return false, nil
	}
	if asAtom.Name == "-" {
		if len(stmt.ParamSegs) != 2 {
			return false, fmt.Errorf("sub must have 2 params, but got %d", len(stmt.ParamSegs))
		}
		return true, nil
	}
	return false, nil
}

func (stmt *FcFn) isMinusAsPrefix() (bool, error) {
	asAtom, ok := stmt.FnHead.(*FcAtom)
	if !ok {
		return false, nil
	}
	if asAtom.Name == "-" {
		if len(stmt.ParamSegs) != 1 {
			return false, fmt.Errorf("minus must have 1 param, but got %d", len(stmt.ParamSegs))
		}
		return true, nil
	}
	return false, nil
}

func (stmt *FcFn) isDiv() (bool, error) {
	asAtom, ok := stmt.FnHead.(*FcAtom)
	if !ok {
		return false, nil
	}
	if asAtom.Name == "/" {
		if len(stmt.ParamSegs) != 2 {
			return false, fmt.Errorf("div must have 2 params, but got %d", len(stmt.ParamSegs))
		}
		return true, nil
	}
	return false, nil
}

func (stmt *FcAtom) orderNumberExpr() ([]Fc, error) {
	return []Fc{stmt}, nil
}

func (stmt *FcFn) orderNumberExpr() ([]Fc, error) {
	isAdd, err := stmt.isAdd()
	if err != nil {
		return nil, err
	}
	if isAdd {
		return stmt.orderAddFcFn()
	}

	isMul, err := stmt.isMul()
	if err != nil {
		return nil, err
	}
	if isMul {
		return stmt.orderMulFcFn()
	}

	isMinusAsInfix, err := stmt.isMinusAsInfix()
	if err != nil {
		return nil, err
	}
	if isMinusAsInfix {
		return stmt.orderMinusAsInfixFcFn()
	}

	isMinusAsPrefix, err := stmt.isMinusAsPrefix()
	if err != nil {
		return nil, err
	}
	if isMinusAsPrefix {
		return stmt.orderMinusAsPrefixFcFn()
	}

	isDiv, err := stmt.isDiv()
	if err != nil {
		return nil, err
	}
	if isDiv {
		return stmt.orderDivFcFn()
	}

	return nil, nil
}

func (stmt *FcFn) orderAddFcFn() ([]Fc, error) {
	orderedLeft, err := stmt.ParamSegs[0].orderNumberExpr()
	if err != nil {
		return nil, err
	}
	orderedRight, err := stmt.ParamSegs[1].orderNumberExpr()
	if err != nil {
		return nil, err
	}

	orderedFc := mergeOrderedAdditionNumberExpr(orderedLeft, orderedRight)

	return orderedFc, nil
}

func mergeOrderedAdditionNumberExpr(orderedLeft []Fc, orderedRight []Fc) []Fc {
	_ = orderedLeft
	_ = orderedRight
	return []Fc{}
}

func (stmt *FcFn) orderMulFcFn() ([]Fc, error) {
	return []Fc{}, nil
}

func (stmt *FcFn) orderMinusAsInfixFcFn() ([]Fc, error) {
	return []Fc{}, nil
}

func (stmt *FcFn) orderDivFcFn() ([]Fc, error) {
	return []Fc{}, nil
}

func (stmt *FcFn) orderMinusAsPrefixFcFn() ([]Fc, error) {
	return []Fc{}, nil
}

func IsNumberExpr_OrderIt(fc Fc) (Fc, bool, error) {
	return nil, false, nil
}
