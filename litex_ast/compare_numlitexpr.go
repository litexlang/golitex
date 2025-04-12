package litex_ast

import (
	glob "golitex/litex_global"
)

func IsFcBuiltinNumLitExpr(left Fc) (*glob.NumLitExpr, bool, error) {
	return MakeFcIntoNumLitExpr(left)
}

func MakeFcIntoNumLitExpr(fc Fc) (*glob.NumLitExpr, bool, error) {
	asStr, ok := IsNumLitFcAtom(fc)
	if ok {
		return &glob.NumLitExpr{Left: nil, OptOrNumber: asStr, Right: nil}, true, nil
	}

	asFcFn, ok := fc.(*FcFn)
	if !ok {
		// is atom
		return nil, false, nil
	}

	opt := asFcFn.FnHead.Value
	if !glob.IsKeySymbolRelaFn(opt) {
		return nil, false, nil
	}

	if len(asFcFn.ParamSegs) != 1 {
		return nil, false, nil
	}

	if len(asFcFn.ParamSegs[0].Params) != 2 {
		return nil, false, nil
	}

	left, ok, err := MakeFcIntoNumLitExpr(asFcFn.ParamSegs[0].Params[0])
	if err != nil {
		return nil, false, err
	}
	if !ok {
		return nil, false, nil
	}

	right, ok, err := MakeFcIntoNumLitExpr(asFcFn.ParamSegs[0].Params[1])
	if err != nil {
		return nil, false, err
	}
	if !ok {
		return nil, false, nil
	}

	return &glob.NumLitExpr{Left: left, OptOrNumber: opt, Right: right}, true, nil
}
