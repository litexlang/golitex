package litexparser

import (
	"fmt"
	glob "golitex/litex_global"
)

type NumberFc struct {
	left        *NumberFc
	optOrNumber string
	right       *NumberFc
}

func IsNumberFcWithBuiltinInfixOpt(fc Fc) (*NumberFc, bool, error) {
	asStr, ok := IsNumberAtom(fc)
	if ok {
		return &NumberFc{nil, asStr, nil}, true, nil
	}

	asFcFn, ok := fc.(*FcFnPipe)
	if !ok {
		return nil, false, fmt.Errorf("")
	}

	opt := asFcFn.FnHead.Value
	if !glob.IsBuiltinRelaFn(opt) {
		return nil, false, nil
	}

	if len(asFcFn.CallPipe) != 1 {
		return nil, false, nil
	}

	if len(asFcFn.CallPipe[0].Params) != 2 {
		return nil, false, nil
	}

	left, ok, err := IsNumberFcWithBuiltinInfixOpt(asFcFn.CallPipe[0].Params[0])
	if err != nil {
		return nil, false, err
	}
	if !ok {
		return nil, false, nil
	}

	right, ok, err := IsNumberFcWithBuiltinInfixOpt(asFcFn.CallPipe[0].Params[0])
	if err != nil {
		return nil, false, err
	}
	if !ok {
		return nil, false, nil
	}

	return &NumberFc{left, opt, right}, true, nil
}
