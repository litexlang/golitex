package litex_env

import (
	ast "golitex/ast"
	cmp "golitex/cmp"
)

type computer struct {
	env *Env
}

func newComputer(env *Env) *computer {
	return &computer{env: env}
}

func Compute(env *Env, fc ast.Fc) (ast.Fc, bool, error) {
	newComputer := newComputer(env)
	return newComputer.compute(fc)
}

func CanBeComputed(fc ast.Fc) bool {
	ok := cmp.IsNumLitFc(fc)
	if ok {
		return true
	}

	ok, _ = ast.IsFcFnWithCompHeadAndReturnFcToCompute(fc)
	return ok
}

func (comp *computer) compute(toCompute ast.Fc) (ast.Fc, bool, error) {
	if cmp.IsNumLitFc(toCompute) {
		return toCompute, true, nil
	}

	return nil, false, nil
}
