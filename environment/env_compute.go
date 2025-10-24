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

func (env *Env) Compute(fc ast.Fc) (ast.Fc, bool, error) {
	newComputer := newComputer(env)
	return newComputer.compute(fc)
}

func (env *Env) CanBeComputed(fc ast.Fc) (ast.Fc, bool, error) {
	ok := cmp.IsNumLitFc(fc)
	if ok {
		return fc, true, nil
	}

	return nil, false, nil
}

func (comp *computer) compute(toCompute ast.Fc) (ast.Fc, bool, error) {
	if cmp.IsNumLitFc(toCompute) {
		return toCompute, true, nil
	}

	return nil, false, nil
}
