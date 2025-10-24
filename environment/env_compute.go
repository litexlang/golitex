package litex_env

import (
	"fmt"
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

	if env.IsFnWithDefinedAlgo(fc) {
		computed, ok, err := env.Compute(fc)
		if err != nil {
			return nil, false, fmt.Errorf("error computing: %s", fc)
		}
		if ok {
			return computed, true, nil
		}
	}

	return nil, false, nil
}

// 算出的数值；是不是真的算出来了（因为可能没算出来，里面涉及到的符号没value什么的），出错
func (comp *computer) compute(toCompute ast.Fc) (ast.Fc, bool, error) {
	return nil, false, nil
}

func (env *Env) IsFnWithDefinedAlgo(fc ast.Fc) bool {
	return false
}
