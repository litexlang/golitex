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

func (env *Env) Compute(fc ast.Fc) (ast.Fc, error) {
	newComputer := newComputer(env)
	return newComputer.compute(fc)
}

func (env *Env) CanBeComputed(fc ast.Fc) (ast.Fc, error) {
	ok := cmp.IsNumLitFc(fc)
	if ok {
		return fc, nil
	}

	if env.IsFnWithDefinedAlgo(fc) {
		computed, err := env.Compute(fc)
		if err != nil {
			return nil, fmt.Errorf("error computing: %s", fc)
		}
		if ok {
			return computed, nil
		}
	}

	return nil, nil
}

// 算出的数值；是不是真的算出来了（因为可能没算出来，里面涉及到的符号没value什么的），出错
func (comp *computer) compute(toCompute ast.Fc) (ast.Fc, error) {
	_ = toCompute
	return nil, nil
}

func (env *Env) IsFnWithDefinedAlgo(fc ast.Fc) bool {
	fcAsFcFn, ok := fc.(*ast.FcFn)
	if !ok {
		return false
	}
	fcAsFcFnHeadAsAtom, ok := fcAsFcFn.FnHead.(ast.FcAtom)
	if !ok {
		return false
	}
	return env.GetAlgoDef(fcAsFcFnHeadAsAtom.String()) != nil
}
