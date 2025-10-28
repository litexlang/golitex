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
	litenv "golitex/environment"
)

type AlgoExecutor struct {
	ExecEnv *litenv.Env
}

func (algoExecutor *AlgoExecutor) Env() *litenv.Env {
	return algoExecutor.ExecEnv
}

func NewAlgoExecutor(execEnv *litenv.Env) *AlgoExecutor {
	return &AlgoExecutor{ExecEnv: execEnv}
}

func (algoExec *AlgoExecutor) CanBeComputed(fc ast.Fc) (ast.Fc, error) {
	ok := cmp.IsNumLitFc(fc)
	if ok {
		return fc, nil
	}

	if algoExec.IsFnWithDefinedAlgo(fc) {
		computed, err := algoExec.Compute(fc)
		if err != nil {
			return nil, fmt.Errorf("error computing: %s", fc)
		}
		if ok {
			return computed, nil
		}
	}

	return nil, nil
}

func (algoExec *AlgoExecutor) Compute(toCompute ast.Fc) (ast.Fc, error) {
	_ = toCompute
	return nil, nil
}

func (algoExec *AlgoExecutor) IsFnWithDefinedAlgo(fc ast.Fc) bool {
	fcAsFcFn, ok := fc.(*ast.FcFn)
	if !ok {
		return false
	}
	fcAsFcFnHeadAsAtom, ok := fcAsFcFn.FnHead.(ast.FcAtom)
	if !ok {
		return false
	}
	return algoExec.Env().GetAlgoDef(fcAsFcFnHeadAsAtom.String()) != nil
}
