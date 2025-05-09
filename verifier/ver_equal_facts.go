// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Contact the development team: <litexlang@outlook.com>
// Visit litexlang.org and https://github.com/litexlang/golitex for more info.

package litex_verifier

import (
	ast "golitex/ast"
	cmp "golitex/cmp"
)

func (ver *Verifier) equalByEqualMem(left ast.Fc, right ast.Fc) (bool, error) {
	for curEnv := ver.env; curEnv != nil; curEnv = curEnv.Parent {
		equalToLeftFcs, gotLeftEqualFcs := curEnv.GetEqualFcs(left)
		equalTorightFcs, gotRightEqualFcs := curEnv.GetEqualFcs(right)

		if gotLeftEqualFcs && gotRightEqualFcs {
			if equalToLeftFcs == equalTorightFcs {
				return true, nil
			}
		}

		if gotLeftEqualFcs {
			for _, equalToLeftFc := range *equalToLeftFcs {
				ok, err := cmp.CmpFcRule(equalToLeftFc, right)
				if err != nil {
					return false, err
				}
				if ok {
					return true, nil
				}
			}
		}

		if gotRightEqualFcs {
			for _, equalToRightFc := range *equalTorightFcs {
				ok, err := cmp.CmpFcRule(equalToRightFc, left)
				if err != nil {
					return false, err
				}
				if ok {
					return true, nil
				}
			}
		}
	}

	return false, nil
}
