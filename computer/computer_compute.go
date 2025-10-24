package litex_computer

import (
	ast "golitex/ast"
	cmp "golitex/cmp"
)

func (comp *computer) compute(toCompute ast.Fc) (ast.Fc, bool, error) {
	if cmp.IsNumLitFc(toCompute) {
		return toCompute, true, nil
	}

	return nil, false, nil
}
