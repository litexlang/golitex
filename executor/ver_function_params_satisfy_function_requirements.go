package litex_executor

import (
	"fmt"
	ast "golitex/ast"
)

func (ver *Verifier) functionParamsSatisfyFunctionRequirements(fnObj *ast.FnObj, state *VerState) ast.VerRet {
	fnSet := ver.Env.GetFnInFnSet(fnObj.String())
	if fnSet == nil {
		return ast.NewErrVerRet(nil).AddExtraInfo(fmt.Sprintf("%s is not defined function", fnObj.String()))
	}

	return ast.NewTrueVerRet(nil, nil, "")
}
