package litex_verifier

import ast "golitex/litex_ast"

// 就像 async func 和 func 在python中被分离开来，我也分离prop和prop_prop
func (ver *Verifier) IsPropProp(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	// TODO
	return false, nil
}

func (ver *Verifier) PropPropFact(stmt *ast.SpecFactStmt, state VerState) (bool, error) {
	// TODO	判断一下传入进来的stmt是不是prop prop，就像数学归纳法这种。prop prop的特点是，它是prop，参数列表里也有prop。如果是的话，那就用其他方式来验证
	return false, nil
}
