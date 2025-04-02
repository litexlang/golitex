package litexverifier

import (
	parser "golitex/litex_parser"
)

func (ver *Verifier) IsPropProp(stmt *parser.SpecFactStmt) (bool, error) {
	// TODO
	return false, nil
}

func (ver *Verifier) PropPropFact(stmt *parser.SpecFactStmt, state VerState) (bool, error) {
	// TODO	判断一下传入进来的stmt是不是prop prop，就像数学归纳法这种。prop prop的特点是，它是prop，参数列表里也有prop。如果是的话，那就用其他方式来验证
	return false, nil
}
