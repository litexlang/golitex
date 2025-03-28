package litexverifier

import (
	env "golitex/litex_env"
	parser "golitex/litex_parser"
)

func (ver *Verifier) EqualFactSpecAtEnv(curEnv *env.Env, stmt *parser.RelaFactStmt) (bool, error) {
	verified, err := ver.FcEqualSpecInSpecMemAtEnv(curEnv, stmt.Params[0], stmt.Params[1])
	if err != nil {
		return false, err
	}
	if verified {
		if ver.round1() {
			ver.successWithMsg(stmt.String(), stmt.Params[0].String())
		} else {
			ver.successNoMsg()
		}
		return true, nil
	}
	return false, nil
}
