package litexverifier

import (
	env "golitex/litex_env"
	parser "golitex/litex_parser"
)

func (verifier *Verifier) EqualFactSpecAtEnv(curEnv *env.Env, stmt *parser.RelaFactStmt) error {
	verified, err := verifier.TwoFcEqualSpecAtEnv(curEnv, stmt.Params[0], stmt.Params[1])
	if err != nil {
		return err
	}
	if verified {
		if verifier.round1() {
			verifier.successWithMsg(stmt.String(), stmt.Params[0].String())
		} else {
			verifier.successNoMsg()
		}
		return nil
	}
	return nil
}
