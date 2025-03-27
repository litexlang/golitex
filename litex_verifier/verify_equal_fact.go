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
		verifier.success(stmt.String(), stmt.Params[0].String())
		return nil
	}
	return nil
}
