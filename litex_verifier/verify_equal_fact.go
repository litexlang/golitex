package litexverifier

import (
	env "golitex/litex_env"
	parser "golitex/litex_parser"
)

func (verifier *Verifier) verifyEqualFactSpecificallyAtEnv(curEnv *env.Env, stmt *parser.RelationFactStmt) error {
	verified, err := verifier.verifyTwoFcEqualSpecificallyAtEnv(curEnv, stmt.Params[0], stmt.Params[1])
	if err != nil {
		return err
	}
	if verified {
		verifier.success("%v is true, verified by %v", stmt, stmt.Params[0])
		return nil
	}
	return nil
}
