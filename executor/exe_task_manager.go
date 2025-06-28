package litex_executor

import (
	env "golitex/environment"
	glob "golitex/glob"
)

var runtimeEnvSlice []*env.Env = []*env.Env{}

func execImportStmtInit(newPkg string, path string, env *env.Env) error {
	runtimeEnvSlice = append(runtimeEnvSlice, env)
	err := glob.ImportStmtInit(newPkg, path)
	return err
}

func execImportStmtEnd(env *env.Env) error {
	runtimeEnvSlice = runtimeEnvSlice[:len(runtimeEnvSlice)-1]
	glob.ImportStmtEnd()
	return nil
}
