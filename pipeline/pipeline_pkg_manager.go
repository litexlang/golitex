package litex_pipeline

import (
	"fmt"
	env "golitex/environment"
	glob "golitex/glob"
	"os"
)

type PackagesManager struct {
	pkgEnv map[string]*env.Env
}

func NewPackageManager() *PackagesManager {
	return &PackagesManager{
		pkgEnv: make(map[string]*env.Env),
	}
}

func (pkgMgr *PackagesManager) NewPkg(builtinEnv *env.Env, path string) (string, glob.SysSignal, error) {
	if _, ok := pkgMgr.pkgEnv[path]; ok {
		return fmt.Sprintf("%s is already imported", path), glob.SysSignalTrue, nil
	}

	// run pkg
	pkgContent, err := os.ReadFile(path)
	if err != nil {
		return fmt.Sprintf("failed to read file %s: %s", path, err.Error()), glob.SysSignalSystemError, err
	}

	msg, signal, newEnv, err := RunSourceCode(builtinEnv, string(pkgContent))
	if err != nil || signal != glob.SysSignalTrue {
		return msg, signal, err
	}

	pkgMgr.pkgEnv[path] = newEnv

	return msg, signal, err
}
