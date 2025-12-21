package litex_env

import ast "golitex/ast"

func (envMemory *EnvMemory) GetEqualObjs(obj ast.Obj) (*[]ast.Obj, bool) {
	objAsStr := obj.String()
	facts, ok := envMemory.EqualMem[objAsStr]
	return facts, ok
}
