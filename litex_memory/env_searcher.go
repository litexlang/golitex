package litexmemory

import (
	parser "golitex/litex_parser"
)

func (mem *RedBlackTree[T]) SearchInEnv(env *Env, key T) (*Node[T], error) {
	// TODO: even when given key is different as tree key, we might still view them as the same. For example, when we know x = y, and we have $p(x), we now are verifying $p(y). As tree node, $p(x) is different from $p(y), but since x = y they are the same. So $p(y) should also be verified.

	return mem.Search(key)
}

func (mem *RedBlackTree[T]) SearchInEnvLayerByLayer(env *Env, key T) (*Node[T], error) {
	curNode := mem.Root
	var err error = nil
	searched := false
	for curNode != nil {
		curNode, err, searched = mem.SearchOneLayer(curNode, key)
		if err != nil {
			return nil, err
		}

		if searched {
			return curNode, nil
		}
	}

	return nil, nil
}

type FcFnRetValueEql struct {
	FnName                 parser.FcStr
	TypeParamsVarParamsEql []TypeParamsAndVarParamsEqlPairs
}

type TypeParamsAndVarParamsEqlPairs struct {
	typeParamEql [][]parser.TypeVarStr
	varParamEql  [][]parser.Fc
}

type FcChainEql struct {
	// REMARK: 如果某一位的member是 FcStr 类型的，那跳过这一位，只保存FcFnRetValueEql
	FcFnRetValueMembersEql []FcFnRetValueEql
}

func (env *Env) searchEquivalentFcFnRetFuncFactParamsInAllEnvs(key *parser.FcFnRetValue) (TypeParamsAndVarParamsEqlPairs, error) {
	panic("")
}

func (env *Env) searchEquivalentFcChainFuncFactParamsInAllEnvs(key *parser.FcChain) (TypeParamsAndVarParamsEqlPairs, error) {
	panic("")
}
