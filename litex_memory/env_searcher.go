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
	FcFnRetValueMembersEql []*FcFnRetValueEql // 如果fc的某位member是fcStr，这里放nil
}

// 这里的逻辑不太完整，因为可能两个prop等价，但是我这里不考虑。不允许prop相等, 否则就出现 f(a,b) = g 这样的情况。那样一来，就会在search $f(a,b)(c)  的时候还要搜索 $g(c) ，这有点太麻烦了，特别是未来做forall的时候更是麻烦到极点。或者说如果他们相等，只有在 prop 作为 param 的时候我才考虑他们相等，而不是作为 被call 的东西时。你要让 2个propName 作为 prop 被视作一样的东西，那用forall
func (env *Env) searchEquivalentFcFnRetFuncFactParamsInAllEnvs(key *parser.FcFnRetValue) (TypeParamsAndVarParamsEqlPairs, error) {
	panic("")
}

func (env *Env) searchEquivalentFcChainFuncFactParamsInAllEnvs(key *parser.FcChain) (TypeParamsAndVarParamsEqlPairs, error) {
	panic("")
}
