package litexexecutor

import (
	structure "golitex/litex_structure"
)

func SearchInEnv[T any](env *Env, memTree *structure.RedBlackTree[T], key T) (*structure.Node[T], error) {
	// TODO: even when given key is different as tree key, we might still view them as the same. For example, when we know x = y, and we have $p(x), we now are verifying $p(y). As tree node, $p(x) is different from $p(y), but since x = y they are the same. So $p(y) should also be verified.

	return memTree.Search(key)
}
