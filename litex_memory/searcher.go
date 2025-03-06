package litexmemory

func (mem *RedBlackTree[T]) SearchUsingEnv(env *Env, key T) (*Node[T], error) {
	return mem.Search(key)
}
