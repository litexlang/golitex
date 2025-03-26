package litexmemory

type MemoryErr struct {
	err error
}

func (e *MemoryErr) Error() string {
	return e.err.Error()
}

type ObjMemoryEntry struct {
}

type PropMem struct {
}

type PropMemoryEntry struct {
}

type FnMem struct {
}

type FnMemEntry struct {
}

type ObjMem struct {
}
