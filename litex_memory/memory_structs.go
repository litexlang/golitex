package litexmemory

type MemoryErr struct {
	err error
}

func (e *MemoryErr) Error() string {
	return e.err.Error()
}

type VarMemoryEntry struct {
}

type PropMemory struct {
}

type PropMemoryEntry struct {
}

type FnMemory struct {
}

type FnMemEntry struct {
}

type VarMemory struct {
}
