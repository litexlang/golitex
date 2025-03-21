package litexmemory

type MemoryErr struct {
	err error
}

func (e *MemoryErr) Error() string {
	return e.err.Error()
}

type ObjMemoryEntry struct {
}

type PropMemory struct {
}

type PropMemoryEntry struct {
}

type FnMemory struct {
}

type FnMemEntry struct {
}

type ObjMemory struct {
}
