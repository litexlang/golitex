package memory

func (mem *VarMemory) Get(s string) (*VarMemoryEntry, bool) {
	ret, ok := mem.entries[s]
	if !ok {
		return nil, false
	}
	return &ret, true
}
