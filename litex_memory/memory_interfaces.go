package litexmemory

type MemFact interface {
	MemFact()
}

func (m *SpecMemoryFact) MemFact() {}
func (m *UniMemFact) MemFact()     {}
