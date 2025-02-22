package litexmemory

type MemFact interface {
	MemFact()
}

func (m *InstantiatedMemoryFact) MemFact() {}
func (m *ForallMemFact) MemFact()          {}
