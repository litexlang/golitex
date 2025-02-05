package memory

type MemFact interface {
	MemFact()
}

func (m *MemSpecificFact) MemFact() {}
func (m *MemForallFact) MemFact()   {}
