package memory

type MemFact interface {
	MemFact()
}

func (m *SpecificFact) MemFact() {}
func (m *ForallFact) MemFact()   {}
