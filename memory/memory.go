package memory

import "fmt"

func (memory *ForallFactMemory) setEntry(name string) error {
	_, ok := memory.entries[name]
	if ok {
		return fmt.Errorf("entry with name '%s' already exists", name)
	}

	memory.entries[name] = []ForallFactMemEntry{}

	return nil
}
