package litexmemory

// TODO: get, newItem

func (m *AliasMemory) newItem(previousName string, newName string) {
	if entry, ok := m.entries[previousName]; ok {
		*entry.Values = append(*entry.Values, newName)
		m.entries[newName] = entry
	} else {
		m.entries[newName] = AliasMemoryEntry{Values: &[]string{newName}}
	}

}
