package litexpackage

import "fmt"

var ImportedPacks = map[string]Pack{}

type Pack struct {
}

func (p Pack) Get(s string) (*Pack, error) {
	pack, ok := ImportedPacks[s]
	if !ok {
		return nil, fmt.Errorf("package %s not found", s)
	}
	return &pack, nil
}
