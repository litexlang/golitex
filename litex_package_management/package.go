package litexpackage

var ImportedPackDict = PackDict{map[string]Pack{}}

type PackDict struct {
	entries map[string]Pack
}

type Pack struct {
}

func (p PackDict) Get(s string) (*Pack, bool) {
	pack, ok := p.entries[s]
	if !ok {
		return nil, false
	}
	return &pack, true
}
