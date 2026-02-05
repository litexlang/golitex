package litex_ast

type SetBuilderObj struct {
}

func (obj *SetBuilderObj) obj()                                    {}
func (obj *SetBuilderObj) String() string                          { return "" }
func (obj *SetBuilderObj) Instantiate(map[string]Obj) (Obj, error) { return nil, nil }
func (obj *SetBuilderObj) ToLatexString() string                   { return "" }
