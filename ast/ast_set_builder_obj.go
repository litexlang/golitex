package litex_ast

type SetBuilderObj struct {
}

func (obj *SetBuilderObj) obj()
func (obj *SetBuilderObj) String() string
func (obj *SetBuilderObj) Instantiate(map[string]Obj) (Obj, error)
func (obj *SetBuilderObj) ToLatexString() string
