package litex_ast

type InferRet interface {
	inferRet()
	IsTrue() bool
	IsUnknown() bool
	IsErr() bool
	IsNotTrue() bool
}

type NotTrueInferRet interface {
	notTrueInferRet()
	GetExtraInfos() []string
}

func (r *UnknownInferRet) notTrueInferRet() {}
func (r *ErrInferRet) notTrueInferRet()     {}
func (r *UnknownInferRet) GetExtraInfos() []string {
	return r.ExtraInfo
}
func (r *ErrInferRet) GetExtraInfos() []string {
	return r.ExtraInfo
}

type TrueInferRet struct {
	Fact  FactStmt
	Infer []FactStmt
}

type UnknownInferRet struct {
	Fact      FactStmt
	ExtraInfo []string
}

type ErrInferRet struct {
	Fact      FactStmt
	ExtraInfo []string
}

func (r *TrueInferRet) inferRet()       {}
func (r *TrueInferRet) IsTrue() bool    { return true }
func (r *TrueInferRet) IsUnknown() bool { return false }
func (r *TrueInferRet) IsErr() bool     { return false }
func (r *TrueInferRet) IsNotTrue() bool { return false }

func (r *UnknownInferRet) inferRet()       {}
func (r *UnknownInferRet) IsTrue() bool    { return false }
func (r *UnknownInferRet) IsUnknown() bool { return true }
func (r *UnknownInferRet) IsErr() bool     { return false }
func (r *UnknownInferRet) IsNotTrue() bool { return true }

func (r *ErrInferRet) inferRet()       {}
func (r *ErrInferRet) IsTrue() bool    { return false }
func (r *ErrInferRet) IsUnknown() bool { return false }
func (r *ErrInferRet) IsErr() bool     { return true }
func (r *ErrInferRet) IsNotTrue() bool { return true }

func NewTrueEmptyInferRet(fact FactStmt) *TrueInferRet {
	return &TrueInferRet{Fact: fact, Infer: []FactStmt{}}
}

func NewTrueInferRet(fact FactStmt) *TrueInferRet {
	return &TrueInferRet{Fact: fact, Infer: []FactStmt{}}
}

func NewUnknownInferRet(fact FactStmt) *UnknownInferRet {
	return &UnknownInferRet{Fact: fact, ExtraInfo: []string{}}
}

func NewErrInferRet(fact FactStmt) *ErrInferRet {
	return &ErrInferRet{Fact: fact, ExtraInfo: []string{}}
}

func (r *TrueInferRet) AddInfer(infer FactStmt) *TrueInferRet {
	r.Infer = append(r.Infer, infer)
	return r
}

func (r *UnknownInferRet) AddExtraInfo(extraInfo string) *UnknownInferRet {
	r.ExtraInfo = append(r.ExtraInfo, extraInfo)
	return r
}

func (r *ErrInferRet) AddExtraInfo(extraInfo string) *ErrInferRet {
	r.ExtraInfo = append(r.ExtraInfo, extraInfo)
	return r
}

func (r *UnknownInferRet) AddExtraInfos(extraInfos []string) *UnknownInferRet {
	r.ExtraInfo = append(r.ExtraInfo, extraInfos...)
	return r
}

func (r *ErrInferRet) AddExtraInfos(extraInfos []string) *ErrInferRet {
	r.ExtraInfo = append(r.ExtraInfo, extraInfos...)
	return r
}

func (r *TrueInferRet) AddInfers(infers []FactStmt) *TrueInferRet {
	r.Infer = append(r.Infer, infers...)
	return r
}
