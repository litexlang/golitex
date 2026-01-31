package litex_ast

type NewFactRet interface {
	inferRet()
	IsTrue() bool
	IsUnknown() bool
	IsErr() bool
	IsNotTrue() bool
}

type TrueNewFactRet struct {
	Fact FactStmt
}

type UnknownNewFactRet struct {
	Fact      FactStmt
	ExtraInfo []string
}

type ErrNewFactRet struct {
	Fact      FactStmt
	ExtraInfo []string
}

func (r *TrueNewFactRet) newFactRet()     {}
func (r *TrueNewFactRet) IsTrue() bool    { return true }
func (r *TrueNewFactRet) IsUnknown() bool { return false }
func (r *TrueNewFactRet) IsErr() bool     { return false }
func (r *TrueNewFactRet) IsNotTrue() bool { return false }

func (r *UnknownNewFactRet) newFactRet()     {}
func (r *UnknownNewFactRet) IsTrue() bool    { return false }
func (r *UnknownNewFactRet) IsUnknown() bool { return true }
func (r *UnknownNewFactRet) IsErr() bool     { return false }
func (r *UnknownNewFactRet) IsNotTrue() bool { return true }

func (r *ErrNewFactRet) newFactRet()     {}
func (r *ErrNewFactRet) IsTrue() bool    { return false }
func (r *ErrNewFactRet) IsUnknown() bool { return false }
func (r *ErrNewFactRet) IsErr() bool     { return true }
func (r *ErrNewFactRet) IsNotTrue() bool { return true }

func NewTrueEmptyNewFactRet(fact FactStmt) *TrueNewFactRet {
	return &TrueNewFactRet{Fact: fact}
}

func NewTrueNewFactRet(fact FactStmt) *TrueNewFactRet {
	return &TrueNewFactRet{Fact: fact}
}

func NewUnknownNewFactRet(fact FactStmt) *UnknownNewFactRet {
	return &UnknownNewFactRet{Fact: fact, ExtraInfo: []string{}}
}

func NewErrNewFactRet(fact FactStmt) *ErrNewFactRet {
	return &ErrNewFactRet{Fact: fact, ExtraInfo: []string{}}
}
