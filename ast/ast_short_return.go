package litex_ast

import "strings"

type ShortRet interface {
	shortRet()
	IsTrue() bool
	IsUnknown() bool
	IsErr() bool
	IsNotTrue() bool
	String() string
	GetMsg() []string
}

type TrueShortRet struct {
	Msg []string
}

type UnknownShortRet struct {
	Msg []string
}

type ErrShortRet struct {
	Msg []string
}

func (r *TrueShortRet) shortRet()       {}
func (r *TrueShortRet) IsTrue() bool    { return true }
func (r *TrueShortRet) IsUnknown() bool { return false }
func (r *TrueShortRet) IsErr() bool     { return false }
func (r *TrueShortRet) IsNotTrue() bool { return false }

func (r *UnknownShortRet) shortRet()       {}
func (r *UnknownShortRet) IsTrue() bool    { return false }
func (r *UnknownShortRet) IsUnknown() bool { return true }
func (r *UnknownShortRet) IsErr() bool     { return false }
func (r *UnknownShortRet) IsNotTrue() bool { return true }
func (r *ErrShortRet) shortRet()           {}
func (r *ErrShortRet) IsTrue() bool        { return false }
func (r *ErrShortRet) IsUnknown() bool     { return false }
func (r *ErrShortRet) IsErr() bool         { return true }
func (r *ErrShortRet) IsNotTrue() bool     { return true }

func NewTrueShortRet() ShortRet {
	return &TrueShortRet{Msg: []string{}}
}

func NewUnknownShortRet() ShortRet {
	return &UnknownShortRet{Msg: []string{}}
}

func NewErrShortRet() ShortRet {
	return &ErrShortRet{Msg: []string{}}
}

func NewTrueShortRetWithMsg(msg string) ShortRet {
	return &TrueShortRet{Msg: []string{msg}}
}

func NewUnknownShortRetWithMsg(msg string) ShortRet {
	return &UnknownShortRet{Msg: []string{msg}}
}

func NewErrShortRetWithMsg(msg string) ShortRet {
	return &ErrShortRet{Msg: []string{msg}}
}

func (r *TrueShortRet) String() string {
	return strings.Join(r.Msg, "\n")
}

func (r *UnknownShortRet) String() string {
	return strings.Join(r.Msg, "\n")
}

func (r *ErrShortRet) String() string {
	return strings.Join(r.Msg, "\n")
}

func (r *TrueShortRet) GetMsg() []string {
	return r.Msg
}

func (r *UnknownShortRet) GetMsg() []string {
	return r.Msg
}

func (r *ErrShortRet) GetMsg() []string {
	return r.Msg
}
