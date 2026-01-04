package litex_global

// // Copyright Jiachen Shen.
// //
// // Licensed under the Apache License, Version 2.0 (the "License");
// // you may not use this file except in compliance with the License.
// // You may obtain a copy of the License at
// //
// //     http://www.apache.org/licenses/LICENSE-2.0
// //
// // Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// // Litex email: <litexlang@outlook.com>
// // Litex website: https://litexlang.com
// // Litex github repository: https://github.com/litexlang/golitex
// // Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

// package litex_global

// import "strings"

// type VerRet interface {
// 	VerRet()
// 	IsTrue() bool
// 	IsUnknown() bool
// 	IsErr() bool
// 	AddMsg(msg string)
// 	String() string
// }

// type ExecTrue struct {
// 	Msg []string
// }

// type ExecUnknown struct {
// 	Msg []string
// }

// type ExecErr struct {
// 	Msg []string
// }

// func (e *ExecTrue) VerRet()          {}
// func (e *ExecTrue) IsTrue() bool      { return true }
// func (e *ExecTrue) IsUnknown() bool   { return false }
// func (e *ExecTrue) IsErr() bool       { return false }
// func (e *ExecTrue) AddMsg(msg string) { e.Msg = append(e.Msg, msg) }
// func (e *ExecTrue) String() string    { return strings.Join(e.Msg, "\n") }

// func (e *ExecUnknown) VerRet()          {}
// func (e *ExecUnknown) IsTrue() bool      { return false }
// func (e *ExecUnknown) IsUnknown() bool   { return true }
// func (e *ExecUnknown) IsErr() bool       { return false }
// func (e *ExecUnknown) AddMsg(msg string) { e.Msg = append(e.Msg, msg) }
// func (e *ExecUnknown) String() string    { return strings.Join(e.Msg, "\n") }

// func (e *ExecErr) VerRet()          {}
// func (e *ExecErr) IsTrue() bool      { return false }
// func (e *ExecErr) IsUnknown() bool   { return false }
// func (e *ExecErr) IsErr() bool       { return true }
// func (e *ExecErr) AddMsg(msg string) { e.Msg = append(e.Msg, msg) }
// func (e *ExecErr) String() string    { return strings.Join(e.Msg, "\n") }

// func NewVerTrue(s string) *ExecTrue {
// 	if s == "" {
// 		return &ExecTrue{Msg: []string{}}
// 	}
// 	return &ExecTrue{Msg: []string{s}}
// }

// func NewVerUnknown(s string) *ExecUnknown {
// 	if s == "" {
// 		return &ExecUnknown{Msg: []string{}}
// 	}
// 	return &ExecUnknown{Msg: []string{s}}
// }

// func NewVerErr(s string) *ExecErr {
// 	if s == "" {
// 		return &ExecErr{Msg: []string{}}
// 	}
// 	return &ExecErr{Msg: []string{s}}
// }
