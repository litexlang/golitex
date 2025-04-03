package litexglobal

import (
	"fmt"
	"strings"
)

type ErrLink struct {
	next error // Last in First out
	msg  string
}

func (e *ErrLink) Error() string {
	var builder strings.Builder

	builder.WriteString(e.msg)
	previous := e.next

	if previous != nil {
		builder.WriteByte('\n')
		builder.WriteString(previous.Error())
	}

	return builder.String()
}

func NewErrLink(next error, msg string, a ...any) *ErrLink {
	return &ErrLink{next, fmt.Sprintf(msg, a...)}
}

func InterpreterBug(msg string, a ...any) error {
	return fmt.Errorf(msg, a...)
}

func NewErrLinkAtFunc(next error, funcName string, msg string, a ...any) *ErrLink {
	if msg == "" {
		return NewErrLink(next, "error at %s", funcName)
	}
	return NewErrLink(NewErrLink(next, msg, a...), "error at %s", funcName)
}
