package litexverifier

import "fmt"

func (e *Verifier) successMsg(stmtString, storedStmtString string) {
	message := fmt.Sprintf("[true]\n%v\n[verified by]\n%v", stmtString, storedStmtString)
	*e.Message = append(*e.Message, message) // 新消息插在后面
}

func (e *Verifier) unknownMsg(format string, args ...any) {
	if e.round1() {
		message := fmt.Sprintf(format, args...)
		*e.Message = append(*e.Message, message) // 新消息插在后面
	}
}
