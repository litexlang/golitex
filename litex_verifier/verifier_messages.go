package litexverifier

import (
	"fmt"
)

func (ver *Verifier) successMsgEnd(stmtStr, stmtVerifiedBy string) {
	if stmtStr != "" {
		ver.env.Msgs = append(ver.env.Msgs, stmtStr)
	}
	if stmtVerifiedBy != "" {
		message := fmt.Sprintf("is true. proved by\n%v", stmtVerifiedBy)
		ver.env.Msgs = append(ver.env.Msgs, message)
	} else {
		message := fmt.Sprintf("is true.")
		ver.env.Msgs = append(ver.env.Msgs, message)
	}
}

func (ver *Verifier) unknownMsgEnd(format string, args ...any) {
	message := fmt.Sprintf(format, args...)
	ver.env.Msgs = append(ver.env.Msgs, message)
}

func (ver *Verifier) appendMsg(format string, args ...any) {
	message := fmt.Sprintf(format, args...)
	ver.env.Msgs = append(ver.env.Msgs, message)
}
