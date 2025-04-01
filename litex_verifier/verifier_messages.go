package litexverifier

import (
	"fmt"
	"slices"
	"strings"
)

func (ver *Verifier) successMsgEnd(stmtStr, stmtVerifiedBy string) {
	if stmtStr != "" {
		*ver.Messages = append(*ver.Messages, stmtStr)
	}
	if stmtVerifiedBy != "" {
		message := fmt.Sprintf("is true. proved by\n%v", stmtVerifiedBy)
		*ver.Messages = append(*ver.Messages, message)
	}
}

func (ver *Verifier) unknownMsgEnd(format string, args ...any) {
	message := fmt.Sprintf(format, args...)
	*ver.Messages = append(*ver.Messages, message)
}

func (ver *Verifier) newMsgEnd(format string, args ...any) {
	message := fmt.Sprintf(format, args...)
	*ver.Messages = append(*ver.Messages, message)
}

func (ver *Verifier) GetMsgAsStr() string {
	slices.Reverse(*ver.Messages)
	return strings.Join(*ver.Messages, "\n")
}
