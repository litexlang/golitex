package msg

import "strings"

type Msg struct {
	Define        []string
	NewFact       []string
	VerifyProcess []string
	Infer         []string
	Error         []string
}

func (m *Msg) String() string {
	var builder strings.Builder
	if len(m.Error) > 0 {
		builder.WriteString("error:\n")
		builder.WriteString(strings.Join(m.Error, "\n"))
		return builder.String()
	}

	if len(m.Define) > 0 {
		builder.WriteString("by definition:\n")
		builder.WriteString(strings.Join(m.Define, "\n"))
	}

	if len(m.NewFact) > 0 {
		builder.WriteString("new fact:\n")
		builder.WriteString(strings.Join(m.NewFact, "\n"))
	}

	if len(m.VerifyProcess) > 0 {
		builder.WriteString("verify process:\n")
		builder.WriteString(strings.Join(m.VerifyProcess, "\n"))
	}

	if len(m.Infer) > 0 {
		builder.WriteString("infer:\n")
		builder.WriteString(strings.Join(m.Infer, "\n"))
	}

	return builder.String()
}

func (m *Msg) AddDefine(define string) *Msg {
	m.Define = append(m.Define, define)
	return m
}

func (m *Msg) AddNewFact(newFact string) *Msg {
	m.NewFact = append(m.NewFact, newFact)
	return m
}

func (m *Msg) AddVerifyProcess(verifyProcess string) *Msg {
	m.VerifyProcess = append(m.VerifyProcess, verifyProcess)
	return m
}

func (m *Msg) AddInfer(infer string) *Msg {
	m.Infer = append(m.Infer, infer)
	return m
}

func (m *Msg) AddError(error string) *Msg {
	m.Error = append(m.Error, error)
	return m
}
