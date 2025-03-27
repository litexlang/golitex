package litexmessages

import "strings"

func LineHead4Indents(line string, n uint32) string {
	if n == 0 {
		return line
	}

	spaces := strings.Repeat("    ", int(n))
	var builder strings.Builder

	// Pre-allocate buffer (estimate 20% extra space for indentation)
	builder.Grow(len(line) + len(spaces)*(strings.Count(line, "\n")+1))

	firstLine := true
	for _, part := range strings.Split(line, "\n") {
		if !firstLine {
			builder.WriteByte('\n')
		}
		builder.WriteString(spaces)
		builder.WriteString(part)
		firstLine = false
	}

	return builder.String()
}
