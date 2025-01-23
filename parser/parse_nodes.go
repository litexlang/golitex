package parser

import "fmt"

func skip(tokens *[]string, start *int, expected string) error {
	// if current token is expected, start ++, else throw an error
	if (*tokens)[*start] == expected {
		*start++
	} else {
		return fmt.Errorf("expected '%s', but got '%s'", expected, (*tokens)[*start])
	}

	return nil
}

func parseTypeVarPairBracket(tokens *[]string, start int) (*[]VarTypePair, int, error) {
	var vals []VarTypePair

	for i, token := range (*tokens)[start+1:] {
		if token == "]" {
			return &vals, i + 1, nil
		}

		v := (*tokens)[i]
		i += 1
		t := (*tokens)[i]
		typeVarPair := VarTypePair{v, t}

		vals = append(vals, typeVarPair)

		i += 1
		err := skip(tokens, &i, KeyChars[","])
		if err != nil {
			return nil, 0, err
		}
	}

	return nil, 0, fmt.Errorf("expected ']', but got '%s'", (*tokens)[start])
}
