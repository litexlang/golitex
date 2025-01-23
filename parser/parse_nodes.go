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

func parseTypeVarPairBracket(tokens *[]string, start *int) (*[]VarTypePair, error) {
	var vals []VarTypePair

	err := skip(tokens, start, KeywordSymbols["["])
	if err != nil {
		return nil, err
	}

	for *start < len(*tokens) {

		v := (*tokens)[*start]
		*start++
		t := (*tokens)[*start]
		typeVarPair := VarTypePair{v, t}

		vals = append(vals, typeVarPair)

		*start++

		if (*tokens)[*start] == KeywordSymbols["]"] {
			*start++
			return &vals, nil
		}

		err := skip(tokens, start, KeywordSymbols[","])
		if err != nil {
			return nil, err
		}
	}

	return nil, fmt.Errorf("expected ']', but got '%s'", (*tokens)[*start])
}

func parseTypeVarPairBrace(tokens *[]string, start *int) (*[]VarTypePair, error) {
	var vals []VarTypePair

	err := skip(tokens, start, KeywordSymbols["("])
	if err != nil {
		return nil, err
	}

	for *start < len(*tokens) {

		v := (*tokens)[*start]
		*start++
		t := (*tokens)[*start]
		typeVarPair := VarTypePair{v, t}

		vals = append(vals, typeVarPair)

		*start++

		if (*tokens)[*start] == KeywordSymbols[")"] {
			*start++
			return &vals, nil
		}

		err := skip(tokens, start, KeywordSymbols[","])
		if err != nil {
			return nil, err
		}
	}

	return nil, fmt.Errorf("expected ')', but got '%s'", (*tokens)[*start])
}
