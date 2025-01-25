package parser

import "fmt"

func skip(tokens *[]string, start *int, expected ...string) error {
	// 边界检查：start不能越界
	if *start >= len(*tokens) {
		return fmt.Errorf("unexpected end of input")
	}

	// 情况1：没有传入expected参数时直接递增
	if len(expected) == 0 {
		*start++
		return nil
	}

	// 情况2：有expected参数时执行原有逻辑
	if (*tokens)[*start] == expected[0] {
		*start++
	} else {
		return fmt.Errorf("expected '%s', but got '%s'", expected[0], (*tokens)[*start])
	}

	return nil
}

func parseTypeVarPairBracket(tokens *[]string, start *int) (*varTypePairBracketBrace, error) {
	pairs := []VarTypePair{}
	facts := []FactStmt{}

	err := skip(tokens, start, KeySyms["["])
	if err != nil {
		return nil, err
	}

	for *start < len(*tokens) {
		v := (*tokens)[*start]
		*start++
		t := (*tokens)[*start]
		typeVarPair := VarTypePair{v, t}

		pairs = append(pairs, typeVarPair)

		*start++

		if (*tokens)[*start] == KeySyms["]"] {
			*start++
			break
		}

		if (*tokens)[*start] == KeySyms["::"] {
			break
		}

		err := skip(tokens, start, KeySyms[","])
		if err != nil {
			return nil, err
		}
	}

	if *start < len(*tokens) && (*tokens)[*start] == KeySyms["::"] {
		*start++
		for *start < len(*tokens) && (*tokens)[*start] != KeySyms["]"] {
			fact, err := parseFactExprStmt(tokens, start)
			if err != nil {
				return nil, err
			}

			facts = append(facts, fact)

			if (*tokens)[*start] == KeySyms["]"] {
				*start++
				break
			}

			err = skip(tokens, start, KeySyms[","])
			if err != nil {
				return nil, err
			}
		}
	}

	return &varTypePairBracketBrace{pairs, facts}, nil
}

func parseTypeVarPairBrace(tokens *[]string, start *int) (*varTypePairBracketBrace, error) {
	pairs := []VarTypePair{}
	facts := []FactStmt{}

	err := skip(tokens, start, KeySyms["("])
	if err != nil {
		return nil, err
	}

	for *start < len(*tokens) {

		v := (*tokens)[*start]
		*start++
		t := (*tokens)[*start]
		typeVarPair := VarTypePair{v, t}

		pairs = append(pairs, typeVarPair)

		*start++

		if (*tokens)[*start] == KeySyms[")"] {
			*start++
			break
		}

		if (*tokens)[*start] == KeySyms["::"] {
			break
		}

		err := skip(tokens, start, KeySyms[","])
		if err != nil {
			return nil, err
		}
	}

	if *start < len(*tokens) && (*tokens)[*start] == KeySyms["::"] {
		*start++
		for *start < len(*tokens) && (*tokens)[*start] != KeySyms[")"] {
			fact, err := parseFactExprStmt(tokens, start)
			if err != nil {
				return nil, err
			}

			facts = append(facts, fact)

			if (*tokens)[*start] == KeySyms[")"] {
				*start++
				break
			}

			err = skip(tokens, start, KeySyms[","])
			if err != nil {
				return nil, err
			}
		}
	}

	return &varTypePairBracketBrace{pairs, facts}, nil
}

func parseFactExprStmt(tokens *[]string, start *int) (*FactStmt, error) {
	// TODO
	return nil, nil
}

func parseVar(tokens *[]string, start *int) (Var, error) {
	// TODO 现在只能 parse 单纯的 var
	v := (*tokens)[*start]
	*start += 1
	return &v, nil
}

func parseBracedVars(tokens *[]string, start *int) ([]Var, error) {
	skip(tokens, start, KeySyms["("])

	vars := []Var{}
	// parseVar from index start, skip , between, end when )
	for *start < len(*tokens) {
		v, err := parseVar(tokens, start)
		if err != nil {
			return nil, err
		}
		vars = append(vars, v)

		if (*tokens)[*start] == KeySyms[")"] {
			*start++
			return vars, nil
		}

		if (*tokens)[*start] == KeySyms[","] {
			*start++
		}
	}

	return nil, fmt.Errorf("expected ')', but got '%s'", (*tokens)[*start])
}

func ParseSingletonVarBracket(tokens *[]string, start *int) (*[]string, error) {
	skip(tokens, start, KeySyms["["])

	typeVars := []string{}
	// parseVar from index start, skip , between, end when )
	for *start < len(*tokens) {
		v := (*tokens)[*start]
		*start += 1
		typeVars = append(typeVars, v)

		if (*tokens)[*start] == KeySyms["]"] {
			*start++
			return &typeVars, nil
		}

		if (*tokens)[*start] == KeySyms[","] {
			*start++
		}
	}

	return nil, fmt.Errorf("expected ']', but got '%s'", (*tokens)[*start])
}

func parseFc(tokens *[]string, start *int) (Fc, error) {
	firstSymbolPtr, err := parseFcStr(tokens, start)
	if err != nil {
		return nil, err
	}

	if (*start < len(*tokens) && !((*tokens)[*start] == KeySyms["["] || (*tokens)[*start] == KeySyms["("])) || *start >= len(*tokens) {
		return firstSymbolPtr, nil
	}

	var previousFc Fc = firstSymbolPtr

	for *start < len(*tokens) && ((*tokens)[*start] == KeySyms["["] || (*tokens)[*start] == KeySyms["("]) {
		curFcc := FcFnRetVal{previousFc, []FcStr{}, []Fc{}}

		typeParams := []FcStr{}
		if t, err := isCurToken(tokens, start, KeySyms["["]); t {
			typeParamsPtr, err := parseBracketedFcString(tokens, start)
			typeParams = *typeParamsPtr
			if err != nil {
				return nil, err
			}
		} else if err != nil {
			return nil, err
		}

		varParams := []Fc{}
		if t, err := isCurToken(tokens, start, KeySyms["("]); t {
			varParamsPtr, err := parseBracedFcArr(tokens, start)
			varParams = *varParamsPtr
			if err != nil {
				return nil, err
			}
		} else if err != nil {
			return nil, err
		}

		curFcc.typeParams = typeParams
		curFcc.varParams = varParams
		previousFc = curFcc
	}

	return &previousFc, nil
}

func parseBracketedFcString(tokens *[]string, start *int) (*[]FcStr, error) {
	typeParams := []FcStr{}
	skip(tokens, start, KeySyms["["])

	for {
		fcStr, err := parseFcStr(tokens, start)

		if err != nil {
			return nil, err
		}

		typeParams = append(typeParams, fcStr)

		if t, err := isCurToken(tokens, start, KeySyms["]"]); t == true {
			*start++
			break
		} else if err != nil {
			return nil, err
		}

		if err := expectCurToken(tokens, start, KeySyms[","]); err != nil {
			return nil, err
		} else {
			*start++
		}
	}

	return &typeParams, nil
}

func parseBracedFcString(tokens *[]string, start *int) (*[]FcStr, error) {
	typeParams := []FcStr{}
	skip(tokens, start, KeySyms["("])

	for {
		fcStr, err := parseFcStr(tokens, start)

		if err != nil {
			return nil, err
		}

		typeParams = append(typeParams, fcStr)

		if t, err := isCurToken(tokens, start, KeySyms[")"]); t == true {
			*start++
			break
		} else if err != nil {
			return nil, err
		}

		if err := expectCurToken(tokens, start, KeySyms[","]); err != nil {
			return nil, err
		} else {
			*start++
		}
	}

	return &typeParams, nil
}

func parseFcStr(tokens *[]string, start *int) (FcStr, error) {
	if (*start) >= len(*tokens) {
		return FcStr(""), fmt.Errorf("unexpected end of input")
	}

	fc := FcStr((*tokens)[*start])
	*start++
	return fc, nil
}

func expectCurToken(tokens *[]string, start *int, expected string) error {
	if (*start) >= len(*tokens) {
		return fmt.Errorf("unexpected end of input")
	}

	if (*tokens)[*start] != expected {
		return fmt.Errorf("expected %s, get %s instead", expected, (*tokens)[*start])
	}

	return nil
}

func isCurToken(tokens *[]string, start *int, expected string) (bool, error) {
	if (*start) >= len(*tokens) {
		return false, fmt.Errorf("unexpected end of input")
	}

	return (*tokens)[*start] == expected, nil
}

func parseBracedFcArr(tokens *[]string, start *int) (*[]Fc, error) {
	skip(tokens, start, KeySyms["("])

	typeParams := []Fc{}
	for {
		fc, err := parseFc(tokens, start)

		if err != nil {
			return nil, err
		}

		typeParams = append(typeParams, fc)

		if t, err := isCurToken(tokens, start, KeySyms[")"]); t == true {
			*start++
			break
		} else if err != nil {
			return nil, err
		}

		if err := expectCurToken(tokens, start, KeySyms[","]); err != nil {
			return nil, err
		} else {
			*start++
		}
	}

	return &typeParams, nil
}
