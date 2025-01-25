package parser

import "fmt"

func skip(tokens *[]string, start *int, expected ...string) error {
	// 边界检查：start不能越界
	if *start >= len(*tokens) {
		return fmt.Errorf("unexpected end of input")
	}

	// 情况1：没有传入expected参数时直接递增
	if len(expected) == 0 {
		*start++ // ✅ 直接递增
		return nil
	}

	// 情况2：有expected参数时执行原有逻辑
	if (*tokens)[*start] == expected[0] {
		*start++ // ✅ 匹配成功后递增
	} else {
		return fmt.Errorf("expected '%s', but got '%s'", expected[0], (*tokens)[*start])
	}

	return nil
}

func parseTypeVarPairBracket(tokens *[]string, start *int) (*varTypePairBracketBrace, error) {
	pairs := []VarTypePair{}
	facts := []FactStmt{}

	err := skip(tokens, start, KeywordSymbols["["])
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

		if (*tokens)[*start] == KeywordSymbols["]"] {
			*start++
			break
		}

		if (*tokens)[*start] == KeywordSymbols["::"] {
			break
		}

		err := skip(tokens, start, KeywordSymbols[","])
		if err != nil {
			return nil, err
		}
	}

	if *start < len(*tokens) && (*tokens)[*start] == KeywordSymbols["::"] {
		*start++
		for *start < len(*tokens) && (*tokens)[*start] != KeywordSymbols["]"] {
			fact, err := parseFactExprStmt(tokens, start)
			if err != nil {
				return nil, err
			}

			facts = append(facts, fact)

			if (*tokens)[*start] == KeywordSymbols["]"] {
				*start++
				break
			}

			err = skip(tokens, start, KeywordSymbols[","])
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

	err := skip(tokens, start, KeywordSymbols["("])
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

		if (*tokens)[*start] == KeywordSymbols[")"] {
			*start++
			break
		}

		if (*tokens)[*start] == KeywordSymbols["::"] {
			break
		}

		err := skip(tokens, start, KeywordSymbols[","])
		if err != nil {
			return nil, err
		}
	}

	if *start < len(*tokens) && (*tokens)[*start] == KeywordSymbols["::"] {
		*start++
		for *start < len(*tokens) && (*tokens)[*start] != KeywordSymbols[")"] {
			fact, err := parseFactExprStmt(tokens, start)
			if err != nil {
				return nil, err
			}

			facts = append(facts, fact)

			if (*tokens)[*start] == KeywordSymbols[")"] {
				*start++
				break
			}

			err = skip(tokens, start, KeywordSymbols[","])
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
	skip(tokens, start, KeywordSymbols["("])

	vars := []Var{}
	// parseVar from index start, skip , between, end when )
	for *start < len(*tokens) {
		v, err := parseVar(tokens, start)
		if err != nil {
			return nil, err
		}
		vars = append(vars, v)

		if (*tokens)[*start] == KeywordSymbols[")"] {
			*start++
			return vars, nil
		}

		if (*tokens)[*start] == KeywordSymbols[","] {
			*start++
		}
	}

	return nil, fmt.Errorf("expected ')', but got '%s'", (*tokens)[*start])
}

func ParseSingletonVarBracket(tokens *[]string, start *int) (*[]string, error) {
	skip(tokens, start, KeywordSymbols["["])

	typeVars := []string{}
	// parseVar from index start, skip , between, end when )
	for *start < len(*tokens) {
		v := (*tokens)[*start]
		*start += 1
		typeVars = append(typeVars, v)

		if (*tokens)[*start] == KeywordSymbols["]"] {
			*start++
			return &typeVars, nil
		}

		if (*tokens)[*start] == KeywordSymbols[","] {
			*start++
		}
	}

	return nil, fmt.Errorf("expected ']', but got '%s'", (*tokens)[*start])
}

func parseFCC(tokens *[]string, start *int) (*FCC, error) {
	var fcc FCC
	var firstSymbol FCStr = FCStr((*tokens)[*start])
	fcc = firstSymbol
	*start++

	for {
		typeParams := []FCC{}
		varParams := []FCC{}

		if (*tokens)[*start] == KeywordSymbols["["] {
			skip(tokens, start, KeywordSymbols["["])
			if (*tokens)[*start] == KeywordSymbols["]"] {
				*start++
			} else {
				for {
					var fc FCStr = FCStr((*tokens)[*start])
					typeParams = append(typeParams, fc)
					*start++

					if (*tokens)[*start] == KeywordSymbols[")"] {
						*start++
						break
					}

					if (*tokens)[*start] == KeywordSymbols[","] {
						*start++
					}
				}
			}
		}

		if (*tokens)[*start] == KeywordSymbols["("] {
			skip(tokens, start, KeywordSymbols["("])
			if (*tokens)[*start] == KeywordSymbols[")"] {
				*start++
			} else {
				for {
					fc, err := parseFCC(tokens, start)

					if err != nil {
						return nil, err
					}

					varParams = append(varParams, fc)
					*start++

					if (*tokens)[*start] == KeywordSymbols[")"] {
						*start++
						break
					}

					if (*tokens)[*start] == KeywordSymbols[","] {
						*start++
					}
				}
			}
		}
	}

	return &fcc, nil
}
