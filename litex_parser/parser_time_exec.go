package litex_parser

// func getUniParamsInUniFactRecursively(facts []ast.FactStmt, uniParamAtCurrentLevel []string) (map[string]struct{}, error) {
// 	uniParamsRecur := make(map[string]struct{})
// 	for _, domainFact := range facts {
// 		factAsConUni, ok := domainFact.(*ast.ConUniFactStmt)
// 		if ok {
// 			for key := range factAsConUni.UniParamsRecur {
// 				for _, curParam := range uniParamAtCurrentLevel {
// 					if curParam == key {
// 						return nil, fmt.Errorf("duplicate universal parameter in %v and current parameter slice %v", domainFact, uniParamAtCurrentLevel)
// 					}
// 				}
// 				uniParamsRecur[key] = struct{}{}
// 			}
// 			factAsConUni.UniParamsRecur = nil // 未来不再有用了，因为我只看最上层的
// 			continue
// 		}

// 		factAsGenUni, ok := domainFact.(*ast.ConUniFactStmt)
// 		if ok {
// 			for key := range factAsGenUni.UniParamsRecur {
// 				for _, curParam := range uniParamAtCurrentLevel {
// 					if curParam == key {
// 						return nil, fmt.Errorf("duplicate universal parameter in %v and current parameter slice %v", domainFact, uniParamAtCurrentLevel)
// 					}
// 				}
// 			}
// 			factAsGenUni.UniParamsRecur = nil // 未来不再有用了，因为我只看最上层的
// 			continue
// 		}
// 	}

// 	for _, paramAtCurLevel := range uniParamAtCurrentLevel {
// 		uniParamsRecur[paramAtCurLevel] = struct{}{}
// 	}

// 	return uniParamsRecur, nil
// }
