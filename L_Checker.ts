import {
  AndToCheckNode,
  BuiltinCheckNode,
  IfNode,
  IsFormNode,
  IsPropertyNode,
  LogicNode,
  OptNode,
  OrToCheckNode,
  ToCheckFormulaNode,
  ToCheckNode,
} from "./L_Nodes";
import { L_Env } from "./L_Env";
import { L_Composite, L_Out, L_Singleton, L_Symbol } from "./L_Structs";
import * as L_Memory from "./L_Memory";
import {
  L_ReportBoolErr,
  L_ReportCheckErr,
  reportCheckErr,
} from "./L_Messages";
import { DEBUG_DICT } from "./L_Executor";

export function checkFact(env: L_Env, toCheck: ToCheckNode): L_Out {
  try {
    const ok = env.factsInToCheckAllDeclaredOrBuiltin(toCheck);
    if (!ok) {
      env.report(`[Error] ${toCheck} not declared.`);
      throw Error();
    }

    if (toCheck instanceof OptNode) {
      return checkOptFact(env, toCheck);
    } else if (toCheck instanceof IfNode) {
      return checkIfFact(env, toCheck);
    } else if (toCheck instanceof BuiltinCheckNode) {
      return checkBuiltinCheckNode(env, toCheck);
    } else if (toCheck instanceof ToCheckFormulaNode) {
      return checkToCheckFormula(env, toCheck);
    } else {
      return L_Out.Error;
    }
  } catch {
    return L_ReportCheckErr(env, checkFact, toCheck);
  }
}

function checkIfFact(env: L_Env, toCheck: IfNode): L_Out {
  try {
    const newEnv = new L_Env(env);
    for (const v of toCheck.vars) {
      if (v instanceof L_Singleton) {
        newEnv.newSingletonVar(v.value);
      } else if (v instanceof L_Composite) {
        //TODO

        throw Error();
      }
    }

    for (const req of toCheck.req) {
      // TODO more error report
      if (DEBUG_DICT.checkCompositeVar && !req.varsDeclared(newEnv, [])) {
        newEnv.report(
          `[Undeclared Error] Some of variables in ${req} not declared.`
        );
        return L_Out.Error;
      }

      L_Memory.newFact(newEnv, req);
    }

    for (const onlyIf of toCheck.onlyIfs) {
      const out = checkFact(newEnv, onlyIf);
      if (out !== L_Out.True) return out;
    }

    return L_Out.True;
  } catch {
    return L_ReportCheckErr(env, checkIfFact, toCheck);
  }
}

function checkOptFact(env: L_Env, toCheck: OptNode): L_Out {
  try {
    if (checkOptFactUsingPureVar(env, toCheck) === L_Out.True) {
      return L_Out.True;
    } else {
      return checkOptFactUsingRegexVar(env, toCheck);
    }
  } catch {
    return L_ReportCheckErr(env, checkOptFact, toCheck);
  }
}

function checkOptFactUsingPureVar(env: L_Env, toCheck: OptNode): L_Out {
  // Main part of this function
  try {
    // TODO 严重的设计矛盾：composite里面的东西，究竟需不需要先定义一下？？
    if (DEBUG_DICT.checkCompositeVar && !toCheck.varsDeclared(env, [])) {
      env.report(
        `[Undeclared Error] Some of variables in ${toCheck} not declared.`
      );
      return L_Out.Error;
    }

    const relatedKnownFacts = env.getFacts(toCheck.optSymbol.name);
    if (relatedKnownFacts === undefined) {
      return L_Out.Unknown;
    }

    //* First check opt-type facts then check if-type facts so that I can check if x: p(x) {p(x)};
    for (const curKnown of relatedKnownFacts) {
      if (curKnown instanceof OptNode) {
        // TODO 这里的验证 isT 的方式我不太满意
        if (toCheck.isT !== curKnown.isT) {
          continue;
        }

        const out = useOptToCheckOpt(env, toCheck, curKnown);
        if (out) return L_Out.True;
      }
    }

    for (const curKnown of relatedKnownFacts) {
      // TODO isT 没考虑
      if (curKnown instanceof ToCheckFormulaNode) {
        const out = useToCheckFormulaToCheckOpt(env, toCheck, curKnown);
        if (out) return L_Out.True;
      }
    }

    for (const curKnown of relatedKnownFacts) {
      if (curKnown instanceof IfNode) {
        // TODO isT 没考虑
        const out = useIfToCheckOpt(env, toCheck, curKnown);
        if (out) return L_Out.True;
      }
    }

    return L_Out.Unknown;
  } catch {
    return L_ReportCheckErr(env, checkOptFact, toCheck);
  }

  // TODO 缺失一些用 formula 来验证的方式 1. "if x: (p(x) or t(x)) {(p(x) or t(x))};" 2. use if...if {or} to check
  function useToCheckFormulaToCheckOpt(
    env: L_Env,
    toCheck: OptNode,
    known: ToCheckFormulaNode
  ): boolean {
    try {
      // all roots that is contained in known
      const rootsUnderFormula = ToCheckNode.getRootOptNodes(known, []);

      // roots that related to toCheck
      const rootsWithKeyAsToCheck = rootsUnderFormula.filter(
        (e) => e[0].optSymbol.name === toCheck.optSymbol.name
      );

      /* 1. all layers are ToCheckFormulaNode */
      for (const root of rootsWithKeyAsToCheck) {
        const layers: (ToCheckFormulaNode | IfNode)[] = root[1];
        if (
          layers.every((layer) => layer instanceof ToCheckFormulaNode) &&
          toCheck.vars.length === root[0].vars.length &&
          toCheck.vars.every((e, i) =>
            L_Symbol.areLiterallyTheSame(env, e, root[0].vars[i])
          )
        ) {
          let checkedTrue = true;
          for (const [i, layer] of layers.entries()) {
            if (layer instanceof AndToCheckNode) {
              continue;
            } else if (layer instanceof OrToCheckNode) {
              if (i + 1 < layers.length && layer.left === layers[i + 1]) {
                const out = checkLiterally(
                  env,
                  layer.right.copyWithIsTReverse()
                );
                if (out) {
                  continue;
                } else {
                  checkedTrue = false;
                  break;
                }
              } else if (
                i + 1 < layers.length &&
                layer.right === layers[i + 1]
              ) {
                const out = checkLiterally(
                  env,
                  layer.left.copyWithIsTReverse()
                );
                if (out) {
                  continue;
                } else {
                  checkedTrue = false;
                  break;
                }
              } else if (i + 1 === layers.length) {
                if (root[0] === layer.left) {
                  const out = checkLiterally(
                    env,
                    layer.right.copyWithIsTReverse()
                  );
                  if (out) {
                    continue;
                  } else {
                    checkedTrue = false;
                    break;
                  }
                } else {
                  const out = checkLiterally(
                    env,
                    layer.left.copyWithIsTReverse()
                  );
                  if (out) {
                    continue;
                  } else {
                    checkedTrue = false;
                    break;
                  }
                }
              }
            }
          }

          if (checkedTrue) return true;
        }
      }

      return false;
    } catch {
      return L_ReportBoolErr(env, useToCheckFormulaToCheckOpt, toCheck);
    }
  }

  // compare vars length in given opts, compare them
  function useOptToCheckOpt(env: L_Env, opt1: OptNode, opt2: OptNode): boolean {
    try {
      if (opt1.vars.length !== opt2.vars.length) {
        return false;
      }

      for (let i = 0; i < opt1.vars.length; i++) {
        if (!L_Symbol.areLiterallyTheSame(env, opt1.vars[i], opt2.vars[i]))
          return false;
      }

      env.report(`[check by] ${toCheck}`);
      return true;
    } catch {
      return L_ReportBoolErr(
        env,
        useOptToCheckOpt,
        `Failed to compare ${opt1}, ${opt2}`
      );
    }
  }

  // use given if-fact to check operator-fact
  // There are several default ways to use given opt to fix freeVars of known
  // 1. known is one-layer, and we replace all vars in that layer with given opt
  function useIfToCheckOpt(
    env: L_Env,
    givenOpt: OptNode,
    known: IfNode
  ): boolean {
    try {
      // TODO: I guess in the future I should remove givenOpt.checkVars.length === 0
      if (givenOpt.checkVars === undefined || givenOpt.checkVars.length === 0) {
        // 1. known is one-layer, and we replace all vars in that layer with given opt
        const automaticallyAddedCheckVars = [givenOpt.vars];
        const automaticallyGeneratedOpt = new OptNode(
          givenOpt.optSymbol,
          givenOpt.vars,
          givenOpt.isT,
          automaticallyAddedCheckVars
        );
        return useIfToCheckOpt(env, automaticallyGeneratedOpt, known);
      } else {
        let roots: [OptNode, (ToCheckFormulaNode | IfNode)[]][] =
          ToCheckNode.getRootOptNodes(known, []);
        roots = roots.filter(
          (root) =>
            root[0].optSymbol.name === givenOpt.optSymbol.name &&
            givenOpt.checkVars !== undefined &&
            // ! 这里利用了Formula里不能用if的特性。这个约定可能未来就没了
            root[1].filter((e) => e instanceof IfNode).length ===
              givenOpt.checkVars.length
        );

        for (const root of roots) {
          let successful = true;
          let freeFixedPairs: [L_Symbol, L_Symbol][] = [];
          const newEnv = new L_Env(env);
          for (const [layerNum, layer] of root[1].entries()) {
            //TODO check length

            // TODO if instanceof ToCheckFormulaNode
            if (layer instanceof IfNode) {
              const currentPairs = LogicNode.makeFreeFixPairs(
                env,
                givenOpt.checkVars[layerNum],
                layer.vars
              );
              freeFixedPairs = [...freeFixedPairs, ...currentPairs];
              if (
                //! checkIfReqLiterally is very dumb and may fail at many situations
                layer.req.every((e) => {
                  return checkLiterally(newEnv, e.fix(newEnv, freeFixedPairs));
                })
              ) {
                layer.req.every((fact) =>
                  L_Memory.newFact(newEnv, fact.fix(newEnv, freeFixedPairs))
                );
              } else {
                successful = false;
                break;
              }
            } else if (layer instanceof ToCheckFormulaNode) {
              // ! 这里利用了Formula里不能用if的特性。这个约定可能未来就没了。事实上这里不用检查，因为 roots 在filter的时候已经相当于检查过了。放在这里只是为了自我提醒
              const nextLayers = root[1].slice(layerNum);
              if (!nextLayers.every((e) => e instanceof ToCheckFormulaNode)) {
                successful = false;
                break;
              }

              const out = useToCheckFormulaToCheckOpt(
                newEnv,
                toCheck,
                layer.fix(newEnv, freeFixedPairs)
              );
              return out;
            }
          }
          if (successful) {
            const fixed = root[0].fix(env, freeFixedPairs);
            if (
              L_Symbol.allSymbolsAreLiterallyTheSame(
                env,
                fixed.vars,
                givenOpt.vars
              )
            ) {
              env.report(`[check by] ${root[1][0]}`);
              return true;
            }
          }
        }
      }

      return false;
    } catch {
      return L_ReportBoolErr(env, useIfToCheckOpt, toCheck);
    }
  }
}

function checkLiterally(env: L_Env, toCheck: ToCheckNode): boolean {
  try {
    if (toCheck instanceof OptNode) {
      const knowns = env.getFacts(toCheck.optSymbol.name);
      if (knowns === undefined) return false;
      for (const known of knowns) {
        if (known instanceof OptNode) {
          if (
            toCheck.isT === known.isT &&
            L_Symbol.allSymbolsAreLiterallyTheSame(
              env,
              toCheck.vars,
              known.vars
            )
          ) {
            return true;
          }
        }
      }
    } else if (toCheck instanceof BuiltinCheckNode) {
      //TODO MAYBE I SHOULD USE CHECK literally
      return checkBuiltinCheckNode(env, toCheck) === L_Out.True;
    } else if (toCheck instanceof ToCheckFormulaNode) {
      //TODO MAYBE I SHOULD USE CHECK literally
      return checkToCheckFormulaLiterally(env, toCheck) === L_Out.True;
    } else {
      // TODO
    }

    return false;
  } catch {
    return L_ReportBoolErr(env, checkLiterally, toCheck);
  }
}

function checkBuiltinCheckNode(env: L_Env, toCheck: BuiltinCheckNode): L_Out {
  try {
    if (toCheck instanceof IsPropertyNode) {
      return env.getDef(toCheck.propertyName) !== undefined
        ? L_Out.True
        : L_Out.Unknown;
    } else if (toCheck instanceof IsFormNode) {
      let correctForm = false;
      if (
        toCheck.baseline.values.every((e) => e instanceof L_Singleton) &&
        toCheck.candidate instanceof L_Composite &&
        toCheck.candidate.name === toCheck.baseline.name &&
        toCheck.candidate.values.length === toCheck.baseline.values.length
      ) {
        correctForm = true;
      }

      if (!correctForm) return L_Out.Unknown;

      const freeFix: [L_Symbol, L_Symbol][] = [];
      for (
        let i = 0;
        i < (toCheck.candidate as L_Composite).values.length;
        i++
      ) {
        freeFix.push([
          toCheck.baseline.values[i],
          (toCheck.candidate as L_Composite).values[i],
        ]);
      }

      for (const fact of toCheck.facts) {
        const fixed = fact.fix(env, freeFix);
        let out: L_Out = L_Out.Error;
        out = checkFact(env, fixed);

        if (out !== L_Out.True) {
          env.report(`[Error] failed to check ${fixed}`);
          return L_Out.Unknown;
        }
      }

      return L_Out.True;
    } else {
      return L_Out.Error;
    }
  } catch {
    return L_ReportCheckErr(env, checkOptFact, toCheck);
  }
}

function checkToCheckFormula(env: L_Env, toCheck: ToCheckFormulaNode): L_Out {
  try {
    if (toCheck instanceof OrToCheckNode) {
      for (const fact of toCheck.getLeftRight()) {
        const newEnv = new L_Env(env);
        const another = toCheck.getLeftRight().filter((e) => e !== fact)[0];
        // 有趣的是，我这里不需要进一步地把子节点（比如如果left是or，我在本函数里把left的or再拿出来做newFact）再拿出来，因为我未来做验证的时候，我调用checkFact的时候，我又会来到这个left，这时候我再会把left的or里面的东西拿出来。
        L_Memory.newFact(newEnv, another.copyWithIsTReverse());
        const out = checkFact(newEnv, fact);
        if (out === L_Out.True) {
          return L_Out.True;
        }
      }

      return L_Out.Unknown;
    } else if (toCheck instanceof AndToCheckNode) {
      for (const fact of toCheck.getLeftRight()) {
        const out = checkFact(env, fact);
        if (out !== L_Out.True) {
          env.report(`Failed to check ${out}`);
          return out;
        }
      }

      return L_Out.True;
    }

    throw Error();
  } catch {
    return L_ReportCheckErr(env, checkOptFact, toCheck);
  }
}

function checkToCheckFormulaLiterally(
  env: L_Env,
  toCheck: ToCheckFormulaNode
): L_Out {
  try {
    if (toCheck instanceof OrToCheckNode) {
      for (const fact of toCheck.getLeftRight()) {
        const newEnv = new L_Env(env);
        const another = toCheck.getLeftRight().filter((e) => e !== fact)[0];
        // 有趣的是，我这里不需要进一步地把子节点（比如如果left是or，我在本函数里把left的or再拿出来做newFact）再拿出来，因为我未来做验证的时候，我调用checkFact的时候，我又会来到这个left，这时候我再会把left的or里面的东西拿出来。
        L_Memory.newFact(newEnv, another.copyWithIsTReverse());
        const out = checkLiterally(newEnv, fact);
        if (out) {
          return L_Out.True;
        }
      }

      return L_Out.Unknown;
    } else if (toCheck instanceof AndToCheckNode) {
      for (const fact of toCheck.getLeftRight()) {
        const out = checkLiterally(env, fact);
        if (!out) {
          env.report(`Failed to check ${out}`);
          return L_Out.Unknown;
        }
      }

      return L_Out.True;
    }

    throw Error();
  } catch {
    return L_ReportCheckErr(env, checkOptFact, toCheck);
  }
}

function checkOptFactUsingRegexVar(env: L_Env, toCheck: OptNode): L_Out {
  try {
    return L_Out.Unknown;
  } catch {
    return L_ReportCheckErr(env, checkOptFactUsingRegexVar, toCheck);
  }
}
