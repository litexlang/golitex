import {
  BuiltinCheckNode,
  IfNode,
  IsFormNode,
  IsPropertyNode,
  LogicNode,
  OptNode,
  OrNode,
  ToCheckNode,
} from "./L_Nodes";
import { L_Env } from "./L_Env";
import { L_Composite, L_Out, L_Singleton, L_Symbol } from "./L_Structs";
import * as L_Memory from "./L_Memory";
import { L_ReportErr } from "./L_Messages";

export function checkFact(env: L_Env, toCheck: ToCheckNode): L_Out {
  try {
    const ok = env.factsInToCheckAllDeclaredOrBuiltin(toCheck);
    if (!ok) {
      env.newMessage(`[Error] ${toCheck} not declared.`);
      throw Error();
    }

    if (toCheck instanceof OptNode) {
      return checkOptFact(env, toCheck);
    } else if (toCheck instanceof IfNode) {
      return checkIfFact(env, toCheck);
    } else if (toCheck instanceof BuiltinCheckNode) {
      return checkBuiltinCheckNode(env, toCheck);
    } else {
      return L_Out.Error;
    }
  } catch {
    return L_Out.Error;
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
      L_Memory.newFact(newEnv, req);
    }

    for (const onlyIf of toCheck.onlyIfs) {
      const out = checkFact(newEnv, onlyIf);
      if (out !== L_Out.True) return out;
    }

    return L_Out.True;
  } catch {
    return env.errMesReturnL_Out(toCheck);
  }
}

function checkOptFact(env: L_Env, toCheck: OptNode): L_Out {
  // compare vars length in given opts, compare them
  function literallyCompareOptVars(
    env: L_Env,
    opt1: OptNode,
    opt2: OptNode
  ): boolean {
    try {
      if (opt1.vars.length !== opt2.vars.length) {
        return false;
      }

      for (let i = 0; i < opt1.vars.length; i++) {
        if (
          !L_Symbol.literallyCompareTwoSymbols(env, opt1.vars[i], opt2.vars[i])
        )
          return false;
      }

      env.newMessage(`[check by] ${toCheck}`);
      return true;
    } catch {
      L_ReportErr(env, literallyCompareOptVars, opt1);
      return false;
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
    // TODO: I guess in the future I should remove givenOpt.checkVars.length === 0
    if (givenOpt.checkVars === undefined || givenOpt.checkVars.length === 0) {
      // 1. known is one-layer, and we replace all vars in that layer with given opt
      let successful = true;
      const freeFixPairs: [L_Symbol, L_Symbol][] = [];
      for (let i = 0; i < known.vars.length; i++) {
        if (!L_Symbol.structureEqual(env, known.vars[i], givenOpt.vars[i])) {
          successful = false;
          break;
        } else {
          freeFixPairs.push([known.vars[i], givenOpt.vars[i]]);
        }
      }
      if (successful) {
        // TODO : A BEtter approach: check root opt name equal to given toCheck at first instead of at the end
        // must be single layer
        if (known.onlyIfs.every((e) => e instanceof OptNode)) {
          const fixedKnown = known.fix(env, freeFixPairs);
          if (fixedKnown.req.every((e) => checkFact(env, e) === L_Out.True)) {
            if (
              fixedKnown.onlyIfs.some(
                (e) =>
                  (e as OptNode).optSymbol.name === givenOpt.optSymbol.name &&
                  (e as OptNode).vars.every((v, i) =>
                    L_Symbol.literallyCompareTwoSymbols(
                      env,
                      givenOpt.vars[i],
                      v
                    )
                  )
              )
            ) {
              env.newMessage(`[check by] ${known}`);
              return true;
            }
          }
        }
      }
    } else {
      const roots: [OptNode, IfNode[]][] = known.getRootNodes();
      for (const root of roots) {
        if (root[0].optSymbol.name !== toCheck.optSymbol.name) continue;

        if (toCheck.checkVars === undefined) continue;
        if (root[1].length !== toCheck.checkVars.length) continue;

        let successful = true;
        let freeFixedPairs: [L_Symbol, L_Symbol][] = [];
        for (const [layerNum, layer] of root[1].entries()) {
          //TODO check length
          const currentPairs = LogicNode.makeFreeFixPairs(
            env,
            toCheck.checkVars[layerNum],
            layer.vars
          );
          freeFixedPairs = [...freeFixedPairs, ...currentPairs];
          if (
            //!
            // TODO: BUG: should be literally check fact instead of checkFact
            layer.req.every((e) =>
              checkIfReqLiterally(env, e.fix(env, freeFixedPairs))
            )
          ) {
          } else {
            successful = false;
            break;
          }
        }
        if (successful) {
          const fixed = root[0].fix(env, freeFixedPairs);
          if (
            L_Symbol.literallyCompareSymbolArray(env, fixed.vars, toCheck.vars)
          ) {
            env.newMessage(`[check by] ${root[1][0]}`);
            return true;
          }
        }
      }
    }

    return false;
  }

  // Main part of this function
  try {
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

        const out = literallyCompareOptVars(env, toCheck, curKnown);
        if (out) return L_Out.True;
      }
    }

    for (const curKnown of relatedKnownFacts) {
      if (curKnown instanceof IfNode) {
        //TODO
        const out = useIfToCheckOpt(env, toCheck, curKnown);
        if (out) return L_Out.True;
      }
    }

    return L_Out.Unknown;
  } catch {
    return env.errMesReturnL_Out(toCheck);
  }
}

function checkIfReqLiterally(env: L_Env, toCheck: ToCheckNode): boolean {
  try {
    if (toCheck instanceof OptNode) {
      const knowns = env.getFacts(toCheck.optSymbol.name);
      if (knowns === undefined) return false;
      for (const known of knowns) {
        if (known instanceof OptNode) {
          if (
            toCheck.isT === known.isT &&
            L_Symbol.literallyCompareSymbolArray(env, toCheck.vars, known.vars)
          ) {
            return true;
          }
        }
      }
    }

    return false;
  } catch {
    return env.errMesReturnBoolean(toCheck);
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
        toCheck.given instanceof L_Composite &&
        toCheck.given.name === toCheck.composite.name &&
        toCheck.given.values.length === toCheck.composite.values.length
      ) {
        correctForm = true;
      }

      if (!correctForm) return L_Out.Unknown;

      const freeFix: [L_Symbol, L_Symbol][] = [];
      for (let i = 0; i < (toCheck.given as L_Composite).values.length; i++) {
        freeFix.push([
          toCheck.composite.values[i],
          (toCheck.given as L_Composite).values[i],
        ]);
      }

      for (const fact of toCheck.facts) {
        const fixed = fact.fix(env, freeFix);
        const out = checkFact(env, fixed);
        if (out !== L_Out.True) {
          env.newMessage(`[Error] failed to check ${fixed}`);
          return L_Out.Unknown;
        }
      }

      return L_Out.True;
    } else {
      return L_Out.Error;
    }
  } catch {
    return env.errMesReturnL_Out(toCheck);
  }
}
