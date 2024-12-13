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
import { L_ReportErr, reportCheckErr } from "./L_Messages";

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

      env.report(`[check by] ${toCheck}`);
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
      const automaticallyAddedCheckVars = [givenOpt.vars];
      const automaticallyGeneratedOpt = new OptNode(
        givenOpt.optSymbol,
        givenOpt.vars,
        givenOpt.isT,
        automaticallyAddedCheckVars
      );
      return useIfToCheckOpt(env, automaticallyGeneratedOpt, known);
    } else {
      const roots: [OptNode, IfNode[]][] = known.getRootOptNodes();
      for (const root of roots) {
        if (root[0].optSymbol.name !== givenOpt.optSymbol.name) continue;

        if (givenOpt.checkVars === undefined) continue;
        if (root[1].length !== givenOpt.checkVars.length) continue;

        let successful = true;
        let freeFixedPairs: [L_Symbol, L_Symbol][] = [];
        for (const [layerNum, layer] of root[1].entries()) {
          //TODO check length
          const currentPairs = LogicNode.makeFreeFixPairs(
            env,
            givenOpt.checkVars[layerNum],
            layer.vars
          );
          freeFixedPairs = [...freeFixedPairs, ...currentPairs];
          if (
            //! checkIfReqLiterally is very dumb and may fail at many situations
            layer.req.every((e) => {
              return checkIfReqLiterally(env, e.fix(env, freeFixedPairs));
            })
          ) {
          } else {
            successful = false;
            break;
          }
        }
        if (successful) {
          const fixed = root[0].fix(env, freeFixedPairs);
          if (
            L_Symbol.literallyCompareSymbolArray(env, fixed.vars, givenOpt.vars)
          ) {
            env.report(`[check by] ${root[1][0]}`);
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
    } else if (toCheck instanceof BuiltinCheckNode) {
      //TODO MAYBE I SHOULD USE CHECK literally
      return checkBuiltinCheckNode(env, toCheck) === L_Out.True;
    } else {
      // TODO
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
    return env.errMesReturnL_Out(toCheck);
  }
}

function checkToCheckFormula(env: L_Env, toCheck: ToCheckFormulaNode): L_Out {
  try {
    if (toCheck instanceof OrToCheckNode) {
      for (const fact of toCheck.getLeftRight()) {
        const out = checkFact(env, fact);
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
    return reportCheckErr(env, checkToCheckFormula.name, toCheck);
  }
}
