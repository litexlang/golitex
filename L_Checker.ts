import {
  AndToCheckNode,
  BuiltinCheckNode,
  FormulaSubNode,
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
import {
  FormulaKnownFactReq,
  IfKnownFactReq,
  L_Composite,
  L_KnownFactReq,
  L_Out,
  L_Singleton,
  L_Symbol,
  OptKnownFactReq,
} from "./L_Structs";
import * as L_Memory from "./L_Memory";
import { L_ReportBoolErr, L_ReportCheckErr, reportCheckErr } from "./L_Report";
import { DEBUG_DICT } from "./L_Executor";

export function checkFact(env: L_Env, toCheck: ToCheckNode): L_Out {
  try {
    const ok = env.subFactsDeclaredOrBuiltin(toCheck);
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
      }
    }

    for (const req of toCheck.req) {
      // TODO more error report
      if (DEBUG_DICT.checkCompositeVar && !req.varsDeclared(newEnv)) {
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
  // Main part of this function
  try {
    // TODO 严重的设计矛盾：composite里面的东西，究竟需不需要先定义一下？？
    if (DEBUG_DICT.checkCompositeVar && !toCheck.varsDeclared(env)) {
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
      if (curKnown instanceof OptKnownFactReq) {
        // TODO 这里的验证 isT 的方式我不太满意
        if (curKnown.opt.isT !== toCheck.isT) {
          continue;
        }

        const out = useOptToCheckOpt(env, toCheck, curKnown.opt as OptNode);
        if (out) return L_Out.True;
      }
    }

    for (const curKnown of relatedKnownFacts) {
      // TODO isT 没考虑
      if (curKnown instanceof FormulaKnownFactReq) {
        const out = useFormulaToCheckOpt(env, toCheck, curKnown);
        if (out) return L_Out.True;
      }
    }

    for (const curKnown of relatedKnownFacts) {
      if (curKnown instanceof IfKnownFactReq) {
        // TODO isT 没考虑
        const out = useIfToCheckOpt(env, toCheck, curKnown);
        if (out) return L_Out.True;
      }
    }

    return L_Out.Unknown;
  } catch {
    return L_ReportCheckErr(env, checkOptFact, toCheck);
  }

  // compare vars length in given opts, compare them
  function useOptToCheckOpt(env: L_Env, opt1: OptNode, opt2: OptNode): boolean {
    try {
      if (opt1.isT !== opt2.isT) return false;

      if (opt1.vars.length !== opt2.vars.length) {
        return false;
      }

      for (let i = 0; i < opt1.vars.length; i++) {
        if (!L_Symbol.areLiterallyIdentical(env, opt1.vars[i], opt2.vars[i]))
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

  function useIfToCheckOpt(
    env: L_Env,
    given: OptNode,
    known: IfKnownFactReq
  ): boolean {
    try {
      if (given.checkVars === undefined || given.checkVars.length === 0) {
        // 1. known is one-layer, and we replace all vars in that layer with given opt
        const autoAddedCheckVars = [given.vars];
        const autoAddedOpt = new OptNode(
          given.optSymbol,
          given.vars,
          given.isT,
          autoAddedCheckVars
        );
        return useIfToCheckOptWithCheckVars(env, autoAddedOpt, known);
      } else {
        return useIfToCheckOptWithCheckVars(env, given, known);
      }
    } catch {
      L_ReportCheckErr(env, useIfToCheckOpt, given);
      return false;
    }
  }

  // use given if-fact to check operator-fact
  // There are several default ways to use given opt to fix freeVars of known
  // 1. known is one-layer, and we replace all vars in that layer with given opt
  function useIfToCheckOptWithCheckVars(
    env: L_Env,
    givenOpt: OptNode,
    known: IfKnownFactReq
  ): boolean {
    try {
      // TODO: I guess in the future I should remove givenOpt.checkVars.length === 0

      let roots: ToCheckNode[] = known.req;

      let successful = true;
      let freeFixedPairs: [L_Symbol, L_Symbol][] = [];
      const newEnv = new L_Env(env);
      for (let i = 0; i < roots.length - 1; i++) {
        //TODO check length
        const layer = roots[i];
        const layerNum = i;

        // TODO if instanceof ToCheckFormulaNode
        if (layer instanceof IfNode) {
          const currentPairs = LogicNode.makeFreeFixPairs(
            env,
            (givenOpt.checkVars as L_Symbol[][])[layerNum],
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
          let nextLayers = roots.slice(layerNum);

          // fix every layer. the reason why we can not use known = nextLayers.map(e => e.fix(newEnv, freeFixedPairs)) as parameter of new FormulaKnownFactReq(known) is that address of left right does not correspond to layers of ToCheckNeck in that known array
          nextLayers[0] = nextLayers[0].fix(newEnv, freeFixedPairs);
          let knowns = nextLayers[0]
            .getRootOptNodes()
            .map((e) => [...e[1], e[0]]);
          knowns = knowns.filter((e) =>
            L_Symbol.optsLiterallyIdentical(
              newEnv,
              toCheck,
              e[e.length - 1] as OptNode
            )
          );
          for (const known of knowns) {
            const formulaKnownFactReq = new FormulaKnownFactReq(known);
            if (useFormulaToCheckOpt(newEnv, givenOpt, formulaKnownFactReq)) {
              newEnv.getMessages().forEach((e) => env.report(e));
              return true;
            }
          }

          newEnv.getMessages().forEach((e) => env.report(e));
          return false;
        }
      }
      if (successful) {
        const fixed = roots[roots.length - 1].fix(env, freeFixedPairs);
        if (
          L_Symbol.allSymbolsLiterallyIdentical(
            env,
            (fixed as OptNode).vars,
            givenOpt.vars
          )
        ) {
          env.report(`[check by] ${roots[0]}`);
          return true;
        }
      }

      return false;
    } catch {
      return L_ReportBoolErr(env, useIfToCheckOpt, toCheck);
    }
  }

  function useFormulaToCheckOpt(
    env: L_Env,
    toCheck: OptNode,
    known: FormulaKnownFactReq
  ): boolean {
    try {
      if (
        !L_Symbol.optsLiterallyIdentical(
          env,
          toCheck,
          known.req[known.req.length - 1] as OptNode
        )
      ) {
        return false;
      }

      let curEnv = new L_Env(env);
      for (let i = 0; i < known.req.length - 1; i++) {
        let curReq = known.req[i];

        if (curReq instanceof OrToCheckNode) {
          const out = curReq.getWhereIsGivenFactAndAnotherBranch(
            known.req[i + 1]
          );

          curEnv = new L_Env(curEnv);
          if (!checkLiterally(curEnv, out.anotherBranch.copyWithIsTReverse())) {
            curEnv.report(
              `failed to check ${toCheck} : [unknown] ${out.anotherBranch.copyWithIsTReverse()}`
            );
            return false;
          }

          if (out.itself instanceof OptNode) {
            curEnv.report(
              `[check by] ${curReq}, ${out.anotherBranch.copyWithIsTReverse()}`
            );
            curEnv.getMessages().forEach((e) => env.report(e));
            return true;
          } else {
            curEnv.report(
              `[check by] ${curReq}, ${out.anotherBranch.copyWithIsTReverse()}`
            );
            const ok = useFormulaToCheckOpt(curEnv, toCheck, known);
            curEnv.getMessages().forEach((e) => env.report(e));
            return ok;
          }
        } else if (curReq instanceof AndToCheckNode) {
          curEnv.report(`[check by] ${curReq}`);
          continue;
        }
      }

      if (checkLiterally(curEnv, known.req[known.req.length - 1])) return true;
      else return false;
    } catch {
      return L_ReportBoolErr(env, useFormulaToCheckOpt, toCheck);
    }
  }
}

function checkLiterally(env: L_Env, toCheck: ToCheckNode): boolean {
  try {
    if (toCheck instanceof OptNode) {
      const knowns = env.getFacts(toCheck.optSymbol.name);
      if (knowns === undefined) return false;
      for (const known of knowns) {
        if (known instanceof OptKnownFactReq) {
          if (
            toCheck.isT === known.opt.isT &&
            L_Symbol.allSymbolsLiterallyIdentical(
              env,
              toCheck.vars,
              known.opt.vars
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
      return checkToCheckFormula(env, toCheck) === L_Out.True;
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

// function checkToCheckFormulaLiterally(
//   env: L_Env,
//   toCheck: ToCheckFormulaNode
// ): L_Out {
//   try {
//     if (toCheck instanceof OrToCheckNode) {
//       for (const fact of toCheck.getLeftRight()) {
//         const newEnv = new L_Env(env);
//         const another = toCheck.getLeftRight().filter((e) => e !== fact)[0];
//         // 有趣的是，我这里不需要进一步地把子节点（比如如果left是or，我在本函数里把left的or再拿出来做newFact）再拿出来，因为我未来做验证的时候，我调用checkFact的时候，我又会来到这个left，这时候我再会把left的or里面的东西拿出来。
//         L_Memory.newFact(newEnv, another.copyWithIsTReverse());
//         const out = checkLiterally(newEnv, fact);
//         if (out) {
//           return L_Out.True;
//         }
//       }

//       return L_Out.Unknown;
//     } else if (toCheck instanceof AndToCheckNode) {
//       for (const fact of toCheck.getLeftRight()) {
//         const out = checkLiterally(env, fact);
//         if (!out) {
//           env.report(`Failed to check ${out}`);
//           return L_Out.Unknown;
//         }
//       }

//       return L_Out.True;
//     }

//     throw Error();
//   } catch {
//     return L_ReportCheckErr(env, checkOptFact, toCheck);
//   }
// }
