import {
  AndToCheckNode,
  BuiltinCheckNode,
  IfNode,
  IsFormNode,
  IsConceptNode,
  LogicNode,
  OptFactNode,
  OrToCheckNode,
  FormulaFactNode,
  L_FactNode,
  FactsNode,
  EqualFact,
  SingletonLogicVar,
  CompositeLogicVar,
  LogicVar,
} from "./L_Facts";
import { L_Env } from "./L_Env";
import {
  FormulaKnownFactReq,
  IfKnownFactReq,
  L_Out,
  OptKnownFactReq,
} from "./L_Structs";
import { L_Composite, L_Singleton, L_Symbol } from "./L_Symbols";
import * as L_Memory from "./L_Memory";
import { L_ReportBoolErr, L_ReportCheckErr, L_ReportErr } from "./L_Report";

export function checkFact(env: L_Env, toCheck: L_FactNode): L_Out {
  try {
    env.tryFactDeclaredOrBuiltin(toCheck);

    if (toCheck instanceof OptFactNode) {
      return checkOptFact(env, toCheck);
    } else if (toCheck instanceof IfNode) {
      return checkIfFact(env, toCheck);
    } else if (toCheck instanceof BuiltinCheckNode) {
      return checkBuiltinCheckNode(env, toCheck);
    } else if (toCheck instanceof FormulaFactNode) {
      return checkToCheckFormula(env, toCheck);
    } else if (toCheck instanceof FactsNode) {
      return checkFacts(env, toCheck);
    } else {
      return L_Out.Error;
    }
  } catch (error) {
    L_ReportCheckErr(env, checkFact, toCheck);
    throw error;
  }
}

function checkOptFact(env: L_Env, toCheck: OptFactNode): L_Out {
  try {
    if (resolveBuiltinOpts(env, toCheck)) return L_Out.True;

    const concept = env.getConcept(toCheck.optSymbol.name);
    if (concept === undefined) {
      L_ReportErr(env, checkOptFact, `fact ${toCheck} not declared`);
      throw Error();
    }

    if (!concept.commutative) {
      return checkOptFactNotCommutatively(env, toCheck);
    } else {
      const out = checkOptFactNotCommutatively(env, toCheck);
      if (out === L_Out.True || out === L_Out.Error) return out;
      const interchanged = toCheck.copyCommutatively();
      if (interchanged === undefined) {
        return L_Out.Error;
      }
      return checkOptFactNotCommutatively(env, interchanged);
    }
  } catch {
    return L_ReportCheckErr(env, checkOptFact, toCheck);
  }

  function resolveBuiltinOpts(env: L_Env, fact: OptFactNode): boolean {
    if (fact instanceof EqualFact) {
      if (L_Symbol.symbolArrLiteralEql(env, [fact.vars[0]], [fact.vars[1]])) {
        env.report(
          `[check by] ${fact.vars[0]} and ${fact.vars[1]} literally equal.`
        );
        return true;
      }
    }
    return false;
  }
}

function checkIfFact(env: L_Env, toCheck: IfNode): L_Out {
  try {
    const newEnv = new L_Env(env);
    for (const v of toCheck.vars) {
      if (v instanceof SingletonLogicVar) {
        newEnv.tryNewSingleton(v.name.value);
      } else if (v instanceof CompositeLogicVar) {
        newEnv.tryNewSingleton(v.name.value);
        v.freeVars.forEach((e) => newEnv.tryNewSingleton(e.value));
        newEnv.tryNewAlias(v.name, [v.form]);
      } else {
        env.report(`Failed when manipulating var in ifNode ${toCheck}`);
        throw Error();
      }
    }

    for (const req of toCheck.req) {
      L_Memory.tryNewFact(newEnv, req);
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

function checkOptFactNotCommutatively(env: L_Env, toCheck: OptFactNode): L_Out {
  // Main part of this function
  try {
    // TODO ? 需要验证一下toCheck的composite是否符合被定义时的要求
    for (const v of toCheck.vars) {
      if (v instanceof CompositeLogicVar) {
        env.report(`\n[check ${v.form} requirements]`);
        if (!v.form.compositeSatisfyItsReq(env)) {
          env.report(`[end of check ${v.form} requirements]\n`);
          return L_Out.Unknown;
        } else {
          env.report(`[end of check ${v.form} requirements]\n`);
        }
      }
    }

    toCheck = toCheck.fixByIfVars(env, []); // Used to fix indexed symbols

    const relatedKnownFacts = env.tryGetFacts(toCheck.optSymbol.name);
    if (relatedKnownFacts === undefined) {
      return L_Out.Unknown;
      // return useLibToCheckOpt(env, toCheck);
    }

    //* First check opt-type facts then check if-type facts so that I can check if x: p(x) {p(x)};
    for (const curKnown of relatedKnownFacts) {
      if (curKnown instanceof OptKnownFactReq) {
        // TODO 这里的验证 isT 的方式我不太满意
        if (curKnown.opt.isT !== toCheck.isT) {
          continue;
        }

        const out = useOptToCheckOpt(env, toCheck, curKnown.opt as OptFactNode);
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
    // return useLibToCheckOpt(env, toCheck);
  } catch {
    return L_ReportCheckErr(env, checkOptFactNotCommutatively, toCheck);
  }

  // compare vars length in given opts, compare them
  function useOptToCheckOpt(
    env: L_Env,
    opt1: OptFactNode,
    opt2: OptFactNode
  ): boolean {
    try {
      if (opt1.isT !== opt2.isT) return false;

      if (opt1.vars.length !== opt2.vars.length) {
        return false;
      }

      for (let i = 0; i < opt1.vars.length; i++) {
        if (!L_Symbol.literalEql(env, opt1.vars[i], opt2.vars[i])) return false;
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
    given: OptFactNode,
    known: IfKnownFactReq
  ): boolean {
    try {
      if (given.checkVars === undefined || given.checkVars.length === 0) {
        // 1. known is one-layer, and we replace all vars in that layer with given opt
        const autoAddedCheckVars = [given.vars];
        const autoAddedOpt = new OptFactNode(
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
  //! TODO: HOW TO PROCESS VARS FORM?
  function useIfToCheckOptWithCheckVars(
    env: L_Env,
    givenOpt: OptFactNode,
    known: IfKnownFactReq
  ): boolean {
    try {
      // TODO: I guess in the future I should remove givenOpt.checkVars.length === 0

      const roots: L_FactNode[] = known.req;

      let successful = true;
      let freeFixedPairs: [L_Symbol, L_Symbol][] = [];
      const newEnv = new L_Env(env);
      if (givenOpt.checkVars === undefined) throw Error();
      for (let i = 0; i < roots.length - 1; i++) {
        //TODO check length
        const layer = roots[i];
        const layerNum = i;

        // TODO if instanceof ToCheckFormulaNode
        if (layer instanceof IfNode) {
          const optFreeFixMap = new Map<string, string>();
          for (const [j, v] of layer.vars.entries()) {
            if (v instanceof LogicVar) {
              if (!(givenOpt.checkVars[i][j] instanceof L_Singleton))
                throw Error();

              optFreeFixMap.set(
                v.name.value,
                (givenOpt.checkVars[i][j] as L_Singleton).value
              );
            }
          }

          layer.fixOpt(env, optFreeFixMap);

          for (const [j, curGivenVar] of givenOpt.checkVars[i].entries()) {
            if (!layer.vars[j].weakEql(env, curGivenVar)) {
              return false;
            }
          }

          const currentPairs: [L_Symbol, L_Symbol][] =
            LogicNode.makeFreeFixPairs(
              env,
              (givenOpt.checkVars as L_Symbol[][])[layerNum],
              layer
            );

          //! ????????? 需要在这里检查一下，传入的 symbol 是否是 形如 所要求的那样

          // //* CHECK WHETHER THE GIVEN VAR SATISFIES ITS FORM.
          // for (const formReq of layer.varsFormReq) {
          //   let done = false;
          //   for (const pair of currentPairs) {
          //     if ((pair[0] as L_Singleton).value === formReq.key.value) {
          //       if (L_Symbol.strongStructurallyEql(formReq.form, pair[1])) {
          //         done = true;

          //         // TODO 下面是把 form 里的符号拿出来建立新的对应关系的逻辑。未来显然一定会被删除。
          //         freeFixedPairs.push(
          //           ...L_Symbol.rootSingletonPairsOfStructurallyIdenticalSymbols(
          //             formReq.form,
          //             pair[1]
          //           )
          //         );

          //         continue;
          //       } else {
          //         throw Error();
          //       }
          //     }
          //     if (done) break;
          //   }
          //   if (done) continue;
          //   else throw Error(`Some variable in formReq is not passed`);
          // }

          freeFixedPairs = [...freeFixedPairs, ...currentPairs];

          // TODO: INPUT VARS INTRODUCED IN FORM REQ

          if (
            //! checkIfReqLiterally is very dumb and may fail at many situations
            layer.req.every((e) => {
              return checkLiterally(
                newEnv,
                e.fixByIfVars(newEnv, freeFixedPairs)
              );
            })
          ) {
            layer.req.every((fact) =>
              L_Memory.tryNewFact(
                newEnv,
                fact.fixByIfVars(newEnv, freeFixedPairs)
              )
            );
          } else {
            successful = false;
            break;
          }
        } else if (layer instanceof FormulaFactNode) {
          // ! 这里利用了Formula里不能用if的特性。这个约定可能未来就没了。事实上这里不用检查，因为 roots 在filter的时候已经相当于检查过了。放在这里只是为了自我提醒
          const nextLayers = roots.slice(layerNum);

          // fix every layer. the reason why we can not use known = nextLayers.map(e => e.fix(newEnv, freeFixedPairs)) as parameter of new FormulaKnownFactReq(known) is that address of left right does not correspond to layers of ToCheckNeck in that known array
          nextLayers[0] = nextLayers[0].fixByIfVars(newEnv, freeFixedPairs);
          let knowns = nextLayers[0]
            .getRootOptNodes()
            .map((e) => [...e[1], e[0]]);
          knowns = knowns.filter((e) =>
            OptFactNode.literallyIdentical(
              newEnv,
              toCheck,
              e[e.length - 1] as OptFactNode
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
        const fixed = roots[roots.length - 1].fixByIfVars(env, freeFixedPairs);
        if (
          L_Symbol.symbolArrLiteralEql(
            env,
            (fixed as OptFactNode).vars,
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
    toCheck: OptFactNode,
    known: FormulaKnownFactReq
  ): boolean {
    try {
      if (
        !OptFactNode.literallyIdentical(
          env,
          toCheck,
          known.req[known.req.length - 1] as OptFactNode
        )
      ) {
        return false;
      }

      let curEnv = new L_Env(env);
      for (let i = 0; i < known.req.length - 1; i++) {
        const curReq = known.req[i];

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

          if (out.itself instanceof OptFactNode) {
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

function checkLiterally(env: L_Env, toCheck: L_FactNode): boolean {
  try {
    if (toCheck instanceof OptFactNode) {
      const knowns = env.tryGetFacts(toCheck.optSymbol.name);
      if (knowns === undefined) return false;
      for (const known of knowns) {
        if (known instanceof OptKnownFactReq) {
          if (
            toCheck.isT === known.opt.isT &&
            L_Symbol.symbolArrLiteralEql(env, toCheck.vars, known.opt.vars)
          ) {
            return true;
          }
        }
      }
    } else if (toCheck instanceof BuiltinCheckNode) {
      //TODO MAYBE I SHOULD USE CHECK literally
      return checkBuiltinCheckNode(env, toCheck) === L_Out.True;
    } else if (toCheck instanceof FormulaFactNode) {
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
    if (toCheck instanceof IsConceptNode) {
      return checkIsConcept(env, toCheck);
    } else if (toCheck instanceof IsFormNode) {
      return checkIsForm(env, toCheck);
    } else {
      return L_Out.Error;
    }
  } catch {
    return L_ReportCheckErr(env, checkBuiltinCheckNode, toCheck);
  }
}

function checkToCheckFormula(env: L_Env, toCheck: FormulaFactNode): L_Out {
  try {
    if (toCheck instanceof OrToCheckNode) {
      for (const fact of toCheck.getLeftRight()) {
        const newEnv = new L_Env(env);
        const another = toCheck.getLeftRight().filter((e) => e !== fact)[0];
        // 有趣的是，我这里不需要进一步地把子节点（比如如果left是or，我在本函数里把left的or再拿出来做newFact）再拿出来，因为我未来做验证的时候，我调用checkFact的时候，我又会来到这个left，这时候我再会把left的or里面的东西拿出来。
        L_Memory.tryNewFact(newEnv, another.copyWithIsTReverse());
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
    return L_ReportCheckErr(env, checkToCheckFormula, toCheck);
  }
}

// async function useLibToCheckOpt(env: L_Env) {
//   try {
//     const paths = env.getIncludes();

//     for (const path of paths) {
//       const external = await import(path);

//       // Assuming external is a module with functions, define the type
//       type ExternalModule = {
//         [key: string]: (...args: any[]) => any; // This defines that the module has string keys, and each value is a function
//       };

//       const typedExternal = external as ExternalModule;

//       // Iterate over all properties in the typed external object
//       for (const prop in typedExternal) {
//         if (typeof typedExternal[prop] === "function") {
//           // console.log(`Found function: ${prop}`);
//           // You can call the function here if needed
//           typedExternal[prop](); // Uncomment to run the function
//         }
//       }
//     }

//     return L_Out.Unknown;
//   } catch (err) {
//     env.report(`加载模块失败:${err}`);
//     return L_Out.Error;
//   }
// }

// function useLibToCheckOpt(env: L_Env, opt: OptFactNode) {
//   try {
//     const paths = env.getIncludes();

//     for (const path of paths) {
//       // Synchronously require the module
//       const external = require(path);

//       // Assuming external is a module with functions, define the type
//       type ExternalModule = {
//         [key: string]: (...args: any[]) => any; // This defines that the module has string keys, and each value is a function
//       };

//       const typedExternal = external as ExternalModule;

//       // Iterate over all properties in the typed external object
//       for (const prop in typedExternal) {
//         if (typeof typedExternal[prop] === "function") {
//           // console.log(`Found function: ${prop}`);
//           // You can call the function here if needed
//           const out = typedExternal[prop](env, opt); // Uncomment to run the function
//           if (out === L_Out.True || out === L_Out.False || out === L_Out.Error)
//             return out;
//         }
//       }
//     }

//     return L_Out.Unknown;
//   } catch (err) {
//     env.report(`加载模块失败: ${err}`);
//     return L_Out.Error;
//   }
// }

function checkIsConcept(env: L_Env, toCheck: IsConceptNode): L_Out {
  if (env.getConcept(toCheck.concept) === undefined) {
    throw Error(`${toCheck.concept} is not a declared concept.`);
  }

  return L_Out.True;
}

function checkIsForm(env: L_Env, toCheck: IsFormNode): L_Out {
  let correctForm = false;
  if (
    toCheck.baseline.values.every((e: L_Symbol) => e instanceof L_Singleton) &&
    toCheck.candidate instanceof L_Composite &&
    toCheck.candidate.name === toCheck.baseline.name &&
    toCheck.candidate.values.length === toCheck.baseline.values.length
  ) {
    correctForm = true;
  }

  if (!correctForm) return L_Out.Unknown;

  const freeFix: [L_Symbol, L_Symbol][] = [];
  for (let i = 0; i < (toCheck.candidate as L_Composite).values.length; i++) {
    freeFix.push([
      toCheck.baseline.values[i],
      (toCheck.candidate as L_Composite).values[i],
    ]);
  }

  for (const fact of toCheck.facts) {
    const fixed = fact.fixByIfVars(env, freeFix);
    let out: L_Out = L_Out.Error;
    out = checkFact(env, fixed);

    if (out !== L_Out.True) {
      env.report(`[Error] failed to check ${fixed}`);
      return L_Out.Unknown;
    }
  }

  return L_Out.True;
}

function checkFacts(env: L_Env, toCheck: FactsNode): L_Out {
  const newEnv = new L_Env(env);
  const newCheckVars = toCheck.varsPairs.map((e) => e.map((v) => v[0]));

  for (const fact of toCheck.facts) {
    // TODO The original source code is changed. It's better to deep copy
    fact.getRootOptNodes().forEach((e) => (e[0].checkVars = newCheckVars));
    const out = checkFact(newEnv, fact);
    if (out !== L_Out.True) return out;
  }

  return L_Out.True;
}
