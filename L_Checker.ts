import { IfNode, OptNode, OrNode, ToCheckNode } from "./L_Nodes";
import { L_Env } from "./L_Env";
import { L_Composite, L_Out, L_Singleton, L_Symbol } from "./L_Structs";
import * as L_Memory from "./L_Memory";
import { L_ReportErr } from "./L_Messages";

export function checkFact(env: L_Env, toCheck: ToCheckNode): L_Out {
  try {
    if (toCheck instanceof OptNode) {
      return checkOptFact(env, toCheck);
    } else {
      return L_Out.Error;
    }
  } catch {
    return L_Out.Error;
  }
}

export function checkOptFact(env: L_Env, toCheck: OptNode): L_Out {
  try {
    const relatedKnownFacts = env.getFacts(toCheck.optSymbol.name);
    if (relatedKnownFacts === undefined) {
      return L_Out.Unknown;
    }
    for (const curKnown of relatedKnownFacts) {
      if (curKnown instanceof OptNode) {
        const out = literallyCompareOptVars(env, toCheck, curKnown);
        if (out) return L_Out.True;
      } else if (curKnown instanceof IfNode) {
      }
    }

    return L_Out.Unknown;
  } catch {
    return env.errMesReturnL_Out(toCheck);
  }
}

// compare vars length in given opts, compare them literally
export function literallyCompareOptVars(
  env: L_Env,
  opt1: OptNode,
  opt2: OptNode
): boolean {
  try {
    if (opt1.vars.length !== opt2.vars.length) {
      return false;
    }

    for (let i = 0; i < opt1.vars.length; i++) {
      if (!literallyCompareVars(env, opt1.vars[i], opt2.vars[i])) return false;
    }

    return true;
  } catch {
    L_ReportErr(env, literallyCompareOptVars, opt1);
    return false;
  }
}

export function literallyCompareVars(
  env: L_Env,
  var1: L_Symbol,
  var2: L_Symbol
) {
  try {
    if (var1 instanceof L_Singleton && var2 instanceof L_Singleton) {
      return var1.value === var2.value;
    } else if (var1 instanceof L_Composite && var2 instanceof L_Composite) {
      // name of composite symbol must be equal
      if (var1.name !== var2.name) {
        return false;
      }

      // vars of composite symbol must be equal
      if (var1.values.length !== var2.values.length) {
        return false;
      } else {
        for (let i = 0; i < var1.values.length; i++) {
          if (!literallyCompareVars(env, var1.values[i], var2.values[i])) {
            return false;
          }
        }
        return true;
      }
    } else {
      return false;
    }
  } catch {
    L_ReportErr(env, literallyCompareVars);
  }
}

// 两个符号字面量结构一样，比如singleton和composite就不一样，然后composite和composite之间，需要name一样才行。任何两个singleton的类型都一样。本函数用于对于 know if x, \frac{1,2} 里面的req里，自由变量和 toCheck 的变量的形式 需要对上
export function literalStructureEqual(
  env: L_Env,
  symbol1: L_Symbol,
  symbol2: L_Symbol
): boolean {
  if (symbol1 instanceof L_Singleton && symbol2 instanceof L_Singleton) {
    return true;
  } else if (symbol1 instanceof L_Composite && symbol2 instanceof L_Composite) {
    if (symbol1.name === symbol2.name) {
      for (let i = 0; i < symbol1.values.length; i++) {
        if (!literalStructureEqual(env, symbol1.values[i], symbol2.values[i])) {
          return false;
        }
      }
      return true;
    } else {
      return false;
    }
  } else {
    return false;
  }
}

//-----------------------------------------------------------

export function check(
  env: L_Env,
  toCheck: ToCheckNode,
  toCheckVarsFromIf: string[][] = []
): L_Out {
  if (toCheck instanceof OptNode) {
    let out = checkOpt(env, toCheck, true, toCheckVarsFromIf);
    if (out === L_Out.Unknown) {
      out = checkOpt(env, toCheck.copyWithoutIsT(!toCheck.isT));
      if (out === L_Out.True) {
        return L_Out.False;
      }
    }
    return out;
  } else if (toCheck instanceof IfNode) {
    return checkIfThen(env, toCheck, toCheckVarsFromIf);
  } else if (toCheck instanceof OrNode) {
    return checkOr(env, toCheck);
  }

  return L_Out.Unknown;
}

export function checkIfThen(
  env: L_Env,
  toCheck: IfNode,
  toCheckVarsFromIf: string[][]
): L_Out {
  if (toCheck.isT === false) {
    env.newMessage(`not-if-then fact ${toCheck} can not be checked directly.`);
    return L_Out.Error;
  }

  const out = openEnvAndCheck(env, toCheck, toCheckVarsFromIf);
  return out;

  function openEnvAndCheck(
    oldEnv: L_Env,
    toCheck: IfNode,
    toCheckVarsFromIf: string[][]
  ): L_Out {
    const newEnv = new L_Env(oldEnv);

    for (const e of toCheck.vars) {
      const ok = newEnv.newVar(e);
      if (!ok) {
        newEnv.getMessages().forEach((e) => env.newMessage(e));
        return L_Out.Error;
      }
    }

    for (const f of toCheck.req) L_Memory.store(newEnv, f, [], true);
    for (const onlyIf of toCheck.onlyIfs) {
      const out = check(newEnv, onlyIf, [...toCheckVarsFromIf, toCheck.vars]);
      if (out !== L_Out.True) return out;
      else {
        // checked facts in then are used as stored fact.
        L_Memory.store(newEnv, toCheck, [], true);
      }
    }

    return L_Out.True;
  }
}

/** MAIN FUNCTION OF THE WHOLE PROJECT
 *  check fact using stored facts. If the stored fact has no extra requirements,
 *  then we literally check whether the stored fact can be used to validate
 *  given toCheck (literally: if the given variable is for-all type, or has
 *  the same literal as stored fact). Else I open a new environment for each
 *  level of if and if given req is operator-type then if all variables
 *  are not free, I check this req, else i store the fact into new environment, or
 *  given req is if-then type, I check it recursively.
 *  WARNING: YOU SHOULD NOT DECLARE FREE VARIABLE WITH THE SAME NAME
 *  IN DIFFERENT LEVELS OF IFs in IF-THEN TYPE FACTS.
 */
export function checkOpt(
  env: L_Env,
  toCheck: OptNode,
  useCheckVarsFromIf: boolean = true,
  toCheckVarsFromIf: string[][] = []
): L_Out {
  return L_Out.Error;
  //*
  // if (isToCheckBuiltin(toCheck)) {
  //   env.newMessage(`checked by builtins.`);
  //   switch (toCheck.optSymbol.name) {
  //     case "is_property":
  //       return isPropertyBuiltinCheck(env, toCheck);
  //     // case ExistKeyword:
  //     //   return existBuiltinCheck(env, toCheck);
  //     default:
  //       return L_Out.Error;
  //   }
  // }
  // const knowns = L_Memory.getStoredFacts(env, toCheck);
  // if (knowns === undefined) return L_Out.Unknown;
  // for (const known of knowns as StoredFact[]) {
  //   if (
  //     (toCheck instanceof ExistNode && !(known instanceof StoredExist)) ||
  //     (!(toCheck instanceof ExistNode) && known instanceof StoredExist)
  //   ) {
  //     continue;
  //   }
  //   // check req
  //   if (known.req.length > 0) {
  //     const map = new Map<string, string>();
  //     if (known.isT !== toCheck.isT) continue;
  //     if (toCheck.checkVars !== undefined) {
  //       for (let i = 0; i < toCheck.checkVars.length; i++) {
  //         for (let j = 0; j < toCheck.checkVars[i].length; j++) {
  //           map.set(known.req[i].vars[j], toCheck.checkVars[i][j]);
  //         }
  //       }
  //     } else {
  //       const freeVarsInKnown: string[] = [];
  //       for (const r of known.req) {
  //         for (const v of r.vars) {
  //           freeVarsInKnown.includes(v);
  //         }
  //       }
  //       const fixedVarsInKnown: string[] = [];
  //       for (const v of known.vars) {
  //         if (!freeVarsInKnown.includes(v)) {
  //           // map.set(v, v);
  //           fixedVarsInKnown.push(v);
  //         }
  //       }
  //       let fixVarInKnownAndGivenVarLiterallyTheSame = true;
  //       for (const [i, v] of toCheck.vars.entries()) {
  //         if (fixedVarsInKnown.includes(known.vars[i])) {
  //           if (known.vars[i] !== v) {
  //             fixVarInKnownAndGivenVarLiterallyTheSame = false;
  //             break;
  //           }
  //         } else {
  //           map.set(known.vars[i], v);
  //         }
  //       }
  //       if (!fixVarInKnownAndGivenVarLiterallyTheSame) {
  //         continue;
  //       }
  //     }
  //     const fixedKnown = known.fixStoredFact(env, map);
  //     let out = L_Out.True;
  //     for (const r of fixedKnown.req as StoredReq[]) {
  //       for (const fact of r.req as ToCheckNode[]) {
  //         if (fact instanceof OptNode) {
  //           out = checkOptLiterally(env, fact);
  //           if (out !== L_Out.True) break;
  //         } else {
  //           //! NEED TO IMPLEMENT HOW TO CHECK If-Then Literally?
  //           // 也可以是  out = checkIfThen(env, fact as IfNode, []);
  //           out = checkIfThen(env, fact as IfNode, toCheckVarsFromIf);
  //         }
  //       }
  //       if (out === L_Out.Unknown) break;
  //     }
  //     if (out === L_Out.True) {
  //       env.newMessage(`[checked by] ${known}`);
  //       return L_Out.True;
  //     }
  //   } else {
  //     if (
  //       known.isT === toCheck.isT &&
  //       known.vars.every((e, i) => {
  //         if (e.startsWith("\\") && toCheck.vars[i].startsWith("\\")) {
  //           return checkCompositeLiterally(env, toCheck.vars[i], e);
  //         } else if (!e.startsWith("\\") && !e.startsWith("\\")) {
  //           return e === toCheck.vars[i];
  //         }
  //       })
  //     ) {
  //       env.newMessage(`[checked by] ${toCheck.optSymbol}(${known})`);
  //       return L_Out.True;
  //     } else continue;
  //   }
  // }
  // //* use checkVars from if to check *//
  // if (useCheckVarsFromIf) {
  //   for (let i = 0; i < toCheckVarsFromIf.length; i++) {
  //     // use toCheckVarsFromIf layer by layer
  //     const curToCheckVars = toCheckVarsFromIf.slice(i);
  //     const newOpt = new OptNode(
  //       toCheck.optSymbol,
  //       toCheck.vars,
  //       toCheck.isT,
  //       curToCheckVars
  //     );
  //     const out = checkOpt(env, newOpt, false);
  //     if (out === L_Out.True) {
  //       return L_Out.True;
  //     }
  //     // use toCheckVarsFromIf as if it's single layer
  //     const anotherCurCheckVars: string[] = [];
  //     curToCheckVars.map((e) => anotherCurCheckVars.push(...e));
  //     const anotherOpt = new OptNode(
  //       toCheck.optSymbol,
  //       toCheck.vars,
  //       toCheck.isT,
  //       [anotherCurCheckVars]
  //     );
  //     if (checkOpt(env, anotherOpt, false) === L_Out.True) return L_Out.True;
  //   }
  // }
  // return L_Out.Unknown;
  //*
}

// check whether a variable in fact.vars is free or fixed at check time instead of run time.
export function checkOptLiterally(env: L_Env, toCheck: OptNode): L_Out {
  return L_Out.Error;
  //*
  // if (isToCheckBuiltin(toCheck)) {
  //   env.newMessage(`checked by builtins.`);
  //   switch (toCheck.optSymbol.name) {
  //     case "is_property":
  //       return isPropertyBuiltinCheck(env, toCheck);
  //     // case ExistKeyword:
  //     //   return existBuiltinCheck(env, toCheck);
  //     default:
  //       return L_Out.Error;
  //   }
  // }
  // if (toCheck.vars.length !== env.getDef(toCheck.optSymbol.name)?.vars.length) {
  //   return L_Out.Unknown;
  // }
  // const facts = env.getKnownFactsFromCurEnv(toCheck);
  // // const facts: StoredFact[] | null = L_Memory.getStoredFacts(env, toCheck);
  // if (facts === undefined) {
  //   env.newMessage(`check Error: ${toCheck.optSymbol} not declared.`);
  //   return L_Out.Error;
  // }
  // for (const fact of facts as StoredFact[]) {
  //   const frees = fact.getAllFreeVars();
  //   if (
  //     //! UPDATE: NOT SURE fact.isT === toCheck.isT should be included.
  //     // fact.isT === toCheck.isT &&
  //     fact.isNoReq() &&
  //     // toCheck.vars.length === fact.vars.length &&
  //     toCheck.vars.every(
  //       (v, i) =>
  //         frees.includes(fact.vars[i]) || //! DO NOT KNOW WHY free.includes is necessary. But i choose to retain it to avoid breakdown.
  //         (!v.startsWith("\\") && v === fact.vars[i]) || //* normal checking
  //         (v.startsWith("\\") &&
  //           fact.vars[i].startsWith("\\") &&
  //           checkCompositeLiterally(env, v, fact.vars[i])) //* check symbol that start with "\\"
  //     )
  //   ) {
  //     return L_Out.True;
  //   } else {
  //     continue;
  //   }
  // }
  // return L_Out.True;
  //*
}

export function checkOptInHave(env: L_Env, opt: OptNode): L_Out {
  env;
  opt;
  return L_Out.Unknown;
}

function checkOr(env: L_Env, toCheck: OrNode): L_Out {
  try {
    if (toCheck.facts.length === 0) return L_Out.True;

    if (toCheck.facts.length === 1) {
      return check(env, toCheck.facts[0]);
    }

    for (let i = 0; i < toCheck.facts.length; i++) {
      let valid = false;
      const newEnv = new L_Env(env);
      for (let j = 0; j < toCheck.facts.length; j++) {
        if (j === i) continue;
        L_Memory.store(
          newEnv,
          toCheck.facts[j].copyWithoutIsT(!toCheck.facts[j].isT),
          [],
          true
        );
      }

      const out = check(newEnv, toCheck.facts[i]);
      if (out === L_Out.True) {
        valid = true;
      }

      if (valid) return L_Out.True;
    }

    return L_Out.Unknown;
  } catch {
    return L_Out.Error;
  }
}

export function checkOptCond(env: L_Env, toCheck: OptNode): L_Out {
  return L_Out.Error;

  //*
  // const def = env.getDef(toCheck.optSymbol);
  // if (def === undefined) {
  //   return env.errMesReturnL_Out(`operator ${toCheck} not declared.`);
  // }
  // if (toCheck.vars.length !== def.vars.length) {
  //   return lstLengthNotEql(env, toCheck.vars, def.vars);
  // }
  // const map = new Map<string, string>();
  // for (const [i, v] of toCheck.vars.entries()) {
  //   map.set(def.vars[i], v);
  // }
  // for (const condition of def?.cond) {
  //   const fixed = condition.useMapToCopy(env, map);
  //   const out = check(env, fixed);
  //   if (out !== L_Out.True) {
  //     env.newMessage(`[Unknown] ${fixed}`);
  //     return L_Out.Unknown;
  //   }
  // }
  // return L_Out.True;
  //*
}

// Steps
// 1. check the symbol name of compositeSymbol and storedFact after "\\" are the same
// 2. check storedFact's requirements in [] are satisfied.
export function checkCompositeLiterally(
  env: L_Env,
  givenStr: string,
  storedStr: string
): boolean {
  return false;
  //*
  // try {
  //   const storedComposite = compositeSymbolParse(
  //     env,
  //     storedStr.split(" ")
  //   ) as CompositeSymbol;
  //   const givenComposite = compositeSymbolParse(
  //     env,
  //     givenStr.split(" ")
  //   ) as CompositeSymbol;
  //   if (storedComposite.name !== givenComposite.name) {
  //     return false;
  //   }
  //   const map = new Map<string, string>();
  //   for (const [i, v] of storedComposite.vars.entries()) {
  //     map.set(v, givenComposite.vars[i]);
  //   }
  //   for (const [i, v] of storedComposite.vars.entries()) {
  //     if (v.startsWith("#")) {
  //       const toChecks = env.getHashVarFacts(v);
  //       if (toChecks === undefined) {
  //         return env.errMesReturnBoolean(`hashed variable ${v} not declared`);
  //       }
  //       for (const r of toChecks) {
  //         const toCheck = r.useMapToCopy(env, map);
  //         const out = check(env, toCheck);
  //         if (out !== L_Out.True) return false;
  //       }
  //     } else {
  //       // check var literally, other wise in(b, \\singleton{b}) leads to in(n, \\singleton{b})
  //       if (map.get(v) === v) continue;
  //       else {
  //         return false;
  //       }
  //     }
  //   }
  //   for (const r of storedComposite.req) {
  //     const toCheck = r.useMapToCopy(env, map);
  //     const out = check(env, toCheck);
  //     if (out !== L_Out.True) return false;
  //   }
  //   return true;
  // } catch {
  //   env.newMessage(`Failed to check ${givenStr}`);
  //   throw Error();
  // }
  //*
}
