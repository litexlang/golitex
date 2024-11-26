import { ToCheckNode, OptNode, OrNode, IfNode } from "./L_Nodes.ts";
import { L_Env } from "./L_Env.ts";
import { RType } from "./L_Executor.ts";
import { StoredFact } from "./L_Memory.ts";
import * as L_Memory from "./L_Memory.ts";
import { L_Builtins } from "./L_Builtins.ts";

export function check(env: L_Env, toCheck: ToCheckNode): RType {
  if (toCheck instanceof OptNode) {
    let out = checkOpt(env, toCheck);
    if (out === RType.Unknown) {
      out = checkOpt(env, toCheck.copyWithoutIsT(!toCheck.isT));
      if (out === RType.True) {
        return RType.False;
      }
    }
    return out;
  } else if (toCheck instanceof IfNode) {
    return checkIfThen(env, toCheck);
  } else if (toCheck instanceof OrNode) {
    return checkOr(env, toCheck);
  }

  return RType.Unknown;
}

export function checkIfThen(env: L_Env, toCheck: IfNode): RType {
  if (toCheck.isT === false) {
    env.newMessage(`not-if-then fact ${toCheck} can not be checked directly.`);
    return RType.Error;
  }

  const out = openEnvAndCheck(env, toCheck);
  return out;

  function openEnvAndCheck(oldEnv: L_Env, toCheck: IfNode): RType {
    const newEnv = new L_Env(oldEnv);

    for (const e of toCheck.vars) {
      const ok = newEnv.newVar(e);
      if (!ok) return RType.Error;
    }

    for (const f of toCheck.req) L_Memory.store(newEnv, f, [], true);
    for (const onlyIf of toCheck.onlyIfs) {
      const out = check(newEnv, onlyIf);
      if (out !== RType.True) return out;
      else {
        // checked facts in then are used as stored fact.
        L_Memory.store(newEnv, toCheck, [], true);
      }
    }

    return RType.True;
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
export function checkOpt(env: L_Env, toCheck: OptNode): RType {
  const builtins = L_Builtins.get(toCheck.name);
  if (builtins !== undefined) {
    return builtins(env, toCheck);
  }

  // const storedFacts: StoredFact[] | null = L_Memory.getStoredFacts(
  //   env,
  //   toCheck
  // );
  // if (storedFacts === null) {
  //   env.newMessage(`check error: ${toCheck.name} not declared.`);
  //   return RType.Error;
  // }

  // const out = useStoredFactsToCheckOpt(env, storedFacts, toCheck);
  // if (out === RType.True) return RType.True;

  if (toCheck.checkVars === undefined) {
    toCheck.checkVars = [];
  }

  const knowns = L_Memory.getStoredFacts(env, toCheck);
  if (knowns === undefined) return RType.Unknown;

  for (const known of knowns as StoredFact[]) {
    if (known.req.length > 0) {
      const map = new Map<string, string>();
      if (known.isT !== toCheck.isT) continue;

      for (let i = 0; i < toCheck.checkVars.length; i++) {
        for (let j = 0; j < toCheck.checkVars[i].length; j++) {
          map.set(known.req[i].vars[j], toCheck.checkVars[i][j]);
        }
      }

      const fixedKnown = known.fixStoredFact(map);

      let out = RType.True;

      for (const r of fixedKnown.req as L_Memory.StoredReq[]) {
        for (const toCheck of r.req as ToCheckNode[]) {
          if (toCheck instanceof OptNode) {
            out = checkOptLiterally(env, toCheck);
            if (out !== RType.True) break;
          } else {
            //! NEED TO IMPLEMENT HOW TO CHECK If-Then Literally?
            out = checkIfThen(env, toCheck as IfNode);
            if (out !== RType.True) break;
          }
        }
        if (out === RType.Unknown) break;
      }

      if (out === RType.True) return RType.True;
    } else {
      if (known.vars.every((e, i) => e === toCheck.vars[i])) return RType.True;
      else continue;
    }
  }

  return RType.Unknown;
}

// check whether a variable in fact.vars is free or fixed at check time instead of run time.
function checkOptLiterally(env: L_Env, toCheck: OptNode): RType {
  if (toCheck.vars.length !== env.getDeclaredFact(toCheck.name)?.vars.length) {
    return RType.Unknown;
  }

  const builtins = L_Builtins.get(toCheck.name);
  if (builtins !== undefined) {
    return builtins(env, toCheck);
  }

  const facts = env.getKnownFactsFromCurEnv(toCheck);
  // const facts: StoredFact[] | null = L_Memory.getStoredFacts(env, toCheck);

  if (facts === undefined) {
    env.newMessage(`check Error: ${toCheck.name} not declared.`);
    return RType.Error;
  }

  for (const fact of facts) {
    const frees = fact.getAllFreeVars();
    if (
      //! UPDATE: NOT SURE fact.isT === toCheck.isT should be included.
      // fact.isT === toCheck.isT &&
      fact.isNoReq() &&
      // toCheck.vars.length === fact.vars.length &&
      toCheck.vars.every(
        (v, i) => frees.includes(fact.vars[i]) || v === fact.vars[i]
      )
    )
      return RType.True;
  }

  return RType.Unknown;
}

export function checkOptInHave(env: L_Env, opt: OptNode): RType {
  env;
  opt;
  return RType.Unknown;
}

function checkOr(env: L_Env, toCheck: OrNode): RType {
  try {
    if (toCheck.facts.length === 0) return RType.True;

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
      if (out === RType.True) {
        valid = true;
      }

      if (valid) return RType.True;
    }

    return RType.Unknown;
  } catch {
    return RType.Error;
  }
}

// function useStoredFactsToCheckOpt(
//   env: L_Env,
//   storedFacts: StoredFact[],
//   toCheck: OptNode
// ): RType {
//   for (const storedFact of storedFacts) {
//     if (storedFact.isT !== toCheck.isT) continue;

//     if (toCheck.vars.length !== storedFact.vars.length) {
//       env.newMessage(
//         `Invalid number of arguments: ${toCheck.name} need ${storedFact.vars.length}, get ${toCheck.vars.length}`
//       );
//       return RType.Error;
//     }

//     if (storedFact.isNoReq()) {
//       const out = checkOptLiterally(env, toCheck);
//       if (out === RType.True) {
//         return RType.True;
//       } else if (out === RType.Error) {
//         return RType.Error;
//       } else {
//         continue;
//       }
//     }

//     let unknown = false;
//     const map = new Map<string, string>();

//     //! I GUESS THE FOLLOWING LOGIC SHOULD BE REPLACED BY COPY_WITH_MAP
//     const freeVarsOfAllLevels = storedFact.getAllFreeVars();
//     // toCheck.vars.length === storedFact.vars.length
//     for (let i = 0; i < storedFact.vars.length; i++) {
//       if (freeVarsOfAllLevels.includes(storedFact.vars[i])) {
//         const alreadyDeclared = map.get(storedFact.vars[i]);
//         if (alreadyDeclared && alreadyDeclared !== toCheck.vars[i]) {
//           env.newMessage(
//             `${storedFact.vars[i]} is signed with 2 different symbols ${alreadyDeclared}, ${toCheck.vars[i]}`
//           );
//           return RType.Error;
//         }

//         map.set(storedFact.vars[i], toCheck.vars[i]);
//       }
//     }

//     for (const currentLevelReq of storedFact.req) {
//       let newEnv = new L_Env(env);

//       for (const req of currentLevelReq.req) {
//         if (req instanceof OptNode) {
//           let everyVarInThisReqIsFixed = true;
//           const fixedVars: string[] = [];
//           for (const v of req.vars) {
//             const fixed = map.get(v);
//             if (fixed === undefined) {
//               everyVarInThisReqIsFixed = false;
//               fixedVars.push(v);
//               break;
//             } else {
//               fixedVars.push(fixed);
//             }
//           }

//           // const fixedVars = req.vars.map((e) => map.get(e)) as string[];
//           if (everyVarInThisReqIsFixed) {
//             const toCheck = new OptNode(
//               req.name,
//               fixedVars,
//               req.isT, //! Unknown whether should be true or req.isT
//               undefined
//             );
//             const out = checkOptLiterally(newEnv, toCheck);
//             if (out === RType.True) {
//               // store checked req as future stored facts.
//               L_Memory.store(newEnv, toCheck, [], true);
//               continue;
//             } else if (out === RType.Error) {
//               newEnv.getMessages().forEach((e) => newEnv.newMessage(e));
//               return RType.Error;
//             } else {
//               unknown = true;
//               break;
//             }
//           } else {
//             //! WARNING: UNKNOWN SHOULD BE THROWN HERE INSTEAD OF STORING NEW FACTS
//             // unknown = true;
//             // break;
//             // const toStore = new OptNode(req.name, fixedVars);
//             // L_Memory.store(newEnv, toStore, []);
//             const toCheck = new OptNode(
//               req.name,
//               fixedVars,
//               req.isT, //! Unknown whether should be true or req.isT
//               undefined
//             );
//             const out = checkOptLiterally(newEnv, toCheck);
//             if (out === RType.True) {
//               // store checked req as future stored facts.
//               L_Memory.store(newEnv, toCheck, [], true);
//               continue;
//             } else if (out === RType.Error) {
//               newEnv.getMessages().forEach((e) => newEnv.newMessage(e));
//               return RType.Error;
//             } else {
//               unknown = true;
//               break;
//             }
//           }
//         }
//         //! WARNING: I GUESS IF-THEN HERE IS BUGGY
//         else if (req instanceof IfNode) {
//           const newReq = req.useMapToCopy(map) as IfNode;

//           const out = checkIfThen(newEnv, newReq); // ? UNTESTED
//           // const out = checkOpt(newEnv, toCheck);
//           if (out === RType.True) continue;
//           else if (out === RType.Error) {
//             newEnv.getMessages().forEach((e) => env.newMessage(e));
//             return RType.Error;
//           } else {
//             unknown = true;
//             break;
//           }
//         }
//         // OrNode
//         else if (req instanceof OrNode) {
//           const newReq: ToCheckNode[] = [];
//           for (const f of req.facts) {
//             newReq.push(f.useMapToCopy(map));
//           }
//           const out = checkOr(newEnv, new OrNode(newReq, req.isT, undefined));
//           if (out === RType.True) continue;
//           else if (out === RType.Error) {
//             newEnv.getMessages().forEach((e) => env.newMessage(e));
//             return RType.Error;
//           } else {
//             unknown = true;
//             break;
//           }
//         }
//         //  else if (req instanceof ExistNode) {
//         //   const newReq: ExistNode = req.useMapToCopy(map) as ExistNode;

//         //   const out = checkExistInLogicReq(newEnv, newReq);
//         //   if (out === RType.True) continue;
//         //   else if (out === RType.Error) {
//         //     newEnv.getMessages().forEach((e) => env.newMessage(e));
//         //     return RType.Error;
//         //   } else {
//         //     unknown = true;
//         //     break;
//         //   }
//         // }
//       }

//       if (unknown) break;
//       newEnv = new L_Env(newEnv);
//     }

//     if (unknown) continue;
//     return RType.True;
//   }

//   return RType.Error;
// }
