import { ByNode, FactNode, IfIffNode, OptNode, OrNode } from "./ast.ts";
import { L_Env } from "./L_Env.ts";
import { RType } from "./L_Executor.ts";
import { StoredFact } from "./L_FactStorage.ts";
import * as L_FactStorage from "./L_FactStorage.ts";

export function check(env: L_Env, toCheck: FactNode): RType {
  if (toCheck instanceof OptNode) {
    const out = checkOpt(env, toCheck);
    return out;
  } else if (toCheck instanceof IfIffNode) {
    return checkIfThen(env, toCheck);
  } else if (toCheck instanceof OrNode) {
    return checkOr(env, toCheck);
  }

  return RType.Unknown;
}

export function checkIfThen(env: L_Env, toCheck: IfIffNode): RType {
  let out = openEnvAndCheck(env, toCheck);
  if (out !== RType.True) return out;
  if (toCheck.isIff) {
    const newToCheck = new IfIffNode(
      toCheck.vars,
      toCheck.onlyIfs,
      toCheck.req,
      toCheck.isT,
      toCheck.byName,
      toCheck.isIff
    );
    out = openEnvAndCheck(env, newToCheck);
  }

  return out;

  function openEnvAndCheck(oldEnv: L_Env, toCheck: IfIffNode): RType {
    const newEnv = new L_Env(oldEnv);

    for (const e of toCheck.vars) {
      const ok = newEnv.safeNewVar(e);
      if (!ok) return RType.Error;
    }

    for (const f of toCheck.req) L_FactStorage.store(newEnv, f, [], true);
    for (const onlyIf of toCheck.onlyIfs) {
      const out = check(newEnv, onlyIf);
      if (out !== RType.True) return out;
      else {
        // checked facts in then are used as stored fact.
        L_FactStorage.store(newEnv, toCheck, [], true);
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
  const storedFacts: StoredFact[] | null = L_FactStorage.getStoredFacts(
    env,
    toCheck
  );
  if (storedFacts === null) {
    env.newMessage(`check error: ${toCheck.fullName} not declared.`);
    return RType.Error;
  }

  for (const storedFact of storedFacts) {
    if (storedFact.isT !== toCheck.isT) continue;

    if (toCheck.vars.length !== storedFact.vars.length) {
      env.newMessage(
        `Invalid number of arguments: need ${storedFact.vars.length}, get ${toCheck.vars.length}`
      );
      return RType.Error;
    }

    if (storedFact.isNoReq()) {
      const out = checkOptLiterally(env, toCheck);
      if (out === RType.True) {
        return RType.True;
      } else if (out === RType.Error) {
        return RType.Error;
      } else {
        continue;
      }
    }

    let unknown = false;
    const map = new Map<string, string>();

    //! I GUESS THE FOLLOWING LOGIC SHOULD BE REPLACED BY COPY_WITH_MAP
    const freeVarsOfAllLevels = storedFact.getAllFreeVars();
    // toCheck.vars.length === storedFact.vars.length
    for (let i = 0; i < storedFact.vars.length; i++) {
      if (freeVarsOfAllLevels.includes(storedFact.vars[i])) {
        const alreadyDeclared = map.get(storedFact.vars[i]);
        if (alreadyDeclared && alreadyDeclared !== toCheck.vars[i]) {
          env.newMessage(
            `${storedFact.vars[i]} is signed with 2 different symbols ${alreadyDeclared}, ${toCheck.vars[i]}`
          );
          return RType.Error;
        }

        map.set(storedFact.vars[i], toCheck.vars[i]);
      }
    }

    for (const currentLevelReq of storedFact.req) {
      let newEnv = new L_Env(env);

      for (const req of currentLevelReq.req) {
        if (req instanceof OptNode) {
          let everyVarInThisReqIsFixed = true;
          const fixedVars: string[] = [];
          for (const v of req.vars) {
            const fixed = map.get(v);
            if (fixed === undefined) {
              everyVarInThisReqIsFixed = false;
              break;
              // fixedVars.push(v);
            } else {
              fixedVars.push(fixed);
            }
          }

          // const fixedVars = req.vars.map((e) => map.get(e)) as string[];
          if (everyVarInThisReqIsFixed) {
            const toCheck = new OptNode(req.fullName, fixedVars);
            const out = checkOptLiterally(newEnv, toCheck);
            if (out === RType.True) {
              // store checked req as future stored facts.
              L_FactStorage.store(newEnv, toCheck, [], true);
              continue;
            } else if (out === RType.Error) {
              newEnv.getMessages().forEach((e) => newEnv.newMessage(e));
              return RType.Error;
            } else {
              unknown = true;
              break;
            }
          } else {
            //! WARNING: UNKNOWN SHOULD BE THROWN HERE INSTEAD OF STORING NEW FACTS
            unknown = true;
            break;
            // const toStore = new OptNode(req.fullName, fixedVars);
            // L_FactStorage.store(newEnv, toStore, []);
          }
        }
        //! WARNING: I GUESS IF-THEN HERE IS BUGGY
        else if (req instanceof IfIffNode) {
          const newReq = req.useMapToCopy(map);

          const out = checkIfThen(newEnv, newReq); // ? UNTESTED
          // const out = checkOpt(newEnv, toCheck);
          if (out === RType.True) continue;
          else if (out === RType.Error) {
            newEnv.getMessages().forEach((e) => env.newMessage(e));
            return RType.Error;
          } else {
            unknown = true;
            break;
          }
        }
        // OrNode
        else if (req instanceof OrNode) {
          const newReq: FactNode[] = [];
          for (const f of req.facts) {
            newReq.push(f.useMapToCopy(map));
          }
          const out = checkOr(newEnv, new OrNode(newReq, req.isT));
          if (out === RType.True) continue;
          else if (out === RType.Error) {
            newEnv.getMessages().forEach((e) => env.newMessage(e));
            return RType.Error;
          } else {
            unknown = true;
            break;
          }
        }
      }

      if (unknown) break;
      newEnv = new L_Env(newEnv);
    }

    if (unknown) continue;
    return RType.True;
  }

  return RType.Unknown;
}

// check whether a variable in fact.vars is free or fixed at check time instead of run time.
function checkOptLiterally(env: L_Env, toCheck: OptNode): RType {
  const facts: StoredFact[] | null = L_FactStorage.getStoredFacts(env, toCheck);

  if (facts === null) {
    env.newMessage(`check Error: ${toCheck.fullName} not declared.`);
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

// TODO:
export function checkBy(env: L_Env, byNode: ByNode): RType {
  const storedFact: undefined | StoredFact = env.getBy(byNode.byName);
  if (storedFact == undefined) {
    env.newMessage(`${byNode.byName} not declared.`);
    return RType.Error;
  }

  const allFreeVars = storedFact.getAllFreeVars();
  if (byNode.vars.length !== allFreeVars.length) {
    env.newMessage(
      `${byNode.byName} expect ${allFreeVars.length} variables, got ${byNode.vars.length}`
    );
    return RType.Error;
  }

  const map = new Map<string, string>();
  for (const indexValuePair of allFreeVars.entries()) {
    map.set(allFreeVars[indexValuePair[0]], byNode.vars[indexValuePair[0]]);
  }

  let unknown = false;
  let newEnv = new L_Env(env);
  for (const currentLevelReq of storedFact.req) {
    // this is necessary because 1. I SIMPLY NEED A NEATER STORAGE SYSTEM THAT ALIGNS WITH THE HIERARCHY OF IF-THENs THE FACT IS STORED. 2. store checked req as future stored facts. 3. If some vars of the req is free, then the req is not checked, it is stored as a fact.

    for (const req of currentLevelReq.req) {
      if (req instanceof OptNode) {
        let everyVarInThisReqIsFixed = true;
        const fixedVars: string[] = [];
        for (const v of req.vars) {
          const fixed = map.get(v);
          if (fixed === undefined) {
            everyVarInThisReqIsFixed = false;
            break;
            // fixedVars.push(v);
          } else {
            fixedVars.push(fixed);
          }
        }

        // const fixedVars = req.vars.map((e) => map.get(e)) as string[];
        if (everyVarInThisReqIsFixed) {
          const toCheck = new OptNode(req.fullName, fixedVars);
          const out = checkOptLiterally(newEnv, toCheck);
          if (out === RType.True) {
            // store checked req as future stored facts.
            L_FactStorage.store(newEnv, toCheck, [], true);
            continue;
          } else if (out === RType.Error) {
            newEnv.getMessages().forEach((e) => newEnv.newMessage(e));
            return RType.Error;
          } else {
            unknown = true;
            break;
          }
        } else {
          //! WARNING: UNKNOWN SHOULD BE THROWN HERE INSTEAD OF STORING NEW FACTS
          unknown = true;
          break;
          // const toStore = new OptNode(req.fullName, fixedVars);
          // L_FactStorage.store(newEnv, toStore, []);
        }
      } else if (req instanceof IfIffNode) {
        const out = checkIfThen(newEnv, req);
        if (out === RType.True) continue;
        else if (out === RType.Error) {
          newEnv.getMessages().forEach((e) => env.newMessage(e));
          return RType.Error;
        } else {
          unknown = true;
          break;
        }
      }
    }

    if (unknown) break;
    newEnv = new L_Env(newEnv);
  }

  if (unknown) return RType.Unknown;

  return RType.True;
}

function checkOr(env: L_Env, toCheck: OrNode): RType {
  try {
    for (let i = 0; i < toCheck.facts.length; i++) {
      let valid = false;
      const newEnv = new L_Env(env);
      for (let j = 0; j < toCheck.facts.length; j++) {
        if (j === i) continue;
        L_FactStorage.store(
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
