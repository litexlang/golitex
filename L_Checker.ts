import { ByNode, FactNode, IfThenNode, KnowNode, OptNode } from "./ast";
import { L_Env } from "./L_Env";
import { L_Executor, RType } from "./L_Executor";
import { L_FactStorage, StoredFact } from "./L_FactStorage";

export namespace L_Checker {
  export function check(
    env: L_Env,
    toCheck: FactNode,
    bys: OptNode[] = []
  ): RType {
    if (toCheck instanceof OptNode) {
      return checkOpt(env, toCheck, bys);
    } else if (toCheck instanceof IfThenNode) {
      return checkIfThen(env, toCheck, bys);
    } else if (toCheck instanceof ByNode) {
      return checkBy(env, toCheck, bys);
    }

    return RType.Unknown;
  }

  export function checkIfThen(
    env: L_Env,
    toCheck: IfThenNode,
    bys: OptNode[]
  ): RType {
    let out: RType = RType.True;
    const newEnv = new L_Env(env);

    for (const e of toCheck.vars) {
      const ok = newEnv.safeNewVar(e);
      if (!ok) return RType.Error;
    }
    // toCheck.vars.forEach((e) => newEnv.newVar(e, e));

    for (const f of toCheck.req) L_FactStorage.store(newEnv, f, []);
    for (const onlyIf of toCheck.onlyIfs) {
      out = check(newEnv, onlyIf, bys);
      if (out !== RType.True) return out;
      else {
        // checked facts in then are used as stored fact.
        L_FactStorage.store(newEnv, toCheck, []);
      }
    }
    return RType.True;
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
    bys: OptNode[]
  ): RType {
    const storedFacts: StoredFact[] | null = L_FactStorage.getStoredFacts(
      env,
      toCheck
    );
    if (storedFacts === null) {
      env.newMessage(`check error: ${toCheck.fullName} not declared.`);
      return RType.Error;
    }

    for (const storedFact of storedFacts) {
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

      // for (let i = 0; i < toCheck.vars.length; i++) {
      //   if (freeVarsOfAllLevels.includes(storedFact.vars[i])) {
      //     const alreadyDeclared = map.get(storedFact.vars[i]);
      //     if (alreadyDeclared && alreadyDeclared !== toCheck.vars[i]) {
      //       env.newMessage(
      //         `${storedFact.vars[i]} is signed with 2 different symbols ${alreadyDeclared}, ${toCheck.vars[i]}`
      //       );
      //       return RType.Error;
      //     }

      //     map.set(storedFact.vars[i], toCheck.vars[i]);
      //   }
      // }

      for (const currentLevelReq of storedFact.req) {
        // this is necessary because 1. I SIMPLY NEED A NEATER STORAGE SYSTEM THAT ALIGNS WITH THE HIERARCHY OF IF-THENs THE FACT IS STORED. 2. store checked req as future stored facts. 3. If some vars of the req is free, then the req is not checked, it is stored as a fact.
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
                L_FactStorage.store(newEnv, toCheck, []);
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
          } else if (req instanceof IfThenNode) {
            const out = checkOpt(newEnv, toCheck, bys);
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
    const facts: StoredFact[] | null = L_FactStorage.getStoredFacts(
      env,
      toCheck
    );

    if (facts === null) {
      env.newMessage(`check Error: ${toCheck.fullName} not declared.`);
      return RType.Error;
    }

    for (const fact of facts) {
      const frees = fact.getAllFreeVars();
      if (
        fact.isNoReq() &&
        toCheck.vars.every(
          (v, i) => frees.includes(fact.vars[i]) || v === fact.vars[i]
        )
      )
        return RType.True;
    }

    return RType.Unknown;
  }

  export function checkOptInHave(env: L_Env, opt: OptNode): RType {
    return RType.Unknown;
  }

  function checkBy(env: L_Env, toCheck: ByNode, bys: OptNode[]): RType {
    try {
      let out = RType.Error;
      for (const by of toCheck.bys) {
        out = checkOpt(env, by, []);
        if (out !== RType.True) {
          if (out === RType.Error) {
            env.newMessage(`Error to check ${by}`);
          }
          return out;
        }
      }

      for (const fact of toCheck.facts) {
        out = check(env, fact, toCheck.bys);

        if (out !== RType.True) {
          if (out === RType.Error) {
            env.newMessage(`Error to check ${fact}`);
          }
          return out;
        }
      }

      return RType.True;
    } catch (error) {
      env.newMessage("check by");
      return RType.Error;
    }
  }
}
