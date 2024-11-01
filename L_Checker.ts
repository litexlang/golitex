import { FactNode, IfThenNode, KnowNode, OptNode } from "./ast";
import { L_Env } from "./L_Env";
import { L_Executor, RType } from "./L_Executor";
import { L_FactStorage, StoredFact } from "./L_FactStorage";

export namespace L_Checker {
  export function check(env: L_Env, toCheck: FactNode): RType {
    if (toCheck instanceof OptNode) {
      return checkOpt(env, toCheck);
    } else if (toCheck instanceof IfThenNode) {
      return checkIfThen(env, toCheck);
    }

    return RType.Unknown;
  }

  // MAIN FUNCTION OF THE WHOLE PROJECT
  export function checkOpt(env: L_Env, toCheck: OptNode): RType {
    const storedFacts: StoredFact[] | undefined = env.getStoredFacts(toCheck);
    if (storedFacts === undefined) return RType.Unknown;

    for (const storedFact of storedFacts) {
      if (toCheck.vars.length !== storedFact.vars.length) {
        env.newMessage(
          `Invalid number of arguments: need ${storedFact.vars.length}, get ${toCheck.vars.length}`
        );
        return RType.Error;
      }

      let unknown = false;
      if (storedFact.isNoReq()) {
        if (checkOptLiterally(env, toCheck)) {
          return RType.True;
        } else {
          continue;
        }
      }

      const map = new Map<String, string>();
      for (let i = 0; i < toCheck.vars.length; i++) {
        // check whether a variable is already declared at current level, for example, `if x,x | ...` is not allowed
        if (map.get(storedFact.vars[i])) {
          env.newMessage(`Double declaration of ${storedFact.vars[i]}`);
          return RType.Error;
        }

        map.set(storedFact.vars[i], toCheck.vars[i]);
      }

      // try to use the current storedFact ot prove toCheck

      // const frees = storedFact.getAllFreeVars();

      // satisfy all requirements

      let newEnv = new L_Env(env);

      for (const currentLevelReq of storedFact.req) {
        // try to operate(store facts, introduce new variables) under current layer of stored if-then
        for (const e of currentLevelReq.vars) {
          const ok = newEnv.safeNewVar(e, map.get(e) as string);
          if (!ok) return RType.Error;
        }
        // currentLevelReq.vars.forEach((e) =>
        //   newEnv.newVar(e, map.get(e) as string)
        // );

        // satisfy literal restrictions
        for (const req of currentLevelReq.req) {
          if (req instanceof OptNode) {
            const checkReq = new OptNode(
              req.fullName,
              req.vars.map((e) => newEnv.getVar(e)) as string[]
            );
            const out = checkOptLiterally(newEnv, checkReq);
            if (out) continue;
            else {
              unknown = true;
              break;
            }
          } else if (req instanceof IfThenNode) {
            const out = checkOpt(newEnv, toCheck);
            if (out === RType.True) continue;
            else if (out === RType.Unknown || out === RType.Error) {
              unknown = true;
              break;
            }
          }
        }

        if (unknown) break;
        else newEnv = new L_Env(newEnv);
      }
      if (unknown) continue;
      return RType.True;
    }

    return RType.Unknown;
  }

  // check whether a variable in fact.vars is free or fixed at check time instead of run time.
  export function checkOptLiterally(env: L_Env, toCheck: OptNode): Boolean {
    const facts: StoredFact[] | undefined = env.getStoredFacts(toCheck);

    if (facts === undefined) return false;

    for (const fact of facts) {
      const frees = fact.getAllFreeVars();
      if (
        fact.isNoReq() &&
        toCheck.vars.every(
          (v, i) => frees.includes(fact.vars[i]) || v === fact.vars[i]
        )
      )
        return true;
    }

    return false;
  }

  export function checkIfThen(env: L_Env, toCheck: IfThenNode): RType {
    let out: RType = RType.True;
    const newEnv = new L_Env(env);

    for (const e of toCheck.vars) {
      const ok = newEnv.safeNewVar(e, e);
      if (!ok) return RType.Error;
    }
    // toCheck.vars.forEach((e) => newEnv.newVar(e, e));

    for (const f of toCheck.req) L_FactStorage.store(newEnv, f, []);
    for (const onlyIf of toCheck.onlyIfs) {
      out = check(newEnv, onlyIf);
      if (out !== RType.True) return out;
      else {
        // checked facts in then are used as stored fact.
        L_FactStorage.store(newEnv, toCheck, []);
      }
    }
    return RType.True;
  }

  export function checkOptInHave(env: L_Env, opt: OptNode): RType {
    return RType.Unknown;
  }
}
