import { FactNode, IfThenNode, KnowNode, OptNode } from "./ast";
import { L_Env } from "./L_Env";
import { L_Executor, RType } from "./L_Executor";
import { StoredFact } from "./L_Storage";

export namespace checker {
  export function L_Check(env: L_Env, toCheck: FactNode): RType {
    if (toCheck instanceof OptNode) {
      return L_CheckOpt(env, toCheck);
    } else if (toCheck instanceof IfThenNode) {
      return L_CheckIfThen(env, toCheck);
    }

    return RType.Unknown;
  }

  // MAIN FUNCTION OF THE WHOLE PROJECT
  export function L_CheckOpt(env: L_Env, toCheck: OptNode): RType {
    const storedFacts: StoredFact[] | undefined =
      env.getStoredFactsFromAllLevels(toCheck.fullName);
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
        if (L_CheckOptLiterally(env, toCheck)) {
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
        currentLevelReq.vars.forEach((e) =>
          newEnv.newVar(e, map.get(e) as string)
        );

        // satisfy literal restrictions
        for (const req of currentLevelReq.req) {
          if (req instanceof OptNode) {
            const checkReq = new OptNode(
              req.fullName,
              req.vars.map((e) => newEnv.getVar(e)) as string[]
            );
            const out = L_CheckOptLiterally(newEnv, checkReq);
            if (out) continue;
            else {
              unknown = true;
              break;
            }
          } else if (req instanceof IfThenNode) {
            const out = L_CheckOpt(newEnv, toCheck);
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
  export function L_CheckOptLiterally(env: L_Env, toCheck: OptNode): Boolean {
    const facts: StoredFact[] | undefined = env.getStoredFactsFromAllLevels(
      toCheck.fullName
    );

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

  export function L_CheckIfThen(env: L_Env, toCheck: IfThenNode): RType {
    let out: RType = RType.True;
    const newEnv = new L_Env(env);
    toCheck.vars.forEach((e) => newEnv.newVar(e, e));
    L_Executor.knowExec(newEnv, new KnowNode(toCheck.req));
    for (const onlyIf of toCheck.onlyIfs) {
      out = L_Check(newEnv, onlyIf);
      if (out !== RType.True) return out;
    }
    return RType.True;
  }

  export function checkOptInHave(env: L_Env, opt: OptNode): RType {
    return RType.Unknown;
  }
}
