import { IfNode, OptNode, OrNode, ToCheckNode } from "./L_Nodes.ts";
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

  if (toCheck.checkVars === undefined) {
    toCheck.checkVars = [];
  }

  const knowns = L_Memory.getStoredFacts(env, toCheck);
  if (knowns === undefined) return RType.Unknown;

  for (const known of knowns as StoredFact[]) {
    if (known.req.length > 0) {
      const map = new Map<string, string>();
      if (known.isT !== toCheck.isT) continue;

      if (toCheck.checkVars.length > 0) {
        for (let i = 0; i < toCheck.checkVars.length; i++) {
          for (let j = 0; j < toCheck.checkVars[i].length; j++) {
            map.set(known.req[i].vars[j], toCheck.checkVars[i][j]);
          }
        }
      } else {
        for (const [i, v] of toCheck.vars.entries()) {
          map.set(known.vars[i], v);
        }
      }

      const fixedKnown = known.fixStoredFact(map);

      let out = RType.True;

      for (const r of fixedKnown.req as L_Memory.StoredReq[]) {
        for (const fact of r.req as ToCheckNode[]) {
          if (fact instanceof OptNode) {
            out = checkOptLiterally(env, fact);
            if (out !== RType.True) break;
          } else {
            //! NEED TO IMPLEMENT HOW TO CHECK If-Then Literally?
            out = checkIfThen(env, fact as IfNode);
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
  if (toCheck.vars.length !== env.getDefs(toCheck.name)?.vars.length) {
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
        (v, i) => frees.includes(fact.vars[i]) || v === fact.vars[i],
      )
    ) {
      return RType.True;
    }
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
          true,
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
