import { IfNode, OptNode, OrNode, ToCheckNode } from "./L_Nodes.ts";
import { L_Env } from "./L_Env.ts";
import { L_Out } from "./L_Executor.ts";
import { StoredFact } from "./L_Memory.ts";
import * as L_Memory from "./L_Memory.ts";
import { L_Builtins } from "./L_Builtins.ts";
import { lstLengthNotEql } from "./L_ErrorReport.ts";

export function check(
  env: L_Env,
  toCheck: ToCheckNode,
  toCheckVarsFromIf: string[][] = [],
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
  toCheckVarsFromIf: string[][],
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
    toCheckVarsFromIf: string[][],
  ): L_Out {
    const newEnv = new L_Env(oldEnv);

    for (const e of toCheck.vars) {
      const ok = newEnv.newVar(e);
      if (!ok) return L_Out.Error;
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
  toCheckVarsFromIf: string[][] = [],
): L_Out {
  const builtins = L_Builtins.get(toCheck.name);
  if (builtins !== undefined) {
    return builtins(env, toCheck);
  }

  //* cond of fact must be satisfied
  const out = checkOptCond(env, toCheck);
  if (out !== L_Out.True) {
    return out;
  }

  const knowns = L_Memory.getStoredFacts(env, toCheck);
  if (knowns === undefined) return L_Out.Unknown;

  for (const known of knowns as StoredFact[]) {
    // check req
    if (known.req.length > 0) {
      const map = new Map<string, string>();
      if (known.isT !== toCheck.isT) continue;

      if (toCheck.checkVars !== undefined) {
        for (let i = 0; i < toCheck.checkVars.length; i++) {
          for (let j = 0; j < toCheck.checkVars[i].length; j++) {
            map.set(known.req[i].vars[j], toCheck.checkVars[i][j]);
          }
        }
      } else {
        //! NOT RIGHT HERE
        for (const [i, v] of toCheck.vars.entries()) {
          map.set(known.vars[i], v);
        }
      }

      const fixedKnown = known.fixStoredFact(map);

      let out = L_Out.True;

      for (const r of fixedKnown.req as L_Memory.StoredReq[]) {
        for (const fact of r.req as ToCheckNode[]) {
          if (fact instanceof OptNode) {
            out = checkOptLiterally(env, fact);
            if (out !== L_Out.True) break;
          } else {
            //! NEED TO IMPLEMENT HOW TO CHECK If-Then Literally?
            // 也可以是  out = checkIfThen(env, fact as IfNode, []);
            out = checkIfThen(env, fact as IfNode, toCheckVarsFromIf);
            if (out !== L_Out.True) break;
          }
        }
        if (out === L_Out.Unknown) break;
      }

      if (out === L_Out.True) return L_Out.True;
    } else {
      if (known.vars.every((e, i) => e === toCheck.vars[i])) return L_Out.True;
      else continue;
    }
  }

  //* use checkVars from if to check *//
  if (useCheckVarsFromIf) {
    for (let i = 0; i < toCheckVarsFromIf.length; i++) {
      // use toCheckVarsFromIf layer by layer
      const curToCheckVars = toCheckVarsFromIf.slice(i);
      const newOpt = new OptNode(
        toCheck.name,
        toCheck.vars,
        toCheck.isT,
        curToCheckVars,
      );
      const out = checkOpt(env, newOpt, false);
      if (out === L_Out.True) return L_Out.True;

      // use toCheckVarsFromIf as if it's single layer
      const anotherCurCheckVars: string[] = [];
      curToCheckVars.map((e) => anotherCurCheckVars.push(...e));
      const anotherOpt = new OptNode(
        toCheck.name,
        toCheck.vars,
        toCheck.isT,
        [anotherCurCheckVars],
      );
      if (checkOpt(env, anotherOpt, false) === L_Out.True) return L_Out.True;
    }
  }

  return L_Out.Unknown;
}

// check whether a variable in fact.vars is free or fixed at check time instead of run time.
export function checkOptLiterally(env: L_Env, toCheck: OptNode): L_Out {
  const builtins = L_Builtins.get(toCheck.name);
  if (builtins !== undefined) {
    return builtins(env, toCheck);
  }

  if (toCheck.vars.length !== env.getDef(toCheck.name)?.vars.length) {
    return L_Out.Unknown;
  }

  const facts = env.getKnownFactsFromCurEnv(toCheck);
  // const facts: StoredFact[] | null = L_Memory.getStoredFacts(env, toCheck);

  if (facts === undefined) {
    env.newMessage(`check Error: ${toCheck.name} not declared.`);
    return L_Out.Error;
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
      return L_Out.True;
    }
  }

  return L_Out.Unknown;
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
          true,
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
  const def = env.getDef(toCheck.name);
  if (def === undefined) {
    return env.errMesReturnL_Out(`${toCheck} not declared.`);
  }
  if (toCheck.vars.length !== def.vars.length) {
    return lstLengthNotEql(env, toCheck.vars, def.vars);
  }

  const map = new Map<string, string>();
  for (const [i, v] of toCheck.vars.entries()) {
    map.set(def.vars[i], v);
  }

  for (const condition of def?.cond) {
    const fixed = condition.useMapToCopy(map);
    const out = check(env, fixed);
    if (out !== L_Out.True) {
      env.newMessage(`[Unknown] ${fixed}`);
      return L_Out.Unknown;
    }
  }

  return L_Out.True;
}
