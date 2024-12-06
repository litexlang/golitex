import {
  DefNode,
  IfNode,
  LogicNode,
  OptNode,
  OrNode,
  ToCheckNode,
} from "./L_Nodes";
import { isToCheckBuiltin } from "./L_Builtins";
import { L_Env } from "./L_Env";
import { StoredFact, StoredReq } from "./L_Structs";
import { reportStoreErr } from "./L_Messages";

export function declNewFact(
  env: L_Env,
  node: DefNode,
  _storeDefName: boolean = true
): boolean {
  let ok = true;
  ok = env.newDef(node.opt.optSymbol.name, node);
  for (const onlyIf of node.onlyIfs) {
    const ok = store(env, onlyIf, [], false);
    if (!ok) return env.errMesReturnBoolean(`Failed to store ${onlyIf}`);
  }
  return ok;
}

export function newFact(env: L_Env, fact: ToCheckNode): boolean {
  if (isToCheckBuiltin(fact)) {
    const ok = newBuiltinFact(env, fact);
    return ok;
  }

  try {
    if (fact instanceof IfNode) {
      const ok = newIfThenFact(env, fact as IfNode);
      if (!ok) return false;
    } else if (fact instanceof OptNode) {
      const ok = newOptFact(env, fact);
      if (!ok) return false;
    } else {
      throw Error();
    }

    return env.OKMesReturnBoolean(`[new fact] ${fact}`);
  } catch {
    return reportStoreErr(env, newFact.name, fact);
  }
}

export function newIfThenFact(env: L_Env, fact: IfNode): boolean {
  try {
    return false;
  } catch {
    return reportStoreErr(env, newIfThenFact.name, fact);
  }
}

export function newOptFact(env: L_Env, fact: OptNode): boolean {
  try {
    return env.newKnown(fact.optSymbol.name, fact);
  } catch {
    return reportStoreErr(env, newOptFact.name, fact);
  }
}

export function newBuiltinFact(env: L_Env, fact: ToCheckNode): boolean {
  try {
    return false;
  } catch {
    return reportStoreErr(env, newBuiltinFact.name, fact);
  }
}

//----------------------------------------------------------------------

// store new fact; declare new fact if fact is of type exist.
function storeIfThen(
  env: L_Env,
  ifThen: IfNode,
  req: StoredReq[] = [],
  storeContrapositive: boolean = true
): boolean {
  try {
    if (ifThen.isT) {
      for (const fact of ifThen.onlyIfs) {
        const newReq = new StoredReq(ifThen.vars, ifThen.req);
        const ok = store(
          env,
          fact,
          [...req, newReq],
          storeContrapositive
          // storeDefName,
        );
        if (!ok) return false;
      }
    } else {
      return false;
    }

    return true;
  } catch {
    return false;
  }
}

function storeOpt(
  env: L_Env,
  fact: OptNode,
  req: StoredReq[],
  _storeContrapositive: boolean
): boolean {
  //*
  // if (L_BuiltinsKeywords.includes(fact.optSymbol)) return true;
  // const declaredOpt = env.getDef(fact.optSymbol);
  // if (declaredOpt === undefined) {
  //   env.newMessage(`${fact.optSymbol} undeclared`);
  //   return false;
  // } else {
  //   // TODO: I GUESS I SHOULD CHECK WHETHER GIVEN VARS SATISFY WHEN IN DEF
  //   if (declaredOpt.vars.length !== fact.vars.length) {
  //     env.newMessage(
  //       `${fact.optSymbol} requires ${declaredOpt.vars.length} parameters, ${fact.vars.length} given.`
  //     );
  //     return false;
  //   }
  // }
  // // env.newFact(fact.name, fact.vars, req, fact.isT);
  // // store contra positive when storing Opt.
  // // if (storeContrapositive) storeContrapositiveFacts(env, fact, req);
  // if (DEBUG_DICT["newFact"]) {
  //   const notWords = fact.isT === false ? "[not]" : "";
  //   if (req.length > 0) {
  //     env.newMessage(
  //       `[fact] ${notWords} ${fact.optSymbol}(${fact.vars}) <= ${req}`
  //     );
  //   } else env.newMessage(`[fact] ${notWords} ${fact.optSymbol}(${fact.vars})`);
  // }
  // let ok = false;
  // let toStore: StoredFact;
  // if (fact instanceof ExistNode) {
  //   toStore = new StoredExist(fact.vars, req, fact.isT);
  //   ok = env.newKnownFact(fact.optSymbol, toStore.getVarsToCheck(), toStore);
  // } else {
  //   toStore = new StoredFact(fact.vars, req, fact.isT);
  //   ok = env.newKnownFact(fact.optSymbol, toStore.getVarsToCheck(), toStore);
  // }
  // if (!ok) return false;
  // // If fact.vars contains all freeVars in current known if-then
  // if (req.length > 0) {
  //   const allFreeVars = toStore.getAllFreeVars();
  //   if (allFreeVars.every((e) => fact.vars.includes(e))) {
  //     ok = env.newKnownFact(fact.optSymbol, [], toStore);
  //   }
  // }
  // return true;
  //*

  return false;
}

function storeOr(
  env: L_Env,
  fact: OrNode,
  req: StoredReq[],
  storeContrapositive: boolean
): boolean {
  for (let i = 0; i < fact.facts.length; i++) {
    const asReq: ToCheckNode[] = [];
    for (let j = 0; j < fact.facts.length; j++) {
      if (j !== i) {
        asReq.push(fact.facts[j].copyWithoutIsT(!fact.facts[j].isT));
      }
    }
    const ok = store(
      env,
      fact.facts[i],
      [...req, new StoredReq([], asReq)],
      storeContrapositive
      // storeDefName,
    );
    if (!ok) return ok;
  }
  return true;
}

// Main Function of Storage
export function store(
  env: L_Env,
  fact: ToCheckNode,
  req: StoredReq[] = [],
  storeContrapositive: boolean
): boolean {
  if (isToCheckBuiltin(fact)) {
    const ok = storeBuiltinFact(env, fact, req, storeContrapositive);
    return ok;
  }

  try {
    if (fact instanceof LogicNode) {
      const ok = storeIfThen(env, fact as IfNode, req, storeContrapositive);
      if (!ok) return false;
    } else if (fact instanceof OptNode) {
      const ok = storeOpt(env, fact, req, storeContrapositive);
      if (!ok) return false;
    } else if (fact instanceof OrNode) {
      const ok = storeOr(env, fact, req, storeContrapositive);
      if (!ok) return false;
    } else {
      throw Error();
    }

    return true;
  } catch {
    env.newMessage(`Function L_Memory store error: ${fact}, req is ${req}.`);
    return false;
  }
}

/** MAIN FUNCTION OF THE WHOLE PROJECT
 *  Given an operator-type fact, return all stored facts that might check this fact.
 *  Only stored fact of correct environment level, i.e. if there are operators or variables with
 *  with the same name declared at some upper environment, Then these stored facts
 *  should are illegal to be returned.
 *
 *  @returns null means error. StoredFact[] is used to hold all legal stored facts.
 */
export function getStoredFacts(
  env: L_Env,
  opt: OptNode
): StoredFact[] | undefined {
  //*
  // // varDeclaredNumberMap is used to store how many times a variable is declared in all visible environments
  // const varsAsSet = new Set(opt.vars);
  // const varDeclaredNumberMap = new Map<string, number>();
  // for (const v of varsAsSet) {
  //   varDeclaredNumberMap.set(v, 0);
  // }
  // // know where the opt is declared.
  // let visibleEnvLevel = -1;
  // const tmp = env.whereIsOptDeclared(opt.optSymbol);
  // if (tmp !== undefined) {
  //   visibleEnvLevel = tmp;
  // } else {
  //   env.newMessage(`operator ${opt} not declared.`);
  //   return undefined;
  // }
  // // get fact from every visible env
  // const out: StoredFact[] = [];
  // for (
  //   let i = 0, curEnv: L_Env = env;
  //   i <= visibleEnvLevel && curEnv;
  //   i++, curEnv = curEnv.getParent() as L_Env
  // ) {
  //   // update how many times a given var is declared
  //   for (const v of varsAsSet) {
  //     if (curEnv.varDeclaredAtCurrentEnv(v)) {
  //       const curNumber = varDeclaredNumberMap.get(v) as number;
  //       varDeclaredNumberMap.set(v, curNumber + 1);
  //     }
  //   }
  //   // get stored facts from current environment level
  //   const facts = curEnv.getKnownFactsFromCurEnv(opt);
  //   if (facts === undefined) continue;
  //   for (const fact of facts) {
  //     const fixedVarsAtFact = fact.getFixedVars();
  //     // If the var is declared at a higher level, then the fact is RELATED TO THE VARIABLE WITH THE SAME NAME AT HIGHER LEVEL, NOT RELATED WITH CURRENT VARIABLE
  //     let invisible = false;
  //     for (const v of fixedVarsAtFact) {
  //       if (varsAsSet.has(v) && (varDeclaredNumberMap.get(v) as number) > 1) {
  //         invisible = true;
  //         break;
  //       }
  //     }
  //     if (invisible) continue;
  //     else out.push(fact);
  //   }
  // }
  // return out;
  //*

  return undefined;
}

export function executorStoreFact(
  env: L_Env,
  fact: ToCheckNode,
  storeContrapositive: boolean
): boolean {
  try {
    if (fact instanceof OptNode) {
      return storeOpt(env, fact as OptNode, [], storeContrapositive);
    } else if (fact instanceof IfNode) {
      const ok = storeIfThen(env, fact, [], storeContrapositive);
      if (!ok) {
        env.newMessage(`Failed to store ${fact}`);
        return false;
      }
      return true;
    } else if (fact instanceof OrNode) {
      return storeOr(env, fact, [], storeContrapositive);
    } else throw Error();
  } catch {
    env.newMessage(`Failed to store ${fact}`);
    return false;
  }
}

// deno-lint-ignore no-unused-vars
function storeContrapositiveFacts(
  env: L_Env,
  fact: OptNode,
  req: StoredReq[]
): boolean {
  let freeVars: string[] = [];
  let allStoredFactReq: ToCheckNode[] = [];
  for (const r of req) {
    freeVars = [...freeVars, ...r.vars];
    allStoredFactReq = [...allStoredFactReq, ...r.req];
  }

  const factInverse = fact.copyWithoutIsT(!fact.isT);

  for (let i = 0; i < allStoredFactReq.length; i++) {
    const r = allStoredFactReq.filter((_, index) => index !== i);
    r.push(factInverse);
    const ifThen = new IfNode(
      freeVars,
      r,
      [allStoredFactReq[i].copyWithoutIsT(!allStoredFactReq[i].isT)],
      true
      // false
    );
    const ok = storeIfThen(env, ifThen, [], false);
    if (!ok) return false;
  }

  return true;
}

//* toStore should not contain if-then req that contains opt as onlyIf.
export function examineStoredFact(
  env: L_Env,
  opt: OptNode,
  toStore: StoredFact
): boolean {
  try {
    for (const storedReq of toStore.req as StoredReq[]) {
      for (const toCheck of storedReq.req) {
        const factContainOptAsIfThenReqOnlyIf =
          toCheck.containOptAsIfThenReqOnlyIf(opt);
        if (factContainOptAsIfThenReqOnlyIf) {
          env.newMessage(
            `Error: ${toCheck} contains operator ${opt} as the onlyIf of a if type requirement.`
          );
          return false;
        }
      }
    }

    return true;
  } catch {
    return false;
  }
}

export function storeBuiltinFact(
  env: L_Env,
  fact: ToCheckNode,
  _req: StoredReq[],
  _storeContrapositive: boolean
): boolean {
  if (fact instanceof OptNode) {
    switch (fact.optSymbol) {
      default:
        return false;
    }
  }

  return false;
}
