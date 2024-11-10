import {
  ByNode,
  DeclNode,
  FactNode,
  IffDeclNode,
  IfThenDeclNode,
  IfIffNode,
  OnlyIfDeclNode,
  OptNode,
  OrNode,
  ExistNode,
} from "./ast.ts";
import { L_Env } from "./L_Env.ts";
import { DEBUG_DICT, RType } from "./L_Executor.ts";

export class StoredReq {
  constructor(
    public vars: string[], // store free vars at current level
    public req: FactNode[]
  ) {}

  toString() {
    return `(if ${this.vars.join(", ")} : ${this.req
      .map((e) => e.toString())
      .join(", ")})`;
  }
}

export class StoredFact {
  public onlyIfs: FactNode[] = []; //? MAYBE USELESS

  constructor(
    public vars: string[], // stored fixed, only used when storing opts
    public req: StoredReq[], // when adding a new layer of if-then, push a new req list (FactNode[]) at end of req.
    public isT: boolean
  ) {}

  toString() {
    const notWords = this.isT === false ? "[not] " : "";
    const varsWords = this.vars.length > 0 ? this.vars.join(", ") : "";
    const reqWords =
      this.req.length > 0
        ? " <= " + this.req.map((e) => e.toString()).join(", ")
        : "";
    const onlyIfWords =
      this.onlyIfs.length > 0 ? `\n onlyIfs: ${this.onlyIfs}\n` : "";

    const out = notWords + varsWords + reqWords + onlyIfWords;

    return out;
  }

  getAllFreeVars() {
    const varsLst: string[][] = this.req.map((e) => e.vars);
    let out: string[] = [];
    varsLst.forEach((e) => {
      out = [...out, ...e];
    });
    return out;
  }

  getFixedVars() {
    const out = [];
    const frees = this.getAllFreeVars();
    for (const v of this.vars) {
      if (!frees.includes(v)) out.push(v);
    }
    return out;
  }

  isNoReq(): boolean {
    for (const req of this.req) {
      if (req.req.length !== 0) return false;
    }
    return true;
  }

  checkLiterally(toCheckFixedVars: string[], isT: boolean): RType {
    const noExtraReq = this.req.every((e) => e.req.length === 0);
    if (!noExtraReq) return RType.Unknown;

    if (isT !== this.isT) return RType.Unknown;

    //! the following check is based on hypothesis that toCheckFixedVars declared at different level are different
    const frees = this.getAllFreeVars();
    for (const [i, v] of toCheckFixedVars.entries()) {
      if (frees.includes(v)) continue;
      else if (toCheckFixedVars[i] === this.vars[i]) continue;
      else return RType.Unknown;
    }

    return RType.True;
  }
}

export function declNewFact(env: L_Env, toDecl: DeclNode): boolean {
  const decl = new OptNode(toDecl.name, toDecl.vars);
  let ok: boolean = true;
  if (toDecl instanceof IfThenDeclNode) {
    const ifThen = new IfIffNode(
      toDecl.vars,
      [decl, ...toDecl.req],
      toDecl.onlyIfs,
      false,
      toDecl.byName
    );
    ok = storeIfThen(env, ifThen, [], true);
    return ok;
    // L_FactStorage.storeIfThenBy(env, ifThen, new StoredFact([], [], true));
  } else if (toDecl instanceof IffDeclNode) {
    ok = storeIfThen(
      env,
      new IfIffNode(
        toDecl.vars,
        [decl, ...toDecl.req],
        toDecl.onlyIfs,
        false,
        toDecl.byName
      ),
      [],
      true
    );
    if (!ok) return false;
    ok = storeIfThen(
      env,
      new IfIffNode(
        toDecl.vars,
        [...toDecl.req, ...toDecl.onlyIfs],
        [decl],
        false,
        toDecl.byName
      ),
      [],
      true
    );
    return ok;
  } else if (toDecl instanceof OnlyIfDeclNode) {
    ok = storeIfThen(
      env,
      new IfIffNode(
        toDecl.vars,
        [...toDecl.req, ...toDecl.onlyIfs],
        [decl],
        true,
        toDecl.byName
      ),
      [],
      true
    );
    return ok;
  }

  return false;
}

function storeIfThen(
  env: L_Env,
  ifThen: IfIffNode,
  req: StoredReq[],
  storeContrapositive: boolean
): boolean {
  try {
    if (ifThen.isT) {
      for (const fact of ifThen.onlyIfs) {
        const ok = store(
          env,
          fact,
          [...req, new StoredReq(ifThen.vars, ifThen.req)],
          storeContrapositive
        );
        if (!ok) return false;
      }

      if (ifThen.isIff) {
        for (const fact of ifThen.req) {
          const ok = store(
            env,
            fact,
            [...req, new StoredReq(ifThen.vars, ifThen.onlyIfs)],
            storeContrapositive
          );
          if (!ok) return false;
        }
      }

      return true;
    } else {
      if (ifThen.byName === undefined) {
        env.newMessage(
          `Failed to store ${ifThen}, because it's suppose to have a name.`
        );
      }

      // declareAndStoreExist(env);
      return declareAndStoreExist(
        env,
        ExistNode.ifThenToExist(ifThen),
        [],
        true
      );
    }
  } catch {
    return false;
  }
}

function storeOpt(
  env: L_Env,
  fact: OptNode,
  req: StoredReq[],
  storeContrapositive: boolean
): boolean {
  const declaredOpt = env.getDeclaredFact(fact.fullName);
  if (declaredOpt === undefined) {
    env.newMessage(`${fact.fullName} undeclared`);
    return false;
  } else {
    // TODO: I GUESS I SHOULD CHECK WHETHER GIVEN VARS SATISFY WHEN IN DEF
    if (declaredOpt.vars.length !== fact.vars.length) {
      env.newMessage(
        `${fact.fullName} requires ${declaredOpt.vars.length} parameters, ${fact.vars.length} given.`
      );
      return false;
    }
  }

  env.newFact(fact.fullName, fact.vars, req, fact.isT);

  // store contra positive when storing Opt.
  if (storeContrapositive) storeContrapositiveFacts(env, fact, req);

  if (DEBUG_DICT["newFact"]) {
    const notWords = fact.isT === false ? "[not]" : "";
    if (req.length > 0)
      env.newMessage(
        `[new fact] ${notWords} ${fact.fullName}(${fact.vars}) <= ${req}`
      );
    else
      env.newMessage(`[new fact] ${notWords} ${fact.fullName}(${fact.vars})`);
  }

  return true;
}

function storeOr(
  env: L_Env,
  fact: OrNode,
  req: StoredReq[],
  storeContrapositive: boolean
): boolean {
  for (let i = 0; i < fact.facts.length; i++) {
    const asReq: FactNode[] = [];
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
    );
    if (!ok) return ok;
  }
  return true;
}

// Main Function of Storage
export function store(
  env: L_Env,
  fact: FactNode,
  req: StoredReq[] = [],
  storeContrapositive: boolean
): boolean {
  try {
    if (fact instanceof IfIffNode) {
      const ok = storeIfThen(env, fact, req, storeContrapositive);
      if (!ok) return false;
    } else if (fact instanceof OptNode) {
      const ok = storeOpt(env, fact, req, storeContrapositive);
      if (!ok) return false;
    } else if (fact instanceof OrNode) {
      const ok = storeOr(env, fact, req, storeContrapositive);
      if (!ok) return false;
    } else throw Error();

    return true;
  } catch {
    env.newMessage(`Failed to store ${fact}.`);
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
export function getStoredFacts(env: L_Env, opt: OptNode): StoredFact[] | null {
  // varDeclaredNumberMap is used to store how many times a variable is declared in all visible environments
  const varsAsSet = new Set(opt.vars);
  const varDeclaredNumberMap = new Map<string, number>();
  for (const v of varsAsSet) {
    varDeclaredNumberMap.set(v, 0);
  }

  // know where the opt is declared.
  let visibleEnvLevel = -1;
  const tmp = env.whereIsOptDeclared(opt.fullName);
  if (tmp !== undefined) {
    visibleEnvLevel = tmp;
  } else {
    env.newMessage(`${opt} not declared.`);
    return null;
  }

  // get fact from every visible env
  const out: StoredFact[] = [];
  for (
    let i = 0, curEnv: L_Env = env;
    i <= visibleEnvLevel && curEnv;
    i++, curEnv = curEnv.getFather() as L_Env
  ) {
    // update how many times a given var is declared
    for (const v of varsAsSet) {
      if (curEnv.varDeclaredAtCurrentEnv(v)) {
        const curNumber = varDeclaredNumberMap.get(v) as number;
        varDeclaredNumberMap.set(v, curNumber + 1);
      }
    }

    // get stored facts from current environment level
    const facts = curEnv.getStoredFactsFromCurrentEnv(opt.fullName);
    if (facts === undefined) continue;

    for (const fact of facts) {
      const fixedVarsAtFact = fact.getFixedVars();

      // If the var is declared at a higher level, then the fact is RELATED TO THE VARIABLE WITH THE SAME NAME AT HIGHER LEVEL, NOT RELATED WITH CURRENT VARIABLE
      let invisible = false;
      for (const v of fixedVarsAtFact) {
        if (varsAsSet.has(v) && (varDeclaredNumberMap.get(v) as number) > 1) {
          invisible = true;
          break;
        }
      }

      if (invisible) continue;
      else out.push(fact);
    }

    // const facts = curEnv.getStoredFactsFromCurrentEnv(opt.fullName);
    // if (facts === undefined) continue;
    // else out = [...out, ...facts];
  }

  return out;
}

export function storeIfThenBy(
  env: L_Env,
  ifThen: IfIffNode,
  higherStoredFact: StoredFact
): boolean {
  try {
    higherStoredFact.req.push(new StoredReq(ifThen.vars, ifThen.req));

    if (ifThen.byName !== undefined) {
      higherStoredFact.onlyIfs = ifThen.onlyIfs;
      env.setBy(ifThen.byName, higherStoredFact);
      if (DEBUG_DICT["storeBy"]) {
        env.newMessage(`[new by] ${ifThen.byName}`);
      }
      return true;
    } else {
      for (const onlyIf of ifThen.onlyIfs) {
        if (onlyIf instanceof IfIffNode) {
          const out = storeIfThenBy(env, onlyIf, higherStoredFact);
          if (!out) {
            env.newMessage(`Failed to declare ${onlyIf}`);
            return false;
          }
        }
      }
    }

    return true;
  } catch {
    throw Error();
  }
}

export function storeDeclaredIfThenAsBy(env: L_Env, node: DeclNode) {
  if (node.byName !== undefined && node instanceof IfThenDeclNode) {
    const ifThenToStore = new IfIffNode(node.vars, node.req, node.onlyIfs);
    ifThenToStore.byName = node.byName;
    storeIfThenBy(env, ifThenToStore, new StoredFact([], [], true));
  }
}

export function storeFactInStoredBy(
  env: L_Env,
  byNode: ByNode,
  storeContrapositive: boolean
): boolean {
  try {
    const storedFact = env.getBy(byNode.byName) as StoredFact;

    const allFreeVars = storedFact.getAllFreeVars();
    if (byNode.vars.length !== allFreeVars.length) {
      env.newMessage(
        `${byNode.byName} expect ${allFreeVars.length} variables, got ${byNode.vars.length}`
      );
      return false;
    }
    const map = new Map<string, string>();
    for (const [i] of allFreeVars.entries()) {
      map.set(allFreeVars[i], byNode.vars[i]);
    }

    // Store onlyIfs bound to StoredBy
    const onlyIfsToBeStored: FactNode[] = [];
    for (const onlyIf of storedFact.onlyIfs) {
      onlyIfsToBeStored.push(onlyIf.useMapToCopy(map));
    }

    let ok: boolean = true;
    for (const onlyIf of onlyIfsToBeStored) {
      ok = store(env, onlyIf, [], storeContrapositive);
      if (!ok) {
        env.newMessage(`Failed to store ${onlyIf}`);
        return false;
      }
    }
    return true;
  } catch {
    throw Error();
  }
}

function declareAndStoreExist(
  env: L_Env,
  fact: ExistNode,
  req: StoredReq[],
  isT: boolean = false
): boolean {
  try {
    if (fact.byName === undefined) {
      env.newMessage(`${fact.byName} has already declared as st name.`);
      throw Error();
    }

    const newReq = [
      ...req,
      new StoredReq(fact.vars, [...fact.req, ...fact.onlyIfs]),
    ];
    const toBeStored = new StoredFact(fact.vars, newReq, isT);

    return env.newExist(fact.byName, toBeStored);
  } catch {
    throw Error();
  }
}

export function storeFactAndBy(
  env: L_Env,
  fact: FactNode,
  storeContrapositive: boolean
): boolean {
  try {
    if (fact instanceof OptNode) {
      return storeOpt(env, fact as OptNode, [], storeContrapositive);
    } else if (fact instanceof ExistNode) {
      return declareAndStoreExist(env, fact, [], true);
    } else if (fact instanceof IfIffNode) {
      let ok = storeIfThen(env, fact, [], storeContrapositive);
      if (!ok) {
        env.newMessage(`Failed to store ${fact}`);
        return false;
      }
      ok = storeIfThenBy(env, fact, new StoredFact([], [], true));
      if (!ok) {
        env.newMessage(`Failed to declare ${fact}`);
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

function storeContrapositiveFacts(
  env: L_Env,
  fact: OptNode,
  req: StoredReq[]
): boolean {
  let freeVars: string[] = [];
  let allStoredFactReq: FactNode[] = [];
  for (const r of req) {
    freeVars = [...freeVars, ...r.vars];
    allStoredFactReq = [...allStoredFactReq, ...r.req];
  }

  const factInverse = fact.copyWithoutIsT(!fact.isT);

  for (let i = 0; i < allStoredFactReq.length; i++) {
    const r = allStoredFactReq.filter((_, index) => index !== i);
    r.push(factInverse);
    const ifThen = new IfIffNode(
      freeVars,
      r,
      [allStoredFactReq[i].copyWithoutIsT(!allStoredFactReq[i].isT)],
      true,
      undefined,
      false
    );
    const ok = storeIfThen(env, ifThen, [], false);
    if (!ok) return false;
  }

  return true;
}

export function storeExistFact(
  env: L_Env,
  fact: ExistNode,
  req: StoredReq[],
  storeContrapositive: boolean
): boolean {
  try {
    if (fact.isT) {
      if (fact.byName === undefined) {
        env.newMessage(`Failed to store ${fact}, name undefined.`);
        return false;
      }

      return declareAndStoreExist(env, fact, req, true);
    } else {
      const ok = storeIfThen(
        env,
        fact.getContraPositive(),
        req,
        storeContrapositive
      );
      return ok;
    }
  } catch {
    env.newMessage(`Failed to store '${fact}'`);
    return false;
  }
}
