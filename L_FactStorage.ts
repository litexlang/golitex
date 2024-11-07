import {
  ByNode,
  DeclNode,
  FactNode,
  IffDeclNode,
  IfThenDeclNode,
  IfThenNode,
  LogicalOptNode,
  OnlyIfDeclNode,
  OptNode,
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
    public isT: Boolean
  ) {}

  toString() {
    const notWords = this.isT ? "[not] " : "";
    const varsWords = this.vars.length > 0 ? this.vars.join(", ") : "";
    const reqWords =
      this.req.length > 0
        ? " <= " + this.req.map((e) => e.toString()).join(", ")
        : "";
    const onlyIfWords =
      this.onlyIfs.length > 0 ? `\n onlyIfs: ${this.onlyIfs}\n` : "";

    let out = notWords + varsWords + reqWords + onlyIfWords;

    // if (this.isT)
    //   out = `${this.vars.length > 0 ? this.vars.join(", ") + " <= " : ""}${this.req.map((e) => e.toString()).join(", ")}`;
    // else
    //   out = `[not] ${this.vars.length > 0 ? this.vars.join(", ") + " <= " : ""}${this.req
    //     .map((e) => e.toString())
    //     .join(", ")}`;

    // if (this.onlyIfs.length !== 0) {
    //   out += `\n onlyIfs: ${this.onlyIfs}\n`;
    // }

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

  isNoReq(): Boolean {
    for (const req of this.req) {
      if (req.req.length !== 0) return false;
    }
    return true;
  }

  checkLiterally(toCheckFixedVars: string[], isT: Boolean): RType {
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

export namespace L_FactStorage {
  export function declNewFact(env: L_Env, toDecl: DeclNode): Boolean {
    const decl = new OptNode(toDecl.name, toDecl.vars);
    let ok: Boolean = true;
    if (toDecl instanceof IfThenDeclNode) {
      const ifThen = new IfThenNode(
        toDecl.vars,
        [decl, ...toDecl.req],
        toDecl.onlyIfs,
        true,
        toDecl.byName
      );
      ok = storeIfThen(env, ifThen, []);
      return ok;
      // L_FactStorage.storeIfThenBy(env, ifThen, new StoredFact([], [], true));
    } else if (toDecl instanceof IffDeclNode) {
      ok = storeIfThen(
        env,
        new IfThenNode(
          toDecl.vars,
          [decl, ...toDecl.req],
          toDecl.onlyIfs,
          true,
          toDecl.byName
        ),
        []
      );
      if (!ok) return false;
      ok = storeIfThen(
        env,
        new IfThenNode(
          toDecl.vars,
          [...toDecl.req, ...toDecl.onlyIfs],
          [decl],
          true,
          toDecl.byName
        ),
        []
      );
      return ok;
    } else if (toDecl instanceof OnlyIfDeclNode) {
      ok = storeIfThen(
        env,
        new IfThenNode(
          toDecl.vars,
          [...toDecl.req, ...toDecl.onlyIfs],
          [decl],
          true,
          toDecl.byName
        ),
        []
      );
      return ok;
    }

    return false;
  }

  function storeIfThen(
    env: L_Env,
    ifThen: IfThenNode,
    req: StoredReq[]
  ): Boolean {
    for (const fact of ifThen.onlyIfs) {
      const ok = store(env, fact, [
        ...req,
        new StoredReq(ifThen.vars, ifThen.req),
      ]);
      if (!ok) return false;
    }

    return true;
  }

  function storeOpt(env: L_Env, fact: OptNode, req: StoredReq[]): Boolean {
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

    const out = env.newFact(fact.fullName, fact.vars, req, fact.isT);

    if (DEBUG_DICT["newFact"]) {
      if (req.length > 0)
        env.newMessage(`[new fact] ${fact.fullName}(${fact.vars}) <= ${req}`);
      else env.newMessage(`[new fact] ${fact.fullName}(${fact.vars})`);
    }

    return true;
  }

  // Main Function of Storage
  export function store(
    env: L_Env,
    fact: FactNode,
    req: StoredReq[] = []
  ): Boolean {
    try {
      if (fact instanceof IfThenNode) {
        const ok = storeIfThen(env, fact, req);
        if (!ok) return false;
      } else if (fact instanceof OptNode) {
        const ok = storeOpt(env, fact, req);
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
  export function getStoredFacts(
    env: L_Env,
    opt: OptNode
  ): StoredFact[] | null {
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
    let out: StoredFact[] = [];
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
    ifThen: IfThenNode,
    higherStoredFact: StoredFact
  ): void {
    try {
      higherStoredFact.req.push(new StoredReq(ifThen.vars, ifThen.req));

      if (ifThen.byName !== undefined) {
        higherStoredFact.onlyIfs = ifThen.onlyIfs;
        env.setBy(ifThen.byName, higherStoredFact);
        return;
      } else {
        for (const onlyIf of ifThen.onlyIfs) {
          if (onlyIf instanceof IfThenNode)
            storeIfThenBy(env, onlyIf, higherStoredFact);
        }
      }
    } catch (error) {
      throw Error();
    }
  }

  export function storeDeclaredIfThenAsBy(env: L_Env, node: DeclNode) {
    if (node.byName !== undefined && node instanceof IfThenDeclNode) {
      const ifThenToStore = new IfThenNode(node.vars, node.req, node.onlyIfs);
      ifThenToStore.byName = node.byName;
      storeIfThenBy(env, ifThenToStore, new StoredFact([], [], true));
    }
  }

  export function storeFactInStoredBy(env: L_Env, byNode: ByNode): Boolean {
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
      for (const [i, v] of allFreeVars.entries()) {
        map.set(allFreeVars[i], byNode.vars[i]);
      }

      // Store onlyIfs bound to StoredBy
      let onlyIfsToBeStored: FactNode[] = [];
      for (const onlyIf of storedFact.onlyIfs) {
        onlyIfsToBeStored.push(onlyIf.useMapToCopy(map));
      }

      let ok: Boolean = true;
      for (const onlyIf of onlyIfsToBeStored) {
        ok = store(env, onlyIf, []);
        if (!ok) {
          env.newMessage(`Failed to store ${onlyIf}`);
          return false;
        }
      }
      return true;
    } catch (error) {
      throw Error();
    }
  }
}
