import {
  DeclNode,
  FactNode,
  IffDeclNode,
  IfThenDeclNode,
  IfThenNode,
  OnlyIfDeclNode,
  OptNode,
} from "./ast";
import { L_Env } from "./L_Env";
import { RType } from "./L_Executor";

export class StoredReq {
  constructor(
    public vars: string[], // store free vars at current level
    public req: FactNode[]
  ) {}

  toString() {
    return `(if ${this.vars.join(", ")} | ${this.req.map((e) => e.toString()).join(", ")})`;
  }
}

export class StoredFact {
  constructor(
    public vars: string[], // stored fixed
    public req: StoredReq[], // when adding a new layer of if-then, push a new req list (FactNode[]) at end of req.
    public isT: Boolean
  ) {}

  toString() {
    if (this.isT)
      return `${this.vars} <=  ${this.req.map((e) => e.toString()).join(", ")}`;
    else
      return `[not] ${this.vars} <= ${this.req.map((e) => e.toString()).join(", ")}`;
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

export const EmptyStoreFact = new StoredFact([], [], true);

export namespace L_FactStorage {
  export function declNewFact(env: L_Env, toDecl: DeclNode) {
    const decl = new OptNode(toDecl.name, toDecl.vars);
    if (toDecl instanceof IfThenDeclNode) {
      const ifThen = new IfThenNode(
        toDecl.vars,
        [decl, ...toDecl.req],
        toDecl.onlyIfs,
        true,
        toDecl.byName
      );
      storeIfThen(env, ifThen, []);
      L_FactStorage.storeIfThenBy(env, ifThen, new StoredFact([], [], true));
    } else if (toDecl instanceof IffDeclNode) {
      storeIfThen(
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
      storeIfThen(
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
    } else if (toDecl instanceof OnlyIfDeclNode) {
      storeIfThen(
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
    }
  }

  function storeIfThen(env: L_Env, ifThen: IfThenNode, req: StoredReq[]) {
    for (const fact of ifThen.onlyIfs) {
      store(env, fact, [...req, new StoredReq(ifThen.vars, ifThen.req)]);
    }
  }

  function storeOpt(env: L_Env, fact: OptNode, req: StoredReq[]) {
    env.newFact(fact.fullName, fact.vars, req, fact.isT);
  }

  // Main Function of Storage
  export function store(
    env: L_Env,
    fact: FactNode,
    req: StoredReq[] = []
  ): Boolean {
    try {
      if (fact instanceof IfThenNode) storeIfThen(env, fact, req);
      else if (fact instanceof OptNode) storeOpt(env, fact, req);
      else throw Error();

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
}
