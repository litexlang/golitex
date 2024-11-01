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
    return `(if ${this.vars} | ${this.req.map((e) => e.toString()).join(", ")})`;
  }
}

export class StoredFact {
  constructor(
    public vars: string[], // stored fixed
    public req: StoredReq[], // when adding a new layer of if-then, push a new req list (FactNode[]) at end of req.
    // public env: L_Env,
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
  export function declNewFact(env: L_Env, toDecl: DeclNode) {
    const decl = new OptNode(toDecl.name, toDecl.vars);
    if (toDecl instanceof IfThenDeclNode) {
      storeIfThen(
        env,
        new IfThenNode(toDecl.vars, [decl, ...toDecl.req], toDecl.onlyIfs),
        []
      );
    } else if (toDecl instanceof IffDeclNode) {
      storeIfThen(
        env,
        new IfThenNode(toDecl.vars, [decl, ...toDecl.req], toDecl.onlyIfs),
        []
      );
      storeIfThen(
        env,
        new IfThenNode(toDecl.vars, [...toDecl.req, ...toDecl.onlyIfs], [decl]),
        []
      );
    } else if (toDecl instanceof OnlyIfDeclNode) {
      storeIfThen(
        env,
        new IfThenNode(toDecl.vars, [...toDecl.req, ...toDecl.onlyIfs], [decl]),
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
  export function store(env: L_Env, fact: FactNode, req: StoredReq[]) {
    if (fact instanceof IfThenNode) storeIfThen(env, fact, req);
    else if (fact instanceof OptNode) storeOpt(env, fact, req);
    else throw Error();
  }
}
