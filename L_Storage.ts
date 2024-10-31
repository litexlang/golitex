import { DeclNode, FactNode, IfThenDeclNode, IfThenNode, OptNode } from "./ast";
import { L_Env } from "./L_Env";
import { RType } from "./L_Executor";

export namespace L_Storage {
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

  export function declNewFact(env: L_Env, toDecl: DeclNode) {
    if (toDecl instanceof IfThenDeclNode) {
      storeIfThen(
        env,
        new IfThenNode(
          toDecl.vars,
          [new OptNode(toDecl.name, toDecl.vars), ...toDecl.req],
          toDecl.onlyIfs
        ),
        []
      );
    }
  }

  function storeIfThen(env: L_Env, ifThen: IfThenNode, req: StoredReq[]) {
    for (const fact of ifThen.onlyIfs) {
      L_Store(env, fact, [...req, new StoredReq(ifThen.vars, ifThen.req)]);
    }
  }

  function yaStoreOpt(env: L_Env, fact: OptNode, req: StoredReq[]) {
    env.pushIntoStorage(fact.fullName, fact.vars, req, fact.isT);
  }

  // Main Function of Saver
  export function L_Store(env: L_Env, fact: FactNode, req: StoredReq[]) {
    if (fact instanceof IfThenNode) storeIfThen(env, fact, req);
    else if (fact instanceof OptNode) yaStoreOpt(env, fact, req);
    else throw Error();
  }
}
