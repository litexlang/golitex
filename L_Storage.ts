import { only } from "node:test";
import {
  DeclNode,
  ExistNode,
  FactNode,
  IffDeclNode,
  IfThenDeclNode,
  IfThenNode,
  OnlyIfDeclNode,
  OptNode,
} from "./ast";
import { L_Env } from "./env";
import { RType } from "./executor";

export namespace L_Storage {
  export class StoredFact {
    constructor(
      public vars: string[],
      public req: FactNode[],
      public isT: Boolean = true,
      public freeVars: string[]
    ) {}

    toString() {
      let result = "";
      result += this.vars
        .map((s) => (this.freeVars.includes(s) ? "#" + s : s))
        .join(", ");
      if (this.req.length > 0) {
        result += " <= ";
        result += this.req.map((e) => e.toString()).join("; ");
      }
      if (!this.isT) result = "[not] " + result;
      return result;
    }

    //! If the stored fact has no req, it means that this stored StoredFact is vanilla stored fact with opt-type.
    checkLiterally(vars: string[], isT: Boolean): RType {
      if (vars.length !== this.vars.length) return RType.Error;
      if (this.req.length !== 0) return RType.Unknown;
      if (this.isT !== isT) return RType.Unknown;

      const freeFixedMap = new Map<string, string>();
      for (const [i, v] of this.vars.entries()) {
        if (!this.freeVars.includes(v)) {
          if (v !== vars[i]) return RType.Unknown;
        }

        if (this.freeVars.includes(v)) {
          if (freeFixedMap.has(v)) {
            if (freeFixedMap.get(v) !== vars[i]) return RType.Unknown;
          } else {
            freeFixedMap.set(v, vars[i]);
          }
        } else {
          if (v !== vars[i]) return RType.Unknown;
        }
      }

      return RType.True;
    }
  }

  export function printEnvFacts(env: L_Env) {
    console.log("\n-----facts-------\n");

    for (const [key, factUnderCurKey] of env.storedFacts) {
      const t = env.getDeclFact(key) as DeclNode;
      let tStr = "";
      if (t instanceof IffDeclNode) {
        tStr = "iff";
      } else if (t instanceof IfThenDeclNode) {
        tStr = "if";
      } else if (t instanceof ExistNode) {
        tStr = "exist";
      } else if (t instanceof OnlyIfDeclNode) {
        tStr = "only_if";
      }

      console.log(`[${tStr}] ${key}`);
      factUnderCurKey.forEach((e: StoredFact) => {
        console.log(e.toString());
      });
      console.log();
    }
  }

  export function storeFactInDecl(env: L_Env, toDecl: DeclNode) {
    if (toDecl instanceof IfThenDeclNode) {
      const declFact = new OptNode(toDecl.name, toDecl.vars);
      for (const onlyIf of toDecl.onlyIfs) {
        //! TODO: ABLE TO STORE IF-THEN
        if (onlyIf instanceof OptNode)
          env.storeFact(
            onlyIf.fullName,
            toDecl.vars,
            [declFact, ...toDecl.req],
            true,
            toDecl.vars
          );
      }
    } else if (toDecl instanceof IffDeclNode) {
      const declFact = new OptNode(toDecl.name, toDecl.vars);
      for (const onlyIfs of toDecl.onlyIfs) {
        if (onlyIfs instanceof OptNode)
          env.storeFact(
            onlyIfs.fullName,
            toDecl.vars,
            // toDecl.req,
            [declFact, ...toDecl.req],
            true,
            toDecl.vars
          );
      }
      env.storeFact(
        declFact.fullName,
        toDecl.vars,
        [...toDecl.req, ...toDecl.onlyIfs],
        true,
        toDecl.vars
      );
    } else if (toDecl instanceof OnlyIfDeclNode) {
      const declFact = new OptNode(toDecl.name, toDecl.vars);
      env.storeFact(
        declFact.fullName,
        toDecl.vars,
        [...toDecl.req, ...toDecl.onlyIfs],
        true,
        toDecl.vars
      );
    }
    return true;
  }

  function storeIfThen(
    env: L_Env,
    ifThen: IfThenNode,
    req: FactNode[],
    isT: Boolean,
    frees: string[]
  ) {
    for (const onlyIf of ifThen.onlyIfs) {
      if (onlyIf instanceof OptNode) {
        storeOpt(env, onlyIf, [...req, ...ifThen.req], isT, frees);
      } else if (onlyIf instanceof IfThenNode) {
        storeIfThen(env, onlyIf, [...req, ...ifThen.req], isT, frees);
      }
    }
  }

  function storeOpt(
    env: L_Env,
    opt: OptNode,
    req: FactNode[],
    isT: Boolean,
    frees: string[]
  ) {
    env.storeFact(opt.fullName, opt.vars, req, isT, frees);
  }

  export function storeFact(
    env: L_Env,
    fact: FactNode,
    req: FactNode[],
    isT: Boolean,
    frees: string[]
  ) {
    if (fact instanceof OptNode) {
      storeOpt(env, fact, req, isT, frees);
    } else if (fact instanceof IfThenNode) {
      storeIfThen(env, fact, req, isT, frees);
    }
  }

  //--------------------------------------------------------------------

  export class StoredReq {
    constructor(
      public vars: string[],
      public req: FactNode[]
    ) {}

    toString() {
      return `(if ${this.vars} | ${this.req.map((e) => e.toString()).join(", ")})`;
    }
  }

  export class Fact {
    constructor(
      public vars: string[], // stored fixed
      public req: StoredReq[], // when adding a new layer of if-then, push a new req list (FactNode[]) at end of req.
      public isT: Boolean = true
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

  export function printEnvStoredFacts(env: L_Env) {
    console.log(`\n---Stored Facts---\n`);
    for (const [s, v] of env.storage.entries()) {
      console.log(s);
      v?.forEach((e) => console.log(e));
      if (v.length >= 0) console.log();
    }
  }

  export function newFactInEnv(env: L_Env, fact: FactNode, req: StoredReq[]) {
    if (fact instanceof OptNode) {
      const name = fact.fullName;

      //! ATTENTION: IMPORTANT RESTRICTION
      //? I GUESS THIS RESTRICTION MIGHT BE CONTROVERSIAL.
      let alreadyDeclared: string[] = [];
      for (const r of req) {
        if (!r.vars.every((e) => fact.vars.includes(e))) {
          env.newMessage(`${r.vars} not fully implemented.`);
          return;
        }
        if (r.vars.every((e) => !alreadyDeclared.includes(e))) {
          alreadyDeclared = [...alreadyDeclared, ...r.vars];
        } else {
          env.newMessage(`double declaration of some variables in ${r.vars}`);
          return;
        }
      }

      const toBeStored = new Fact(fact.vars, req, fact.isT);

      const out = env.storage.get(name);
      if (out === undefined) {
        env.storage.set(name, [toBeStored]);
      } else {
        out.push(toBeStored);
      }
    } else if (fact instanceof IfThenNode) {
      for (const onlyIf of fact.onlyIfs) {
        newFactInEnv(env, onlyIf, [...req, new StoredReq(fact.vars, fact.req)]);
      }
    }
  }

  export function declNewFact(env: L_Env, toDecl: DeclNode) {
    if (toDecl instanceof IfThenDeclNode) {
      newFactInEnv(
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
}
