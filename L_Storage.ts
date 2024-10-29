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
      for (const [i, freeVar] of this.freeVars.entries()) {
        if (this.freeVars.includes(freeVar)) {
          if (freeFixedMap.has(freeVar)) {
            if (freeFixedMap.get(freeVar) !== vars[i]) return RType.Unknown;
          } else {
            freeFixedMap.set(freeVar, vars[i]);
          }
        } else {
          if (freeVar !== vars[i]) return RType.Unknown;
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
        if (onlyIf instanceof OptNode)
          env.storeFact(
            onlyIf.fullName,
            toDecl.vars,
            [declFact],
            true,
            toDecl.vars
          );
      }
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
}
