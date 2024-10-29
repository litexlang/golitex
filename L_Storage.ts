import {
  DeclNode,
  ExistNode,
  FactNode,
  IffDeclNode,
  IfThenDeclNode,
  OnlyIfDeclNode,
  OptNode,
} from "./ast";
import { L_Env } from "./env";
import { RType } from "./executor";

export namespace L_Storage {
  export class Fact {
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

    checkLiterally(opt: OptNode): RType {
      if (opt.vars.length !== this.vars.length) return RType.Error;
      if (this.req.length !== 0) return RType.Unknown;
      if (this.isT !== opt.isT) return RType.Unknown;

      const freeFixedMap = new Map<string, string>();
      for (const [i, freeVar] of this.freeVars.entries()) {
        if (this.freeVars.includes(freeVar)) {
          if (freeFixedMap.has(freeVar)) {
            if (freeFixedMap.get(freeVar) !== opt.vars[i]) return RType.Unknown;
          } else {
            freeFixedMap.set(freeVar, opt.vars[i]);
          }
        } else {
          if (freeVar !== opt.vars[i]) return RType.Unknown;
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
      factUnderCurKey.forEach((e: Fact) => {
        console.log(e.toString());
      });
      console.log();
    }
  }

  export function storeFact(
    env: L_Env,
    name: string,
    vars: string[],
    req: FactNode[],
    isT: Boolean = true,
    freeVars: string[]
  ): boolean {
    try {
      if (env.storedFacts.get(name) === undefined) {
        if (env.getDeclFact(name)) {
          env.storedFacts.set(name, [new Fact(vars, req, isT, freeVars)]);
          return true;
        } else {
          env.newMessage(`${name} not declared.`);
          return false;
        }
      } else {
        env.storedFacts.get(name)!.push(new Fact(vars, req, isT, freeVars));
        return true;
      }
    } catch (error) {
      env.newMessage(`failed to store fact about ${name}.`);
      return false;
    }
  }

  export function storeFactInDecl(env: L_Env, node: DeclNode) {
    if (node instanceof IfThenDeclNode) {
      const declFact = new OptNode(node.name, node.vars);
      for (const onlyIf of node.onlyIfs) {
        return env.storeFact(
          node.name,
          node.vars,
          [declFact, ...node.req],
          true,
          node.vars
        );
      }
    }
    return null;
  }
}
