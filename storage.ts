import { DeclNode, FactNode, IfThenDeclNode } from "./ast";
import { L_Env } from "./env";

export class StoredFact {
  constructor(
    public vars: string[],
    public req: FactNode[],
    public isT: Boolean = true,
    public freeVars: string[]
  ) {}

  toString() {
    let result = "";
    result += this.vars.join(", ");
    if (this.req.length > 0) {
      result += " | ";
      result += this.req.map((e) => e.toString()).join("; ");
    }
    if (!this.isT) result = "[not] " + result;
    return result;
  }
}

export namespace storage {
  function storeFact(
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
          env.storedFacts.set(name, [new StoredFact(vars, req, isT, freeVars)]);
          return true;
        } else {
          env.newMessage(`${name} not declared.`);
          return false;
        }
      } else {
        env.storedFacts
          .get(name)!
          .push(new StoredFact(vars, req, isT, freeVars));
        return true;
      }
    } catch (error) {
      env.newMessage(`failed to store fact about ${name}.`);
      return false;
    }
  }

  function storeFactInDecl(env: L_Env, node: DeclNode) {
    let out = false;
    if (node instanceof IfThenDeclNode) {
      return env.storeFact(node.name, node.vars, node.req, true, node.vars);
    }
  }
}
