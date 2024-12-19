import {
  BuiltinCheckNode,
  DefNode,
  L_Node,
  DefCompositeNode,
  LogicNode,
  OptNode,
  ToCheckNode,
  ToCheckFormulaNode,
} from "./L_Nodes";
import * as L_Nodes from "./L_Nodes";
import { L_KnownFact, L_OptSymbol, L_Out } from "./L_Structs";

export class L_Env {
  private parent: L_Env | undefined = undefined;
  private messages: string[] = [];
  private declaredSingletons = new Set<string>();
  private defs = new Map<string, DefNode>();
  private facts = new Map<string, L_KnownFact[]>();
  private declaredComposites = new Map<string, DefCompositeNode>();
  private letsVars: L_Nodes.LetsNode[] = [];

  constructor(parent: L_Env | undefined = undefined) {
    this.parent = parent;
  }

  newCompositeVar(key: string, fact: DefCompositeNode): boolean {
    if (this.declaredComposites.get(key)) {
      this.report(`Failed: ${key} already declared.`);
      return false;
    } else {
      this.declaredComposites.set(key, fact);
      return true;
    }
  }

  getCompositeVar(key: string): undefined | DefCompositeNode {
    const out = this.declaredComposites.get(key);
    if (out !== undefined) {
      return out;
    } else {
      if (this.parent !== undefined) {
        return this.parent.getCompositeVar(key);
      } else {
        return undefined;
      }
    }
  }

  newFact(key: string, fact: L_KnownFact): boolean {
    if (this.facts.get(key) === undefined) {
      this.facts.set(key, [fact]);
    } else {
      this.facts.get(key)?.push(fact);
    }
    return true;
  }

  getFacts(
    key: string,
    factsFromParent: L_KnownFact[] | undefined = undefined
  ): undefined | L_KnownFact[] {
    // Initialize factsFromParent if it's undefined
    if (factsFromParent === undefined) {
      factsFromParent = [];
    }

    // Check facts in current instance
    const currentFacts = this.facts.get(key);
    if (currentFacts !== undefined) {
      factsFromParent.push(...currentFacts);
    }

    // If no parent, return accumulated facts
    if (this.parent === undefined) {
      return factsFromParent.length > 0 ? factsFromParent : undefined;
    }

    // Recursively get facts from parent
    return this.parent.getFacts(key, factsFromParent);
  }

  clear() {
    this.parent = undefined;
    this.messages = [];
    this.declaredSingletons = new Set<string>();
    this.letsVars = [];
    this.defs = new Map<string, DefNode>();
  }

  getLetsVars(): L_Nodes.LetsNode[] {
    let letsVarsFromAllEnvs: L_Nodes.LetsNode[] = [...this.letsVars];
    if (this.parent !== undefined) {
      letsVarsFromAllEnvs.push(...this.parent.getLetsVars());
      return letsVarsFromAllEnvs;
    } else {
      return this.letsVars;
    }
  }

  newLetsVars(macroNode: L_Nodes.LetsNode) {
    this.letsVars.push(macroNode);
  }

  // used by checker and executor
  factsInToCheckAllDeclaredOrBuiltin(node: ToCheckNode): boolean {
    if (node instanceof OptNode) {
      return (
        this.getDef(node.optSymbol.name) !== undefined ||
        node instanceof BuiltinCheckNode
      );
    } else if (node instanceof LogicNode) {
      return (
        node.req.every((e) => this.factsInToCheckAllDeclaredOrBuiltin(e)) &&
        node.onlyIfs.every((e) => this.factsInToCheckAllDeclaredOrBuiltin(e))
      );
    } else if (node instanceof BuiltinCheckNode) {
      return true;
    } else if (node instanceof ToCheckFormulaNode) {
      return (
        this.factsInToCheckAllDeclaredOrBuiltin(node.left) &&
        this.factsInToCheckAllDeclaredOrBuiltin(node.right)
      );
    }

    return false;
  }

  getDef(s: string): DefNode | undefined {
    if (this.defs.has(s)) {
      return this.defs.get(s);
    } else if (this.parent) {
      return this.parent.getDef(s);
    } else {
      return undefined;
    }
  }

  newDef(s: string, DefNode: DefNode): boolean {
    // REMARK: YOU ARE NOT ALLOWED TO DECLARE A FACT TWICE AT THE SAME ENV.
    if (this.getDef(s) !== undefined) {
      this.report(
        `${s} already declared in this environment or its parents environments.`
      );
      return false;
    }

    this.defs.set(s, DefNode);
    this.report(`[def] ${DefNode}`);
    return true;
  }

  newSingletonVar(fix: string): boolean {
    // TO MAKE MY LIFE EASIER SO THAT I DO NOT NEED TO BIND ENV TO VARIABLE, I forbid redefining a variable with the same name with any visible variable.
    if (this.singletonDeclared(fix)) {
      this.report(`${fix} already declared.`);
      return false;
    }
    this.declaredSingletons.add(fix);
    return true;
  }

  singletonDeclared(key: string): boolean {
    if (this.declaredSingletons.has(key)) {
      return true;
    } else {
      if (!this.parent) return false;
      else return this.parent.singletonDeclared(key);
    }
  }

  optDeclared(key: string): boolean {
    if (this.defs.get(key)) {
      return true;
    } else {
      if (!this.parent) return false;
      else return this.parent.optDeclared(key);
    }
  }

  getMessages() {
    return this.messages;
  }

  report(s: string) {
    this.messages.push(s);
  }

  printClearMessage() {
    this.messages.forEach((m) => console.log(m));
    this.messages = [];
  }

  clearMessages() {
    this.messages = [];
  }

  OKMesReturnL_Out(message: L_Node | string): L_Out {
    if (message instanceof L_Node) this.report(`OK! ${message}`);
    else this.report(message);
    return L_Out.True;
  }

  OKMesReturnBoolean(message: L_Node | string): boolean {
    if (message instanceof L_Node) this.report(`OK! ${message}`);
    else this.report(message);
    return true;
  }

  errMesReturnL_Out(s: L_Node | string): L_Out {
    this.report(`Error: ${s}`);
    return L_Out.Error;
  }

  errMesReturnBoolean(s: L_Node | string): boolean {
    this.report(`Error: ${s}`);
    return false;
  }

  printDeclFacts() {
    console.log("\n--Declared Facts--\n");

    for (const [name, declFact] of this.defs) {
      console.log(name);
      console.log(declFact);
    }
  }

  toJSON() {
    return {
      vars: Array.from(this.declaredSingletons),
      defs: Object.fromEntries(this.defs),
      facts: Object.fromEntries(this.facts),
    };
  }
}
