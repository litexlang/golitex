import { L_ReportBoolErr } from "./L_Messages";
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
import { L_KnownFact, L_OptSymbol, L_Out, L_Singleton } from "./L_Structs";

export class L_Env {
  private parent: L_Env | undefined = undefined;
  private messages: string[] = [];
  private declaredSingletons = new Set<string>();
  private defs = new Map<string, DefNode>();
  private facts = new Map<string, L_KnownFact[]>();
  private declaredComposites = new Map<string, DefCompositeNode>();
  private letsVars = new Map<string, L_Nodes.LetsNode>();

  constructor(parent: L_Env | undefined = undefined) {
    this.parent = parent;
  }

  newCompositeVar(key: string, fact: DefCompositeNode): boolean {
    if (this.declaredComposites.get(key)) {
      return L_ReportBoolErr(
        this,
        this.newCompositeVar,
        `The variable "${key}" is already declared in this environment or its parent environments. Please use a different name.`
      );
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

  getFacts(key: string): undefined | L_KnownFact[] {
    let currentFacts = this.facts.get(key);

    if (currentFacts === undefined) {
      if (this.parent !== undefined) {
        return this.parent.getFacts(key);
      } else {
        return undefined;
      }
    } else {
      const fromParent = this.parent?.getFacts(key);
      if (fromParent === undefined) {
        return currentFacts;
      } else {
        return [...currentFacts, ...fromParent];
      }
    }
  }

  clear() {
    this.parent = undefined;
    this.messages = [];
    this.declaredSingletons = new Set<string>();
    this.letsVars = new Map<string, L_Nodes.LetsNode>();
    this.defs = new Map<string, DefNode>();
  }

  // two ways of checking : 1. it's letsVar name 2. it satisfies regex of a var
  isLetsVar(varStr: string): boolean {
    if (this.letsVars.has(varStr)) {
      return true;
    }

    for (const knownLet of this.letsVars.values()) {
      if (knownLet.regex.test(varStr)) return true;
    }

    if (this.parent !== undefined) {
      return this.parent.isLetsVar(varStr);
    } else return false;
  }

  newLetsVars(letsNode: L_Nodes.LetsNode) {
    this.letsVars.set(letsNode.name, letsNode);
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
      return L_ReportBoolErr(
        this,
        this.newDef,
        `The variable "${s}" is already declared in this environment or its parent environments. Please use a different name.`
      );
    }

    this.defs.set(s, DefNode);
    this.report(`[def] ${DefNode}`);
    return true;
  }

  newSingletonVar(fix: string): boolean {
    // TO MAKE MY LIFE EASIER SO THAT I DO NOT NEED TO BIND ENV TO VARIABLE, I forbid redefining a variable with the same name with any visible variable.
    if (this.isSingletonDeclared(fix)) {
      return L_ReportBoolErr(
        this,
        this.newSingletonVar,
        `The variable "${fix}" is already declared in this environment or its parent environments. Please use a different name.`
      );
    }
    this.declaredSingletons.add(fix);
    return true;
  }

  isSingletonDeclared(key: string): boolean {
    if (this.declaredSingletons.has(key) || this.isLetsVar(key)) {
      return true;
    } else {
      if (!this.parent) return false;
      else return this.parent.isSingletonDeclared(key);
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

  getLetsVar(varStr: string): L_Nodes.LetsNode | undefined {
    if (this.letsVars.has(varStr)) {
      return this.letsVars.get(varStr);
    }

    for (const knownLet of this.letsVars.values()) {
      if (knownLet.regex.test(varStr)) return knownLet;
    }

    if (this.parent !== undefined) {
      return this.parent.getLetsVar(varStr);
    } else return undefined;
  }
}
