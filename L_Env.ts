import {
  DefNode,
  L_Node,
  LogicNode,
  MacroNode,
  OptNode,
  ToCheckNode,
} from "./L_Nodes";
import {
  examineStoredFact,
  KnownExist,
  KnownFact,
  StoredFact,
} from "./L_Memory";
import { L_Out } from "./L_Executor";
import { isToCheckBuiltin } from "./L_Builtins";

export class L_Env {
  private parent: L_Env | undefined = undefined;
  private messages: string[] = [];
  private declaredVars = new Set<string>();
  private macros: MacroNode[] = [];
  private defs = new Map<string, DefNode>();
  private knownFacts = new Map<string, KnownFact>();
  private namedKnownToChecks = new Map<string, ToCheckNode>();
  private exists = new Map<string, KnownExist>();

  constructor(parent: L_Env | undefined = undefined) {
    this.parent = parent;
  }

  clear() {
    this.parent = undefined;
    this.messages = [];
    this.declaredVars = new Set<string>();
    this.macros = [];
    this.defs = new Map<string, DefNode>();
    this.knownFacts = new Map<string, KnownFact>();
    this.namedKnownToChecks = new Map<string, ToCheckNode>();
    this.exists = new Map<string, KnownExist>();
  }

  newExist(optName: string, exist: KnownExist): boolean {
    this.exists.set(optName, exist);
    return true;
  }

  isExisted(optName: string): boolean {
    if (this.exists.get(optName)?.isT === true) {
      return true;
    } else if (this.parent !== undefined) {
      return this.parent.isExisted(optName);
    } else {
      return false;
    }
  }

  newNamedKnownToCheck(name: string, toCheck: ToCheckNode): boolean {
    const out = this.getNamedKnownToCheck(name);
    if (out === undefined) {
      this.namedKnownToChecks.set(name, toCheck);
      return true;
    } else {
      return this.errMesReturnBoolean(
        `${name} is already a known fact. You can not double declare it.`,
      );
    }
  }

  getNamedKnownToCheck(name: string): ToCheckNode | undefined {
    const known = this.namedKnownToChecks.get(name);
    if (known !== undefined) return known;
    else if (this.parent !== undefined) {
      return this.parent.getNamedKnownToCheck(name);
    } else return undefined;
  }

  getKnownFactsFromCurEnv(
    opt: OptNode,
    onlyRoot: boolean = false,
  ): undefined | StoredFact[] {
    const knownNodeRoot: KnownFact | undefined = this.knownFacts.get(opt.name);

    if (onlyRoot) {
      return knownNodeRoot?.getFactsToCheck([]);
    }

    if (knownNodeRoot !== undefined) {
      if (opt.checkVars === undefined) return knownNodeRoot.getFactsToCheck([]);
      else {
        const varsToCheckNumbers = opt.checkVars?.map((e) => e.length);
        if (varsToCheckNumbers === undefined) return undefined;
        return knownNodeRoot.getFactsToCheck(varsToCheckNumbers);
      }
    } else {
      return undefined;
    }
  }

  newKnownFact(
    optName: string,
    checkVars: string[][],
    fact: StoredFact,
  ): boolean {
    const ok = examineStoredFact(this, new OptNode(optName, fact.vars), fact);
    if (!ok) return false;

    const checkVarsNumLst = checkVars.map((e) => e.length);
    const knownFact = this.knownFacts.get(optName);
    if (knownFact === undefined) {
      const newKnownFact = new KnownFact();
      this.knownFacts.set(optName, newKnownFact);

      return newKnownFact.addChild(checkVarsNumLst, fact);
    } else {
      return knownFact.addChild(checkVarsNumLst, fact);
    }
  }

  getMacros(previous: MacroNode[]): MacroNode[] {
    previous = [...previous, ...this.macros];
    if (this.parent !== undefined) {
      return this.parent.getMacros(previous);
    } else {
      return previous;
    }
  }

  newMacro(macroNode: MacroNode) {
    this.macros.push(macroNode);
  }

  factsInToCheckAllDeclared(node: ToCheckNode): boolean {
    if (node instanceof OptNode) {
      return this.getDef(node.name) !== undefined || isToCheckBuiltin(node);
    } else if (node instanceof LogicNode) {
      return node.req.every((e) => this.factsInToCheckAllDeclared(e)) &&
        node.onlyIfs.every((e) => this.factsInToCheckAllDeclared(e));
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
      this.newMessage(
        `${s} already declared in this environment or its parents environments.`,
      );
      return false;
    }

    this.defs.set(s, DefNode);
    this.newMessage(`[def] ${DefNode}`);
    return true;
  }

  // Return the lowest level of environment in which an operator with given name is declared.
  public whereIsOptDeclared(s: string): number | undefined {
    if (this.defs.get(s)) return 0;

    let curEnv: L_Env | undefined = this.parent;
    let n = 1;

    while (curEnv && curEnv.defs.get(s) === undefined) {
      n++;
      curEnv = curEnv.parent;
    }

    return curEnv?.defs.get(s) ? n : undefined;
  }

  newVar(fix: string): boolean {
    // TO MAKE MY LIFE EASIER SO THAT I DO NOT NEED TO BIND ENV TO VARIABLE, I forbid redefining a variable with the same name with any visible variable.
    if (this.varDeclared(fix)) {
      this.newMessage(`${fix} already declared.`);
      return false;
    }
    this.declaredVars.add(fix);
    return true;
  }

  varDeclaredAtCurrentEnv(key: string) {
    return this.declaredVars.has(key);
  }

  varDeclared(key: string): boolean {
    if (this.declaredVars.has(key)) {
      return true;
    } else {
      if (!this.parent) return false;
      else return this.parent.varDeclared(key);
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

  newMessage(s: string) {
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
    if (message instanceof L_Node) this.newMessage(`OK! ${message}`);
    else this.newMessage(message);
    return L_Out.True;
  }

  OKMesReturnBoolean(message: L_Node | string): boolean {
    if (message instanceof L_Node) this.newMessage(`OK! ${message}`);
    else this.newMessage(message);
    return true;
  }

  errMesReturnL_Out(s: L_Node | string): L_Out {
    this.newMessage(`Error: ${s}`);
    return L_Out.Error;
  }

  errMesReturnBoolean(s: L_Node | string): boolean {
    this.newMessage(`Error: ${s}`);
    return false;
  }

  printDeclFacts() {
    console.log("\n--Declared Facts--\n");

    for (const [name, declFact] of this.defs) {
      console.log(name);
      console.log(declFact);
    }
  }

  getParent() {
    return this.parent;
  }

  toJSON() {
    return {
      vars: Array.from(this.declaredVars),
      defs: Object.fromEntries(this.defs),
      knowns: Object.fromEntries(this.knownFacts),
      macros: this.macros,
    };
  }

  // used by prove to check whether vars in factToCheck is redefined in block
  someVarsDeclaredHere(fact: ToCheckNode, freeVars: string[]): boolean {
    if (fact instanceof OptNode) {
      const out = fact.vars.some(
        (e) => !freeVars.includes(e) && this.declaredVars.has(e),
      );
      return out;
    } else if (fact instanceof LogicNode) {
      return (
        fact.onlyIfs.some((e) => this.someVarsDeclaredHere(e, fact.vars)) ||
        fact.req.some((e) => this.someVarsDeclaredHere(e, fact.vars))
      );
    }

    throw Error();
  }

  // used by prove to check whether factToCheck is redefined in block
  someOptsDeclaredHere(fact: ToCheckNode): boolean {
    if (fact instanceof OptNode) {
      return this.defs.get(fact.name) !== undefined;
    } else if (fact instanceof LogicNode) {
      return (
        fact.onlyIfs.some((e) => this.someOptsDeclaredHere(e)) ||
        fact.req.some((e) => this.someOptsDeclaredHere(e))
      );
    }

    throw Error();
  }

  optDeclaredHere(name: string): boolean {
    return this.defs.get(name) !== undefined;
  }
}
