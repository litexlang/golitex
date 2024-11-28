import {
  DefNode,
  ExistDefNode,
  L_Node,
  LogicNode,
  MacroNode,
  OptNode,
  ToCheckNode,
} from "./L_Nodes.ts";
import {
  examineStoredFact,
  KnownFact,
  ReqSpace,
  StoredFact,
} from "./L_Memory.ts";
import { MemorizedExistDecl } from "./L_Memory.ts";
import { L_Out } from "./L_Executor.ts";

export class L_Env {
  private messages: string[] = [];
  private declaredVars = new Set<string>();

  private defs = new Map<string, DefNode>();

  private declaredExist = new Map<string, MemorizedExistDecl>();
  private parent: L_Env | undefined = undefined;

  private reqSpaces = new Map<string, ReqSpace>();
  private macros: MacroNode[] = [];

  private knownFacts = new Map<string, KnownFact>();
  private namedKnownToChecks = new Map<string, ToCheckNode>();

  constructor(parent: L_Env | undefined = undefined) {
    this.parent = parent;
  }

  clear() {
    this.messages = [];
    this.declaredVars = new Set<string>();

    this.defs = new Map<string, DefNode>();

    this.declaredExist = new Map<string, MemorizedExistDecl>();
    this.parent = undefined;

    this.reqSpaces = new Map<string, ReqSpace>();
    this.macros = [];

    this.knownFacts = new Map<string, KnownFact>();
  }

  newNamedKnownToChecks(name: string, toCheck: ToCheckNode): boolean {
    const out = this.getNamedKnownToChecks(name);
    if (out === undefined) {
      this.namedKnownToChecks.set(name, toCheck);
      return true;
    } else {
      return this.errIntoEnvReturnBoolean(
        `${name} is already a known fact. You can not double declare it.`,
      );
    }
  }

  getNamedKnownToChecks(name: string): ToCheckNode | undefined {
    const known = this.namedKnownToChecks.get(name);
    if (known !== undefined) return known;
    else if (this.parent !== undefined) {
      return this.parent.getNamedKnownToChecks(name);
    } else return undefined;
  }

  getKnownFactsFromCurEnv(
    opt: OptNode,
    onlyRoot: boolean = false,
  ): undefined | StoredFact[] {
    const knownNodeRoot = this.knownFacts.get(opt.name);

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

  getReqSpace(s: string): ReqSpace | undefined {
    const out = this.reqSpaces.get(s);
    if (out !== undefined) return out;
    else {
      if (this.parent) {
        return this.parent.getReqSpace(s);
      } else {
        return undefined;
      }
    }
  }

  newReqSpace(s: string, space: ReqSpace): boolean {
    if (this.reqSpaces.get(s)) return false;
    this.reqSpaces.set(s, space);
    return true;
  }

  newDeclExist(decl: ExistDefNode): boolean {
    try {
      const out = this.declaredExist.get(decl.name);
      if (out !== undefined) {
        this.newMessage(`${decl.name} already declared.`);
        return false;
      } else {
        this.declaredExist.set(decl.name, decl.toMemorized());
        return true;
      }
    } catch {
      return false;
    }
  }

  getDeclExist(s: string): MemorizedExistDecl | undefined {
    const out = this.declaredExist.get(s);
    if (out !== undefined) return out;
    else {
      if (this.parent) {
        return this.parent.getDeclExist(s);
      } else {
        return undefined;
      }
    }
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
    if (this.declaredVars.has(fix)) {
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

  OKMesIntoEnvReturnL_Out(message: L_Node | string): L_Out {
    if (message instanceof L_Node) this.newMessage(`OK! ${message}`);
    else this.newMessage(message);
    return L_Out.True;
  }

  OKMesIntoEnvReturnBoolean(message: L_Node | string): boolean {
    if (message instanceof L_Node) this.newMessage(`OK! ${message}`);
    else this.newMessage(message);
    return true;
  }

  errIntoEnvReturnL_Out(s: L_Node | string): L_Out {
    this.newMessage(`Error: ${s}`);
    return L_Out.Error;
  }

  errIntoEnvReturnBoolean(s: L_Node | string): boolean {
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
      exists: Object.fromEntries(this.declaredExist),
      reqSpaces: Object.fromEntries(this.reqSpaces),
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
