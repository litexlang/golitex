import {
  DefNode,
  ToCheckNode,
  LogicNode,
  OptNode,
  ExistDefNode,
  MacroNode,
} from "./L_Nodes.ts";
import { ReqSpace, StoredFact, StoredReq } from "./L_Memory.ts";
import { MemorizedExistDecl } from "./L_Memory.ts";
import { RType } from "./L_Executor.ts";
import { L_Cache } from "./L_Cache.ts";

export class L_Env {
  private messages: string[] = [];
  private declaredVars = new Set<string>();

  private declaredFacts = new Map<string, DefNode>();
  private storage = new Map<string, StoredFact[]>();

  private declaredExist = new Map<string, MemorizedExistDecl>();
  private father: L_Env | undefined = undefined;

  private reqSpaces = new Map<string, ReqSpace>();
  private macros: MacroNode[] = [];

  private cache: L_Cache = new L_Cache();

  constructor(father: L_Env | undefined = undefined) {
    this.father = father;
  }

  getCache() {
    return this.cache;
  }

  getMacros() {
    return this.macros;
  }

  newMacro(macroNode: MacroNode) {
    this.macros.push(macroNode);
  }

  clear() {
    this.messages = [];
    this.declaredVars = new Set<string>();
    this.declaredFacts = new Map<string, DefNode>();
    this.storage = new Map<string, StoredFact[]>();
    this.declaredExist = new Map<string, MemorizedExistDecl>();
    this.father = undefined;
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

  getReqSpace(s: string): ReqSpace | undefined {
    const out = this.reqSpaces.get(s);
    if (out !== undefined) return out;
    else {
      if (this.father) {
        return this.father.getReqSpace(s);
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

  getDeclExist(s: string): MemorizedExistDecl | undefined {
    const out = this.declaredExist.get(s);
    if (out !== undefined) return out;
    else {
      if (this.father) {
        return this.father.getDeclExist(s);
      } else {
        return undefined;
      }
    }
  }

  getDeclaredFact(s: string): DefNode | undefined {
    if (this.declaredFacts.has(s)) {
      return this.declaredFacts.get(s);
    } else if (this.father) {
      return this.father.getDeclaredFact(s);
    } else {
      return undefined;
    }
  }

  newFact(
    name: string,
    vars: string[],
    req: StoredReq[],
    isT: boolean
  ): StoredFact {
    const newFact = new StoredFact(vars, req, isT);
    const out = this.storage.get(name);
    if (!out) {
      this.storage.set(name, [newFact]);
    } else {
      out.push(newFact);
    }

    return newFact;
  }

  public getStoredFactsFromCurrentEnv(s: string) {
    return this.storage.get(s);
  }

  // Return the lowest level of environment in which an operator with given name is declared.
  public whereIsOptDeclared(s: string): number | undefined {
    if (this.declaredFacts.get(s)) return 0;

    let curEnv: L_Env | undefined = this.father;
    let n = 1;

    while (curEnv && curEnv.declaredFacts.get(s) === undefined) {
      n++;
      curEnv = curEnv.father;
    }

    return curEnv?.declaredFacts.get(s) ? n : undefined;
  }

  newDef(s: string, DefNode: DefNode): boolean {
    // REMARK: YOU ARE NOT ALLOWED TO DECLARE A FACT TWICE AT THE SAME ENV.
    if (this.declaredFacts.get(s) !== undefined) {
      this.newMessage(
        `${s} already declared in this environment or its fathers environments.`
      );
      return false;
    }

    this.declaredFacts.set(s, DefNode);
    this.newMessage(`[def] ${DefNode}`);
    return true;
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
      if (!this.father) return false;
      else return this.father.varDeclared(key);
    }
  }

  optDeclared(key: string): boolean {
    if (this.declaredFacts.get(key)) {
      return true;
    } else {
      if (!this.father) return false;
      else return this.father.optDeclared(key);
    }
  }

  getMessages() {
    return this.messages;
  }

  newMessage(s: string) {
    this.messages.push(s);
  }

  printAllStoredFacts() {
    console.log(`\n---Stored Facts---\n`);
    for (const [s, v] of this.storage.entries()) {
      console.log(`[${s}]`);
      v?.forEach((e) => console.log(e));
      if (v.length >= 0) console.log();
    }
  }

  printClearMessage() {
    this.messages.forEach((m) => console.log(m));
    this.cache.newMessage(this.messages);
    this.messages = [];
  }

  clearMessages() {
    this.messages = [];
  }

  printDeclFacts() {
    console.log("\n--Declared Facts--\n");

    for (const [name, declFact] of this.declaredFacts) {
      console.log(name);
      console.log(declFact);
    }
  }

  getFather() {
    return this.father;
  }

  someVarsDeclaredHere(fact: ToCheckNode, freeVars: string[]): boolean {
    if (fact instanceof OptNode) {
      const out = fact.vars.some(
        (e) => !freeVars.includes(e) && this.declaredVars.has(e)
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

  someOptsDeclaredHere(fact: ToCheckNode): boolean {
    if (fact instanceof OptNode) {
      return this.declaredFacts.get(fact.name) !== undefined;
    } else if (fact instanceof LogicNode) {
      return (
        fact.onlyIfs.some((e) => this.someOptsDeclaredHere(e)) ||
        fact.req.some((e) => this.someOptsDeclaredHere(e))
      );
    }

    throw Error();
  }

  optDeclaredHere(name: string): boolean {
    return this.declaredFacts.get(name) !== undefined;
  }

  RTypeErr(message: string): RType {
    this.newMessage(message);
    return RType.Error;
  }

  boolErr(message: string): boolean {
    this.newMessage(message);
    return false;
  }

  toJSON() {
    return {
      vars: Array.from(this.declaredVars),
      defs: Object.fromEntries(this.declaredFacts),
      exists: Object.fromEntries(this.declaredExist),
      facts: Object.fromEntries(this.storage),
      reqSpaces: Object.fromEntries(this.reqSpaces),
      macros: this.macros,
    };
  }
  // const out = {
  //   vars: [],
  //   defs: {},
  //   exists: {},
  //   facts: {},
  //   reqSpaces: {},
  //   macros: [],
  // };
}
