import { DeclNode, FactNode, IfThenNode, OptNode } from "./ast";
import { StoredFact, StoredReq } from "./L_FactStorage";

export class L_Env {
  private messages: string[] = [];
  private declaredFacts = new Map<string, DeclNode>();
  // private varsMap = new Map<string, string>();
  // private fixFreeMap = new Map<string, string>();
  private declaredVars = new Set<string>();
  private storage = new Map<string, StoredFact[]>();
  private haves = new Set<string>();

  constructor(private father: L_Env | undefined = undefined) {
    this.father = father;
  }

  inHaves(name: string): Boolean {
    if (this.haves.has(name)) return true;
    else if (this.declaredFacts.has(name))
      return false; // means the opt is declared at current environment and haves above is invisible.
    else if (this.father) return this.father?.inHaves(name);
    else return false;
  }

  newHave(name: string) {
    return this.haves.add(name);
  }

  newFact(name: string, vars: string[], req: StoredReq[], isT: Boolean) {
    const newFact = new StoredFact(vars, req, isT);
    const out = this.storage.get(name);
    if (!out) {
      this.storage.set(name, [newFact]);
    } else {
      out.push(newFact);
    }
  }

  public getStoredFactsFromCurrentEnv(s: string) {
    return this.storage.get(s);
  }

  // Return the lowest level of environment in which an operator with given name is declared.
  public whereIsOptDeclared(s: string): number | undefined {
    let curEnv: L_Env | undefined = this;
    let n = 0;

    while (curEnv && curEnv.declaredFacts.get(s) === undefined) {
      n++;
      curEnv = curEnv.father;
    }

    return curEnv?.declaredFacts.get(s) ? n : undefined;
  }

  safeDeclOpt(s: string, declNode: DeclNode): Boolean {
    // REMARK: YOU ARE NOT ALLOWED TO DECLARE A FACT TWICE AT THE SAME ENV.
    if (this.declaredFacts.get(s) !== undefined) {
      this.newMessage(
        `${s} already declared in this environment or its fathers environments.`
      );
      return false;
    }

    this.declaredFacts.set(s, declNode);
    return true;
  }

  safeNewVar(fix: string): Boolean {
    if (
      // this.varsMap.has(free)
      //  ||
      this.declaredVars.has(fix)
      //  this.fixFreeMap.has(fix)
    ) {
      this.newMessage(`${fix} already declared.`);
      return false;
    }
    // this.varsMap.set(free, fix);

    // this.fixFreeMap.set(fix, free);
    this.declaredVars.add(fix);
    return true;
  }

  varDeclaredAtCurrentEnv(key: string) {
    return this.declaredVars.has(key);
  }

  varDeclared(key: string): Boolean {
    if (this.declaredVars.has(key)) {
      return true;
    } else {
      if (!this.father) return false;
      else return this.father.varDeclared(key);
    }
  }

  optDeclared(key: string): Boolean {
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
    this.messages = [];
  }

  clearMessages() {
    this.messages = [];
  }

  printDeclFacts() {
    console.log("\n--Declared Facts--\n");

    for (const [name, declFact] of this.declaredFacts) {
      console.log(declFact);
    }
  }

  getFather() {
    return this.father;
  }

  someVarsDeclaredHere(fact: FactNode, freeVars: string[]): Boolean {
    if (fact instanceof OptNode) {
      const out = fact.vars.some(
        (e) => !freeVars.includes(e) && this.declaredVars.has(e)
      );
      return out;
    } else if (fact instanceof IfThenNode) {
      return (
        fact.onlyIfs.some((e) => this.someVarsDeclaredHere(e, fact.vars)) ||
        fact.req.some((e) => this.someVarsDeclaredHere(e, fact.vars))
      );
    }

    throw Error();
  }

  someOptsDeclaredHere(fact: FactNode): Boolean {
    if (fact instanceof OptNode) {
      return this.declaredFacts.get(fact.fullName) !== undefined;
    } else if (fact instanceof IfThenNode) {
      return (
        fact.onlyIfs.some((e) => this.someOptsDeclaredHere(e)) ||
        fact.req.some((e) => this.someOptsDeclaredHere(e))
      );
    }

    throw Error();
  }
}
