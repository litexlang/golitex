import {
  DefNode,
  ToCheckNode,
  LogicNode,
  OptNode,
  ExistDefNode,
} from "./L_Nodes.ts";
import { RType } from "./L_Executor.ts";
import { StoredFact, StoredReq } from "./L_Memory.ts";
import { MemorizedExistDecl } from "./L_Memory.ts";

export class L_Env {
  private messages: string[] = [];
  private declaredVars = new Set<string>();

  private declaredFacts = new Map<string, DefNode>();
  private storage = new Map<string, StoredFact[]>();

  private haves = new Set<string>();

  private bys = new Map<string, StoredFact>();
  // private existFactMemory = new Map<string, OneLayerStoredFact[]>();
  private declaredExist = new Map<string, MemorizedExistDecl>();

  // private exists = new Map<string, StoredFact[]>();

  constructor(private father: L_Env | undefined = undefined) {
    this.father = father;
  }

  declNewExist(decl: ExistDefNode): boolean {
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

  // TODO: IF THE BY IS RELATED TO OPT WITH THE SAME NAME AT HIGHER LEVEL, WE SHOULD NOT RETURN IT. FOR
  // TODO: THE TIME BEING, WE DON'T IMPLEMENT THAT PROTECTION.
  getBy(s: string): undefined | StoredFact {
    const out = this.bys.get(s);
    if (out !== undefined) return out;
    else if (this.father === undefined) return undefined;
    else return this.father.getBy(s);
  }

  setBy(s: string, by: StoredFact) {
    const out = this.bys.get(s);
    if (!out) this.bys.set(s, by);
    else throw Error(`By name ${s} is already occupied.`);
  }

  inHaves(name: string): boolean {
    if (this.haves.has(name)) return true;
    else if (this.declaredFacts.has(name))
      return false; // means the opt is declared at current environment and haves above is invisible.
    else if (this.father) return this.father?.inHaves(name);
    else return false;
  }

  newHave(name: string) {
    return this.haves.add(name);
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

  safeDeclOpt(s: string, DefNode: DefNode): boolean {
    // REMARK: YOU ARE NOT ALLOWED TO DECLARE A FACT TWICE AT THE SAME ENV.
    if (this.declaredFacts.get(s) !== undefined) {
      this.newMessage(
        `${s} already declared in this environment or its fathers environments.`
      );
      return false;
    }

    this.declaredFacts.set(s, DefNode);
    return true;
  }

  safeNewVar(fix: string): boolean {
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

  printBys() {
    console.log("\n-----Bys-----\n");
    for (const [defName, by] of this.bys) {
      console.log(defName);
      console.log(`${by}\n`);
    }
  }

  // printExists() {
  //   console.log("\n----Exists----\n");
  //   for (const [existName, exist] of this.exists) {
  //     console.log(existName);
  //     console.log(`${exist}\n`);
  //   }
  // }

  onFail(m: string, t: RType = RType.Error, err: unknown = null): RType {
    if (err instanceof Error) this.newMessage(err.message);
    this.newMessage(m);
    return t;
  }
}
