import { DeclNode, OptNode } from "./ast";
import { StoredFact, StoredReq } from "./L_Storage";

export class L_Env {
  private messages: string[] = [];
  private declaredFacts = new Map<string, DeclNode>();
  private varsMap = new Map<string, string>();
  private storage = new Map<string, StoredFact[]>();

  constructor(private father: L_Env | undefined = undefined) {
    this.father = father;
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

  private getStoredFactsFromCurrentEnv(s: string) {
    return this.storage.get(s);
  }

  // // TODO: NEED TO BE REFACTORED SO THAT FACTS WITH THE SAME NAME DECLARED OR STORED WON'T GO WRONG.
  // getStoredFactsFromAllLevels(s: string): StoredFact[] {
  //   let out: StoredFact[] = [];
  //   let curEnv: L_Env | undefined = this;
  //   while (curEnv) {
  //     const facts = curEnv.storage.get(s);
  //     if (facts !== undefined) out = [...out, ...(facts as StoredFact[])];
  //     curEnv = curEnv.father;
  //   }
  //   return out;
  // }

  getStoredFacts(opt: OptNode): StoredFact[] | undefined {
    let visibleEnvLevel = -1;
    let highestVisibleEnv: L_Env | undefined = undefined;

    const tmp = this.whereIsOptDeclared(opt.fullName);
    if (tmp) {
      [visibleEnvLevel, highestVisibleEnv] = tmp;
    } else {
      this.newMessage(`${opt} not declared.`);
      return undefined;
    }

    // for (let i = 0; i < opt.vars.length; i++) {
    //   const tmp = this.whereIsVarDeclared(opt.vars[i]);
    //   let curLevel = 0;
    //   if (tmp) {
    //     [curLevel, highestVisibleEnv] = tmp;
    //     if (curLevel < visibleEnvLevel) visibleEnvLevel = curLevel;
    //   } else {
    //     this.newMessage(`${opt.vars[0]} not found.`);
    //     return undefined;
    //   }
    // }

    let out: StoredFact[] = [];
    for (
      let i = 0, curEnv: L_Env = this;
      i <= visibleEnvLevel && curEnv;
      i++, curEnv = curEnv.father as L_Env
    ) {
      const facts = curEnv.getStoredFactsFromCurrentEnv(opt.fullName);
      if (facts === undefined) continue;
      else out = [...out, ...facts];
    }

    return out;
  }

  private whereIsVarDeclared(s: string): [number, L_Env] | undefined {
    let curEnv: L_Env | undefined = this;
    let n = 0;

    while (curEnv && curEnv.getVar(s) === undefined) {
      n++;
      curEnv = curEnv.father;
    }

    return curEnv?.getVar(s) ? [n, curEnv] : undefined;
  }

  // Return the lowest level of environment in which an operator with given name is declared.
  private whereIsOptDeclared(s: string): [number, L_Env] | undefined {
    let curEnv: L_Env | undefined = this;
    let n = 0;

    while (curEnv && curEnv.declaredFacts.get(s) === undefined) {
      n++;
      curEnv = curEnv.father;
    }

    return curEnv?.declaredFacts.get(s) ? [n, curEnv] : undefined;
  }

  // isOptDeclaredInThisOrFathers(s: string) {
  //   let out = this.declaredFacts.get(s);
  //   return (out ? out : this.father?.declaredFacts.get(s)) !== undefined;
  // }

  safeSetDeclFact(s: string, declNode: DeclNode): Boolean {
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

  newVar(free: string, fix: string): Boolean {
    if (this.varsMap.has(free)) {
      this.newMessage(`${free} already declared.`);
      return false;
    }
    this.varsMap.set(free, fix);
    return true;
  }

  getVar(key: string, includesFather: Boolean = true): undefined | string {
    const out = this.varsMap.get(key);
    if (out) return out;
    else if (includesFather) return this.father?.getVar(key, true);
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

  printDeclFacts() {
    console.log("\n--Declared Facts--\n");

    for (const [name, declFact] of this.declaredFacts) {
      console.log(declFact);
    }
  }
}
