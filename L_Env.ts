import { DeclNode, OptNode } from "./ast";
import { StoredFact, StoredReq } from "./L_FactStorage";

export class L_Env {
  private messages: string[] = [];
  private declaredFacts = new Map<string, DeclNode>();
  // private varsMap = new Map<string, string>();
  // private fixFreeMap = new Map<string, string>();
  private declaredVars = new Set<string>();
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

  getStoredFacts(opt: OptNode): StoredFact[] | null {
    // varDeclaredNumberMap is used to store how many times a variable is declared in all visible environments
    const varsAsSet = new Set(opt.vars);
    const varDeclaredNumberMap = new Map<string, number>();
    for (const v of varsAsSet) {
      varDeclaredNumberMap.set(v, 0);
    }

    // know where the opt is declared.
    let visibleEnvLevel = -1;
    const tmp = this.whereIsOptDeclared(opt.fullName);
    if (tmp !== undefined) {
      visibleEnvLevel = tmp;
    } else {
      this.newMessage(`${opt} not declared.`);
      return null;
    }

    // get fact from every visible env
    let out: StoredFact[] = [];
    for (
      let i = 0, curEnv: L_Env = this;
      i <= visibleEnvLevel && curEnv;
      i++, curEnv = curEnv.father as L_Env
    ) {
      // update how many times a given var is declared
      for (const v of varsAsSet) {
        if (curEnv.varDeclaredAtCurrentEnv(v)) {
          const curNumber = varDeclaredNumberMap.get(v) as number;
          varDeclaredNumberMap.set(v, curNumber + 1);
        }
      }

      // get stored facts from current environment level
      const facts = curEnv.getStoredFactsFromCurrentEnv(opt.fullName);
      if (facts === undefined) continue;

      for (const fact of facts) {
        const fixedVarsAtFact = fact.getFixedVars();

        // If the var is declared at a higher level, then the fact is RELATED TO THE VARIABLE WITH THE SAME NAME AT HIGHER LEVEL, NOT RELATED WITH CURRENT VARIABLE
        let invisible = false;
        for (const v of fixedVarsAtFact) {
          if (varsAsSet.has(v) && (varDeclaredNumberMap.get(v) as number) > 1) {
            invisible = true;
            break;
          }
        }

        if (invisible) continue;
        else out.push(fact);
      }

      // const facts = curEnv.getStoredFactsFromCurrentEnv(opt.fullName);
      // if (facts === undefined) continue;
      // else out = [...out, ...facts];
    }

    return out;
  }

  // Return the lowest level of environment in which an operator with given name is declared.
  private whereIsOptDeclared(s: string): number | undefined {
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
      this.declaredFacts.has(fix)
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

  // getVar(key: string, includesFather: Boolean = true): undefined | string {
  //   const out = this.varsMap.get(key);
  //   if (out) return out;
  //   else if (includesFather) return this.father?.getVar(key, true);
  // }

  // getVarFromCurrentEnv(key: string) {
  //   return this.fixFreeMap.get(key);
  //   // return this.varsMap.get(key);
  // }

  varDeclaredAtCurrentEnv(key: string) {
    return this.declaredVars.has(key);
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
}
