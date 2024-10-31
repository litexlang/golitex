import { DeclNode } from "./ast";
import { L_Storage, StoredFact, StoredReq } from "./L_Storage";

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

  getStoredFactsFromAllLevels(s: string): StoredFact[] {
    let out: StoredFact[] = [];
    let curEnv: L_Env | undefined = this;
    while (curEnv) {
      const facts = curEnv.storage.get(s);
      if (facts !== undefined) out = [...out, ...(facts as StoredFact[])];
      curEnv = curEnv.father;
    }
    return out;
  }

  isOptDeclared(s: string) {
    let out = this.declaredFacts.get(s);
    return (out ? out : this.father?.declaredFacts.get(s)) !== undefined;
  }

  setDeclFact(s: string, declNode: DeclNode) {
    this.declaredFacts.set(s, declNode);
  }

  newVar(free: string, fix: string) {
    this.varsMap.set(free, fix);
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
