import {
  OptNode,
  FactNode,
  ExistNode,
  DeclNode,
  IffDeclNode,
  IfThenDeclNode,
  OnlyIfDeclNode,
  IfThenNode,
} from "./ast";
import { L_Storage } from "./L_Storage";
export class StoredFactValue {
  constructor(
    public vars: string[], //! vars here never start with #
    public req: FactNode[], //! vars here might start with #
    public isT: Boolean = false
  ) {}

  toString() {
    let result = "";
    result += this.vars.join(", ");
    if (this.req.length > 0) {
      result += " | ";
      result += this.req.map((e) => e.toString()).join("; ");
    }
    if (!this.isT) result = "[not] " + result;
    return result;
  }
}

export class L_Env {
  // private declaredVars: string[] = [];
  private messages: string[] = [];
  // private OptFacts = new Map<string, StoredFactValue[]>();
  private declaredFacts = new Map<string, DeclNode>();

  // public storedFacts = new Map<string, L_Storage.StoredFact[]>();
  private varsMap = new Map<string, string>();

  private storage = new Map<string, L_Storage.StoredFact[]>();

  constructor(private father: L_Env | undefined = undefined) {
    this.father = father;
  }

  pushIntoStorage(
    name: string,
    vars: string[],
    req: L_Storage.StoredReq[],
    isT: Boolean
  ) {
    const newFact = new L_Storage.StoredFact(vars, req, isT);
    const out = this.storage.get(name);
    if (!out) {
      this.storage.set(name, [newFact]);
    } else {
      out.push(newFact);
    }
  }

  printAllStoredFacts() {
    console.log(`\n---Stored Facts---\n`);
    for (const [s, v] of this.storage.entries()) {
      console.log(`[${s}]`);
      v?.forEach((e) => console.log(e));
      if (v.length >= 0) console.log();
    }
  }

  getStoredFactsFromAllLevels(s: string): L_Storage.StoredFact[] {
    let out: L_Storage.StoredFact[] = [];
    let curEnv: L_Env | undefined = this;
    while (curEnv) {
      const facts = curEnv.storage.get(s);
      if (facts !== undefined)
        out = [...out, ...(facts as L_Storage.StoredFact[])];
      curEnv = curEnv.father;
    }
    return out;
  }

  //
  // getDeclFact(s: string) {
  //   let out = this.declaredFacts.get(s);
  //   return out ? out : this.father?.declaredFacts.get(s);
  // }

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

  fixFrees(
    frees: string[],
    fixed: string[],
    includesFather: Boolean = true
  ): null | Boolean {
    //! TODO: I SHOULD ALLOW different length
    if (frees.length !== fixed.length) return null;

    for (const [i, v] of frees.entries()) {
      const stored = this.getVar(v, includesFather);
      if (stored === undefined) {
        this.newVar(v, fixed[i]);
      } else {
        if (stored !== fixed[i]) return null;
      }
    }

    return true;
  }

  getVar(key: string, includesFather: Boolean = true): undefined | string {
    // TODO: THERE SHOULD NEVER BE A # OUT
    if (key.startsWith("#")) key = key.slice(1);
    const out = this.varsMap.get(key);
    if (out) return out;
    else if (includesFather) return this.father?.getVar(key);
  }

  newMessage(s: string) {
    this.messages.push(s);
  }

  getAllMessages() {
    return this.messages;
  }

  printClearMessage() {
    this.messages.forEach((m) => console.log(m));
    this.messages = [];
  }

  // printFacts() {
  //   console.log("\n-----facts-------\n");

  //   for (const [key, factUnderCurKey] of this.OptFacts) {
  //     const t = this.declaredFacts.get(key);
  //     let tStr = "";
  //     if (t instanceof IffDeclNode) {
  //       tStr = "iff";
  //     } else if (t instanceof IfThenDeclNode) {
  //       tStr = "if";
  //     } else if (t instanceof ExistNode) {
  //       tStr = "exist";
  //     } else if (t instanceof OnlyIfDeclNode) {
  //       tStr = "only_if";
  //     }

  //     console.log(`[${tStr}] ${key}`);
  //     factUnderCurKey.forEach((e: StoredFactValue) => {
  //       console.log(e.toString());
  //     });
  //     console.log();
  //   }
  // }

  printDeclFacts() {
    console.log("\n--Declared Facts--\n");

    for (const [name, declFact] of this.declaredFacts) {
      console.log(declFact);
    }
  }
}
