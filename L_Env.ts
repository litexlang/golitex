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
import { L_Saver } from "./L_Saver";
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
  private declaredVars: string[] = [];
  private messages: string[] = [];
  private OptFacts = new Map<string, StoredFactValue[]>();
  private declaredFacts = new Map<string, DeclNode>();

  // public storedFacts = new Map<string, L_Saver.StoredFact[]>();
  private freeFixMap = new Map<string, string>();

  public storage = new Map<string, L_Saver.StoredFact[]>();

  constructor(private father: L_Env | undefined = undefined) {
    this.father = father;
  }

  pushIntoStorage(
    name: string,
    vars: string[],
    req: L_Saver.StoredReq[],
    isT: Boolean
  ) {
    const newFact = new L_Saver.StoredFact(vars, req, isT);
    const out = this.storage.get(name);
    if (!out) {
      this.storage.set(name, [newFact]);
    } else {
      out.push(newFact);
    }
  }

  getStoredFactsFromAllLevels(s: string): L_Saver.StoredFact[] {
    let out: L_Saver.StoredFact[] = [];
    let curEnv: L_Env | undefined = this;
    while (curEnv) {
      const facts = curEnv.storage.get(s);
      if (facts !== undefined)
        out = [...out, ...(facts as L_Saver.StoredFact[])];
      curEnv = curEnv.father;
    }
    return out;
  }

  newFreeFix(free: string, fix: string) {
    this.freeFixMap.set(free, fix);
  }

  getFather(): L_Env | undefined {
    return this.father;
  }

  // get from itself and father
  getDeclFact(s: string) {
    let out = this.declaredFacts.get(s);
    return out ? out : this.father?.declaredFacts.get(s);
  }

  setDeclFact(s: string, declNode: DeclNode) {
    this.declaredFacts.set(s, declNode);
  }

  // getStoredFacts(s: string): L_Saver.StoredFact[] | undefined {
  //   let curEnv: L_Env | undefined = this;
  //   let out: L_Saver.StoredFact[] = [];
  //   while (curEnv !== undefined) {
  //     const facts = curEnv.storedFacts.get(s);
  //     if (facts !== undefined) {
  //       out = out.concat(facts);
  //     }
  //     curEnv = curEnv.father;
  //   }
  //   return out;
  // }

  // storeFact(
  //   name: string,
  //   vars: string[],
  //   req: FactNode[],
  //   isT: Boolean = true,
  //   freeVars: string[]
  // ): L_Saver.StoredFact | null {
  //   try {
  //     if (this.storedFacts.get(name) === undefined) {
  //       // ! Currently does not examine whether an operator is declared
  //       const out = new L_Saver.StoredFact(vars, req, isT, freeVars);
  //       this.storedFacts.set(name, [out]);
  //       return out;

  // if (this.declaredFacts.get(name)) {
  //   const out = new L_Saver.StoredFact(vars, req, isT, freeVars);
  //   this.storedFacts.set(name, [out]);
  //   return out;
  // } else {
  //   this.newMessage(`${name} not declared.`);
  //   return null;
  // }
  //     } else {
  //       const out = new L_Saver.StoredFact(vars, req, isT, freeVars);
  //       this.storedFacts.get(name)!.push(out);
  //       return out;
  //     }
  //   } catch (error) {
  //     this.newMessage(`failed to store fact about ${name}.`);
  //     return null;
  //   }
  // }

  // get from itself and father
  //? To be removed
  getOptFact(s: string): StoredFactValue[] | undefined {
    let out = this.OptFacts.get(s);
    return out ? out : this.father?.getOptFact(s);
  }

  addOptFact(opt: OptNode, req: FactNode[]) {
    if (this.OptFacts.get(opt.fullName) === undefined) {
      this.OptFacts.set(opt.fullName, [
        new StoredFactValue(opt.vars, req, opt.isT),
      ]);
    } else {
      this.OptFacts.get(opt.fullName)!.push(
        new StoredFactValue(opt.vars, req, opt.isT)
      );
    }
  }

  declareNewVar(v: string[]): boolean {
    if (this.varsAreNotDeclared(v)) {
      this.declaredVars.push(...v);
      return true;
    }

    return false;
  }

  newVar(free: string, fix: string) {
    this.freeFixMap.set(free, fix);
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
    const out = this.freeFixMap.get(key);
    if (out) return out;
    else if (includesFather) return this.father?.getVar(key);
  }

  varsAreNotDeclared(vars: string[]): boolean {
    const isVarDeclared = (v: string): boolean => {
      if (this.declaredVars.includes(v) || v.startsWith("#")) {
        return true;
      }
      return this.father ? this.father.isVarDeclared(v) : false;
    };

    if (Array.isArray(vars)) {
      return vars.every((v) => !isVarDeclared(v));
    } else {
      return !isVarDeclared(vars);
    }
  }

  private isVarDeclared(v: string): boolean {
    if (this.declaredVars.includes(v) || v.startsWith("#")) return true;
    return this.father ? this.father.isVarDeclared(v) : false;
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

  printFacts() {
    console.log("\n-----facts-------\n");

    for (const [key, factUnderCurKey] of this.OptFacts) {
      const t = this.declaredFacts.get(key);
      let tStr = "";
      if (t instanceof IffDeclNode) {
        tStr = "iff";
      } else if (t instanceof IfThenDeclNode) {
        tStr = "if";
      } else if (t instanceof ExistNode) {
        tStr = "exist";
      } else if (t instanceof OnlyIfDeclNode) {
        tStr = "only_if";
      }

      console.log(`[${tStr}] ${key}`);
      factUnderCurKey.forEach((e: StoredFactValue) => {
        console.log(e.toString());
      });
      console.log();
    }
  }

  printDeclFacts() {
    console.log("\n--Declared Facts--\n");

    for (const [name, declFact] of this.declaredFacts) {
      console.log(declFact);
    }
  }
}
