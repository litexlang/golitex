import {
  OptNode,
  FactNode,
  ExistNode,
  DeclNode,
  IffDeclNode,
  IfThenDeclNode,
  OnlyIfDeclNode,
} from "./ast";
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

    if (!this.isT) {
      result = "[not] " + result;
    }

    return result;
  }
}

export class L_Env {
  private declaredVars: string[] = [];
  private messages: string[] = [];
  private OptFacts = new Map<string, StoredFactValue[]>();
  private declaredFacts = new Map<string, DeclNode>();

  constructor(private father: L_Env | undefined = undefined) {
    this.father = father;
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

  // get from itself and father
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
    if (this.declaredVars.includes(v) || v.startsWith("#")) {
      return true;
    }
    return this.father ? this.father.isVarDeclared(v) : false;
  }

  newMessage(s: string) {
    this.messages.push(s);
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
