import {
  ShortCallOptNode,
  FactNode,
  ExistNode,
  DeclNode,
  DefDeclNode,
  IfThenDeclNode,
  OnlyIfDeclNode,
} from "./ast";
export class StoredFactValue {
  constructor(
    public vars: string[],
    public req: FactNode[],
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
  private shortOptFacts = new Map<string, StoredFactValue[]>();
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
  getShortOptFact(s: string): StoredFactValue[] | undefined {
    let out = this.shortOptFacts.get(s);
    return out ? out : this.father?.getShortOptFact(s);
  }

  addShortOptFact(opt: ShortCallOptNode, req: FactNode[]) {
    if (this.shortOptFacts.get(opt.fullName) === undefined) {
      this.shortOptFacts.set(opt.fullName, [
        new StoredFactValue(opt.vars, req, opt.isT),
      ]);
    } else {
      this.shortOptFacts
        .get(opt.fullName)!
        .push(new StoredFactValue(opt.vars, req, opt.isT));
    }
  }

  declareNewVar(v: string[]): boolean {
    if (v.every(this.varsAreNotDeclared, this)) {
      this.declaredVars.push(...v);
      return true;
    }

    return false;
  }

  varsAreNotDeclared(vars: string[] | string): boolean {
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

    for (const [key, factUnderCurKey] of this.shortOptFacts) {
      const t = this.declaredFacts.get(key);
      let tStr = "";
      if (t instanceof DefDeclNode) {
        tStr = "def";
      } else if (t instanceof IfThenDeclNode) {
        tStr = "if-then";
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
