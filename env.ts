import { ShortCallOptNode, FactNode, FactType } from "./ast";
export class StoredFactValue {
  constructor(
    public vars: string[][],
    public req: FactNode[],
    public isT: Boolean = false
  ) {}

  toString() {
    let result = "";

    result += this.vars.map((subArray) => subArray.join(", ")).join("; ");

    if (this.req.length > 0) {
      result += " | ";
      result += this.req.map((e) => e.toString()).join("; ");
    }

    if (!this.isT) {
      result = "(not) " + result;
    }

    return result;
  }
}

export class L_Env {
  private declaredVars: string[] = [];
  private messages: string[] = [];
  private shortOptFacts = new Map<string, StoredFactValue[]>();
  private factTypes = new Map<string, FactType>();

  constructor(private father: L_Env | undefined = undefined) {
    this.father = father;
  }

  getFather(): L_Env | undefined {
    return this.father;
  }

  // get from itself and father
  getOptType(s: string) {
    let out = this.factTypes.get(s);
    return out ? out : this.father?.factTypes.get(s);
  }

  setOptType(s: string, type: FactType) {
    this.factTypes.set(s, type);
  }

  // get from itself and father
  getShortOptFact(s: string): StoredFactValue[] | undefined {
    let out = this.shortOptFacts.get(s);
    return out ? out : this.father?.getShortOptFact(s);
  }

  addShortOptFact(opt: ShortCallOptNode, req: FactNode[]) {
    if (this.shortOptFacts.get(opt.fullName) === undefined) {
      this.shortOptFacts.set(opt.fullName, [
        new StoredFactValue(opt.params, req, opt.isT),
      ]);
    } else {
      this.shortOptFacts
        .get(opt.fullName)!
        .push(new StoredFactValue(opt.params, req, opt.isT));
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
      const t = this.factTypes.get(key);
      let tStr = "";
      if (t === FactType.Def) {
        tStr = "def";
      } else if (t === FactType.IfThen) {
        tStr = "if-then";
      } else if (t === FactType.Or) {
        tStr = "or";
      }

      console.log(`[${tStr}] ${key}`);
      factUnderCurKey.forEach((e: StoredFactValue) => {
        console.log(e.toString());
      });
      console.log();
    }
  }
}
