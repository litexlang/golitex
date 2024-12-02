import { ToCheckNode } from "./L_Nodes";

export type L_Symbol = string;

export enum L_Out {
  Error,
  True,
  False,
  Unknown,
}

export type ExampleItem = {
  name: string;
  code: string[];
  debug: boolean;
  print: boolean;
};

export class KnownExist {
  constructor(public isT: boolean) {}
}

export class KnownFact {
  facts: StoredFact[] = []; // facts at current if-then level.
  children = new Map<number, KnownFact>();

  constructor() {}

  addChild(checkVarsNumLst: number[], fact: StoredFact): boolean {
    try {
      if (checkVarsNumLst.length === 0) {
        this.facts.push(fact);
        return true;
      } else {
        const child = this.children.get(checkVarsNumLst[0]);
        if (child === undefined) {
          const newChild = new KnownFact();
          this.children.set(checkVarsNumLst[0], newChild);
          checkVarsNumLst.shift();
          return newChild.addChild(checkVarsNumLst, fact);
        } else {
          checkVarsNumLst.shift();
          return child.addChild(checkVarsNumLst, fact);
        }
      }
    } catch {
      return false;
    }
  }

  getFactsToCheck(checkVarsNumLst: number[]): StoredFact[] | undefined {
    try {
      if (checkVarsNumLst.length === 0) {
        return this.facts;
      } else {
        const index = checkVarsNumLst.shift();
        const child = this.children.get(index as number);
        return child?.getFactsToCheck(checkVarsNumLst);
      }
    } catch {
      return undefined;
    }
  }

  toString(indent: string = ""): string {
    let result = indent + "facts: " + this.facts.toString() + "\n";
    if (!Array.isArray(this.facts)) {
      this.children.forEach((child) => {
        result += child.toString(indent + "  ");
      });
    }
    return result;
  }
}

export class StoredReq {
  constructor(
    public vars: string[], // store free vars at current level
    public req: ToCheckNode[]
  ) {}

  toString() {
    return `(if ${this.vars.join(", ")} : ${this.req
      .map((e) => e.toString())
      .join(", ")})`;
  }

  fixReqVars(map: Map<string, string>): StoredReq {
    const newReq = this.req.map((e) => e.useMapToCopy(map));
    return new StoredReq(this.vars, newReq);
  }
}

export class StoredFact {
  constructor(
    public vars: string[], // stored fixed, only used when storing opts
    public req: StoredReq[], // when adding a new layer of if-then, push a new req list (ToCheckNode[]) at end of req.
    public isT: boolean
  ) {}

  fixStoredFact(map: Map<string, string>): StoredFact {
    const newReq: StoredReq[] = [];
    for (const r of this.req) {
      newReq.push(r.fixReqVars(map));
    }
    return new StoredFact(this.vars, newReq, this.isT);
  }

  getVarsToCheck(): string[][] {
    return this.req.map((e) => e.vars);
  }

  toString() {
    const notWords = this.isT === false ? "[not] " : "";
    const varsWords = this.vars.length > 0 ? this.vars.join(", ") : "";
    const reqWords =
      this.req.length > 0
        ? " <= " + this.req.map((e) => e.toString()).join(", ")
        : "";

    const out = notWords + varsWords + reqWords;

    return out;
  }

  getAllFreeVars(): string[] {
    const varsLst: string[][] = this.req.map((e) => e.vars);
    let out: string[] = [];
    varsLst.forEach((e) => {
      out = [...out, ...e];
    });
    return out;
  }

  getFixedVars() {
    const out = [];
    const frees = this.getAllFreeVars();
    for (const v of this.vars) {
      if (!frees.includes(v)) out.push(v);
    }
    return out;
  }

  isNoReq(): boolean {
    for (const req of this.req) {
      if (req.req.length !== 0) return false;
    }
    return true;
  }

  checkLiterally(toCheckFixedVars: string[], isT: boolean): L_Out {
    const noExtraReq = this.req.every((e) => e.req.length === 0);
    if (!noExtraReq) return L_Out.Unknown;

    if (isT !== this.isT) return L_Out.Unknown;

    //! the following check is based on hypothesis that toCheckFixedVars declared at different level are different
    const frees = this.getAllFreeVars();
    for (const [i, v] of toCheckFixedVars.entries()) {
      if (frees.includes(v)) continue;
      else if (toCheckFixedVars[i] === this.vars[i]) continue;
      else return L_Out.Unknown;
    }

    return L_Out.True;
  }
}
