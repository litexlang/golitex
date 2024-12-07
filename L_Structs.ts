import { lchown } from "fs";
import { L_Env } from "./L_Env";
import { L_ReportErr } from "./L_Messages";
import { ToCheckNode } from "./L_Nodes";

export abstract class L_Symbol {
  static literallyCompareVars(env: L_Env, var1: L_Symbol, var2: L_Symbol) {
    try {
      if (var1 instanceof L_Singleton && var2 instanceof L_Singleton) {
        return var1.value === var2.value;
      } else if (var1 instanceof L_Composite && var2 instanceof L_Composite) {
        // name of composite symbol must be equal
        if (var1.name !== var2.name) {
          return false;
        }

        // vars of composite symbol must be equal
        if (var1.values.length !== var2.values.length) {
          return false;
        } else {
          for (let i = 0; i < var1.values.length; i++) {
            if (
              !L_Symbol.literallyCompareVars(
                env,
                var1.values[i],
                var2.values[i]
              )
            ) {
              return false;
            }
          }
          return true;
        }
      } else {
        return false;
      }
    } catch {
      L_ReportErr(env, L_Symbol.literallyCompareVars);
    }
  }

  // 两个符号字面量结构一样，比如singleton和composite就不一样，然后composite和composite之间，需要name一样才行。任何两个singleton的类型都一样。本函数用于对于 know if x, \frac{1,2} 里面的req里，自由变量和 toCheck 的变量的形式 需要对上
  static symbolStructureEqual(
    env: L_Env,
    symbol1: L_Symbol,
    symbol2: L_Symbol
  ): boolean {
    if (symbol1 instanceof L_Singleton && symbol2 instanceof L_Singleton) {
      return true;
    } else if (
      symbol1 instanceof L_Composite &&
      symbol2 instanceof L_Composite
    ) {
      if (symbol1.name === symbol2.name) {
        for (let i = 0; i < symbol1.values.length; i++) {
          if (
            !L_Symbol.symbolStructureEqual(
              env,
              symbol1.values[i],
              symbol2.values[i]
            )
          ) {
            return false;
          }
        }
        return true;
      } else {
        return false;
      }
    } else {
      return false;
    }
  }
}

export class L_Singleton extends L_Symbol {
  constructor(public value: string) {
    super();
  }

  toString() {
    return this.value;
  }
}

export class L_Composite extends L_Symbol {
  constructor(public name: string, public values: L_Symbol[]) {
    super();
  }

  toString() {
    return `\\${this.name}{${this.values.map((e) => e.toString()).join(", ")}}`;
  }

  // the current symbol is free, use a fixed one to fix. the fixed and current symbol must be of the same structure.
  fix(env: L_Env, fixed: L_Composite): L_Composite | undefined {
    if (!L_Symbol.symbolStructureEqual(env, this, fixed)) return undefined;

    const newValues: L_Symbol[] = [];
    for (const [i, v] of this.values.entries()) {
      if (v instanceof L_Singleton) continue;
      else if (v instanceof L_Composite) {
        const newV = v.fix(env, fixed.values[i] as L_Composite);
        if (newV !== undefined) newValues.push(newV);
        else return undefined;
      }
    }

    return new L_Composite(this.name, newValues);
  }
}

export class CompositeSymbolInIfReq extends L_Composite {
  constructor(name: string, values: L_Symbol[], public newVars: L_Singleton[]) {
    super(name, values);
  }
}

export class L_OptSymbol {
  constructor(public name: string) {}

  toString() {
    return this.name;
  }
}

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
  test?: string[] | undefined;
  runTest?: boolean;
};

// export class KnownExist {
//   constructor(public isT: boolean) {}
// }

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

export class KnownExist extends KnownFact {}

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

  fixReqVars(env: L_Env, map: Map<string, string>): StoredReq {
    const newReq = this.req.map((e) => e.useMapToCopy(env, map));
    return new StoredReq(this.vars, newReq);
  }
}

export class StoredFact {
  constructor(
    public vars: string[], // stored fixed, only used when storing opts
    public req: StoredReq[], // when adding a new layer of if-then, push a new req list (ToCheckNode[]) at end of req.
    public isT: boolean
  ) {}

  fixStoredFact(env: L_Env, map: Map<string, string>): StoredFact {
    const newReq: StoredReq[] = [];
    for (const r of this.req) {
      newReq.push(r.fixReqVars(env, map));
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

export class StoredExist extends StoredFact {}

export type L_KnownFact = ToCheckNode;
