import { L_Env } from "./L_Env";
import { L_ReportErr } from "./L_Report";
import { ToCheckNode } from "./L_Nodes";

export abstract class L_Symbol {
  abstract getRootSingletons(): L_Singleton[];

  // getDeclaredAndUndeclaredRootSingletons(env: L_Env): {
  //   declared: L_Singleton[];
  //   undeclared: L_Singleton[];
  // } {
  //   const allRootSingletons = this.getRootSingletons();
  //   const declared: L_Singleton[] = [];
  //   const undeclared: L_Singleton[] = [];
  //   for (const root of allRootSingletons) {
  //     if (env.isSingletonDeclared(root.value)) {
  //       declared.push(root);
  //     } else {
  //       undeclared.push(root);
  //     }
  //   }
  //   return { declared: declared, undeclared: undeclared };
  // }

  // A singleton equals any symbol; A composite must have the same name, the same number of vars of given composite symbol. meanwhile, whether elements of composite are the same does not matter. e.g. \frac{1,2} and \frac{a,b} does not matter.
  static haveTheSameForm(
    env: L_Env,
    expected: L_Symbol,
    candidate: L_Symbol
  ): boolean {
    if (expected instanceof L_Singleton) {
      return true;
    } else if (expected instanceof L_Composite) {
      if (
        candidate instanceof L_Composite &&
        candidate.name === expected.name &&
        candidate.values.length === expected.values.length
      ) {
        for (const [i, v] of candidate.values.entries()) {
          if (!L_Symbol.haveTheSameForm(env, v, expected.values[i])) {
            return false;
          }
        }

        return true;
      }
    }

    throw Error();
  }

  static allSymbolsAreLiterallyTheSame(
    env: L_Env,
    given: L_Symbol[],
    template: L_Symbol[]
  ): boolean {
    return (
      given.length === template.length &&
      given.every((e, i) => L_Symbol.areLiterallyTheSame(env, e, template[i]))
    );
  }

  abstract subSymbolsDeclared(env: L_Env): boolean;

  fix(env: L_Env, freeFixedPairs: [L_Symbol, L_Symbol][]): L_Symbol {
    throw Error();
  }

  static areLiterallyTheSame(
    env: L_Env,
    given: L_Symbol,
    template: L_Symbol
  ): boolean {
    try {
      if (given instanceof L_Singleton && template instanceof L_Singleton) {
        return (
          given.value === template.value || regexTheSame(env, given, template)
        );
      } else if (
        given instanceof L_Composite &&
        template instanceof L_Composite
      ) {
        // name of composite symbol must be equal
        if (given.name !== template.name) {
          return false;
        }

        // vars of composite symbol must be equal
        if (given.values.length !== template.values.length) {
          return false;
        } else {
          for (let i = 0; i < given.values.length; i++) {
            if (
              !L_Symbol.areLiterallyTheSame(
                env,
                given.values[i],
                template.values[i]
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
      L_ReportErr(env, L_Symbol.areLiterallyTheSame);
      return false;
    }

    function regexTheSame(
      env: L_Env,
      given: L_Singleton,
      template: L_Singleton
    ): boolean {
      const relatedLets = env.getLetsVar(template.value);
      if (relatedLets !== undefined) {
        if (relatedLets.regex.test(given.value)) return true;
      }
      return false;
    }
  }
}

export class L_Singleton extends L_Symbol {
  constructor(public value: string) {
    super();
  }

  getRootSingletons(): L_Singleton[] {
    return [this];
  }

  subSymbolsDeclared(env: L_Env): boolean {
    return env.isSingletonDeclared(this.value);
  }

  toString() {
    return this.value;
  }

  fix(env: L_Env, freeFixedPairs: [L_Symbol, L_Symbol][]): L_Symbol {
    for (const freeFixed of freeFixedPairs) {
      if (L_Symbol.areLiterallyTheSame(env, freeFixed[0], this))
        return freeFixed[1];
    }
    return this;
  }
}

// e.g. \frac{1,2} ; \+{1,2} ; \union{A,B} ; \set{x}
export class L_Composite extends L_Symbol {
  constructor(public name: string, public values: L_Symbol[]) {
    super();
  }

  getRootSingletons(): L_Singleton[] {
    const out: L_Singleton[] = [];
    for (const value of this.values) {
      out.push(...value.getRootSingletons());
    }
    return out;
  }

  compositesInside(): L_Composite[] {
    const out: L_Composite[] = [this];
    for (const v of this.values) {
      if (v instanceof L_Composite) {
        out.push(...v.compositesInside());
      }
    }
    return out;
  }

  subSymbolsDeclared(env: L_Env): boolean {
    if (env.getCompositeVar(this.name) === undefined) return false;

    for (const value of this.values) {
      if (value instanceof L_Singleton) {
        if (!env.isSingletonDeclared(value.value)) {
          let ok = false;

          if (!ok) return false;
        }
      } else if (value instanceof L_Composite) {
        if (!value.subSymbolsDeclared(env)) return false;
      }
    }

    return true;
  }

  // //! subSymbols in L_Composite are supposed to be freeVars
  // declared(env: L_Env, varsFromAbove: L_Symbol[]): boolean {
  //   if (env.getCompositeVar(this.name) === undefined) {
  //     env.report(`[Error] composite \\${this.name} not declared.`);
  //     return false;
  //   }

  //   return this.compositesInside().every(
  //     (e) => env.getCompositeVar(e.name) !== undefined
  //   );
  // }

  fix(env: L_Env, freeFixedPairs: [L_Symbol, L_Symbol][]): L_Symbol {
    const outValues: L_Symbol[] = [];
    for (const value of this.values) {
      const fixed = value.fix(env, freeFixedPairs);
      outValues.push(fixed);
    }

    return new L_Composite(this.name, outValues);
  }

  toString() {
    return `\\${this.name}{${this.values.map((e) => e.toString()).join(", ")}}`;
  }

  // the current symbol is free, use a fixed one to fix. the fixed and current symbol must be of the same structure.
  fixUsingGivenFixedComposite(
    env: L_Env,
    fixed: L_Composite
  ): L_Composite | undefined {
    if (!L_Symbol.haveTheSameForm(env, this, fixed)) return undefined;

    const newValues: L_Symbol[] = [];
    for (const [i, v] of this.values.entries()) {
      if (v instanceof L_Singleton) continue;
      else if (v instanceof L_Composite) {
        const newV = v.fixUsingGivenFixedComposite(
          env,
          fixed.values[i] as L_Composite
        );
        if (newV !== undefined) newValues.push(newV);
        else return undefined;
      }
    }

    return new L_Composite(this.name, newValues);
  }
}

// e.g. \frac{\frac{a,b},c}[a,b,c] Here a,b,c are free variables that appear in the given composite symbol.
export class CompositeSymbolInIfReq extends L_Composite {
  constructor(name: string, values: L_Symbol[], public newVars: L_Singleton[]) {
    super(name, values);
  }

  subSymbolsDeclared(env: L_Env): boolean {
    return false;
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
  Unknown,
  False,
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
}

export class StoredFact {
  constructor(
    public vars: string[], // stored fixed, only used when storing opts
    public req: StoredReq[], // when adding a new layer of if-then, push a new req list (ToCheckNode[]) at end of req.
    public isT: boolean
  ) {}

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
