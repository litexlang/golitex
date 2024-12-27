import { L_Env } from "./L_Env";
import { L_ReportBoolErr, L_ReportErr } from "./L_Report";
import { LogicNode, OptNode, ToCheckNode } from "./L_Nodes";
import { checkFact } from "./L_Checker";
import { L_Keywords } from "./L_Keywords";

export abstract class L_Symbol {
  // abstract getRootSingletons(): L_Singleton[];

  static isExist(symbol: L_Symbol): boolean {
    return (
      symbol instanceof L_Singleton && symbol.value === L_Keywords.ExistSymbol
    );
  }

  static isAny(symbol: L_Symbol): boolean {
    return (
      symbol instanceof L_Singleton && symbol.value === L_Keywords.AnySymbol
    );
  }

  // A singleton equals any symbol; A composite must have the same name, the same number of vars of given composite symbol. meanwhile, whether elements of composite are the same does not matter. e.g. \frac{1,2} and \frac{a,b} does not matter.
  static haveMatchingSymbolStructure(
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
          if (
            !L_Symbol.haveMatchingSymbolStructure(env, v, expected.values[i])
          ) {
            return false;
          }
        }

        return true;
      }
    }

    throw Error();
  }

  static optsLiterallyIdentical(
    env: L_Env,
    given: OptNode,
    expects: OptNode
  ): boolean {
    if (given.optSymbol.name !== expects.optSymbol.name) return false;

    return L_Symbol.allSymbolsLiterallyIdentical(env, given.vars, expects.vars);
  }

  static allSymbolsLiterallyIdentical(
    env: L_Env,
    given: L_Symbol[],
    expected: L_Symbol[]
  ): boolean {
    return (
      given.length === expected.length &&
      given.every((e, i) => L_Symbol.literallyIdentical(env, e, expected[i]))
    );
  }

  // * MAIN FUNCTION OF THE WHOLE PROJECT
  static literallyIdentical(
    env: L_Env,
    given: L_Symbol,
    expected: L_Symbol
  ): boolean {
    try {
      //* ANY symbol is equal to any symbol, except EXIST
      if (provedByAny(env, given, expected)) return true;
      if (regexIdentical(env, given, expected)) return true;
      if (pureSingleIdentical(env, given, expected)) return true;
      if (compareComposites(env, given, expected)) return true;

      return false;
    } catch {
      L_ReportErr(env, L_Symbol.literallyIdentical);
      return false;
    }

    function compareComposites(
      env: L_Env,
      given: L_Symbol,
      expected: L_Symbol
    ): boolean {
      if (given instanceof L_Composite && expected instanceof L_Composite) {
        // name of composite symbol must be equal
        if (given.name !== expected.name) {
          return false;
        }

        // vars of composite symbol must be equal
        if (given.values.length !== expected.values.length) {
          return false;
        } else {
          for (let i = 0; i < given.values.length; i++) {
            if (
              !L_Symbol.literallyIdentical(
                env,
                given.values[i],
                expected.values[i]
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
    }

    function provedByAny(
      env: L_Env,
      given: L_Symbol,
      expected: L_Symbol
    ): boolean {
      if (L_Symbol.isAny(expected) && !L_Symbol.isExist(given)) return true;
      if (L_Symbol.isAny(given) && !L_Symbol.isExist(expected)) return true;

      return false;
    }

    function pureSingleIdentical(
      env: L_Env,
      given: L_Symbol,
      expected: L_Symbol
    ) {
      if (given instanceof L_Singleton && expected instanceof L_Singleton) {
        return given.value === expected.value;
      }

      return false;
    }

    function regexIdentical(
      env: L_Env,
      given: L_Symbol,
      expected: L_Symbol
    ): boolean {
      if (given instanceof L_Singleton && expected instanceof L_Singleton) {
        let relatedLets = env.getLetsVar(expected.value);
        if (relatedLets !== undefined) {
          if (relatedLets.regex.test(given.value)) return true;
        }
        return false;
      }
      return false;
    }
  }

  abstract subSymbolsDeclared(env: L_Env): boolean;

  abstract fix(env: L_Env, freeFixedPairs: [L_Symbol, L_Symbol][]): L_Symbol;
}

// Used for TS API FOR USERS
export class L_UndefinedSymbol extends L_Symbol {
  constructor() {
    super();
  }

  // getRootSingletons(): L_Singleton[] {
  //   throw Error();
  // }

  subSymbolsDeclared(env: L_Env): boolean {
    throw Error();
  }

  fix(env: L_Env, freeFixedPairs: [L_Symbol, L_Symbol][]): L_Symbol {
    throw Error();
  }
}

export class L_Singleton extends L_Symbol {
  constructor(public value: string) {
    super();
  }

  // getRootSingletons(): L_Singleton[] {
  //   return [this];
  // }

  //* IMPORTANT METHOD
  subSymbolsDeclared(env: L_Env): boolean {
    return (
      this.value === L_Keywords.ExistSymbol ||
      this.value === L_Keywords.AnySymbol ||
      env.isSingletonDeclared(this.value) ||
      env.isRegexSingleton(this.value)
    );
  }

  toString() {
    return this.value;
  }

  fix(env: L_Env, freeFixedPairs: [L_Symbol, L_Symbol][]): L_Symbol {
    for (const freeFixed of freeFixedPairs) {
      if (L_Symbol.literallyIdentical(env, freeFixed[0], this))
        return freeFixed[1];
    }
    return this;
  }
}

export class IndexedSymbol extends L_Symbol {
  constructor(public given: L_Symbol, public indexes: number[]) {
    super();
  }

  // getRootSingletons(): L_Singleton[] {
  //   throw Error();
  // }

  subSymbolsDeclared(env: L_Env): boolean {
    return this.given.subSymbolsDeclared(env);
  }

  // ! IndexedSymbol fix has 2 effects: 1. fix frees 2. return the symbol under the index
  fix(env: L_Env, freeFixedPairs: [L_Symbol, L_Symbol][]): L_Symbol {
    let out: IndexedSymbol = this;

    for (const freeFixed of freeFixedPairs) {
      if (L_Symbol.literallyIdentical(env, freeFixed[0], this.given)) {
        out = new IndexedSymbol(freeFixed[1], this.indexes);
      }
    }

    if (out.given instanceof L_Composite) {
      return out.given.getIndexedSubNode(out.indexes);
    } else {
      throw Error();
    }
  }

  toString() {
    return `${L_Keywords.IndexedSymbolKeyword}(${this.given}, ${this.indexes})`;
  }
}

// e.g. \frac{1,2} ; \+{1,2} ; \union{A,B} ; \set{x}
export class L_Composite extends L_Symbol {
  constructor(public name: string, public values: L_Symbol[]) {
    super();
  }

  getIndexedSubNode(indexes: number[]): L_Symbol {
    let curComposite: L_Composite = this;
    for (let i = 0; i < indexes.length - 1; i++) {
      const cur = curComposite.values[indexes[i]];
      if (cur instanceof L_Composite) curComposite = cur;
    }

    return curComposite.values[indexes[indexes.length - 1]];
  }

  compositeSatisfyItsReq(env: L_Env): boolean {
    try {
      const declaration = env.getCompositeVar(this.name);

      if (declaration === undefined) {
        env.report(`[Error] ${this.name} undeclared`);
        throw Error();
      }

      if (this.values.length !== declaration.composite.values.length) {
        env.report(`[Error] ${this.name} invalid number of parameters.`);
        throw Error();
      }

      const freeFixPairs: [L_Symbol, L_Symbol][] = LogicNode.makeFreeFixPairs(
        env,
        this.values,
        declaration.composite.values
      );

      const newFacts = declaration.facts.map((e) => e.fix(env, freeFixPairs));

      for (const fact of newFacts) {
        if (checkFact(env, fact) !== L_Out.True) {
          env.report(
            `[Unknown] failed to check ${fact} when checking requirements of sub-symbols of composite ${this}`
          );
          return false;
        }
      }

      return true;
    } catch {
      return L_ReportBoolErr(env, this.compositeSatisfyItsReq, ``);
    }
  }

  // getRootSingletons(): L_Singleton[] {
  //   const out: L_Singleton[] = [];
  //   for (const value of this.values) {
  //     out.push(...value.getRootSingletons());
  //   }
  //   return out;
  // }

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
    if (!L_Symbol.haveMatchingSymbolStructure(env, this, fixed))
      return undefined;

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

export class FormalSymbol extends L_Singleton {}

export class FunctionalSymbol extends L_Symbol {
  // fixed: at compile time, test whether it contains free vars.
  constructor(public fixed: boolean) {
    super();
  }

  subSymbolsDeclared(env: L_Env): boolean {
    throw Error();
  }

  fix(env: L_Env, freeFixedPairs: [L_Symbol, L_Symbol][]): L_Symbol {
    throw Error();
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

export abstract class L_KnownFactReq {
  constructor() {}
}

export class OptKnownFactReq extends L_KnownFactReq {
  constructor(public opt: OptNode) {
    super();
  }
}

export class IfKnownFactReq extends L_KnownFactReq {
  constructor(public req: ToCheckNode[]) {
    super();
  }
}

export class FormulaKnownFactReq extends L_KnownFactReq {
  constructor(public req: ToCheckNode[]) {
    super();
  }
}
