import { L_Env } from "./L_Env";
import { L_Node } from "./L_Nodes";
import {
  L_Composite,
  L_Singleton,
  L_Symbol,
  SymbolDeclaredChecker,
} from "./L_Symbols";
import { L_KW } from "./L_Keywords";
import { OptSymbol } from "./L_OptSymbol";
import exp from "constants";

export abstract class L_FactNode extends L_Node {
  constructor(public isT: boolean) {
    super();
  }

  abstract fixByIfVars(
    env: L_Env,
    freeFixPairs: [L_Symbol, L_Symbol][]
  ): L_FactNode; // called by prove_by_contradiction
  abstract copyWithIsTReverse(): L_FactNode;
  abstract getRootOptNodes(): [OptFactNode, L_FactNode[]][];
}

export type IfVarsFormReqType = {
  key: L_Singleton;
  freeVars: L_Singleton[];
  form: L_Symbol;
};

export abstract class LogicVar {
  constructor(public name: L_Singleton) {}
}

export class SingletonLogicVar extends LogicVar {}

export class CompositeLogicVar extends LogicVar {
  constructor(
    name: L_Singleton,
    public freeVars: L_Singleton[],
    public form: L_Composite
  ) {
    super(name);
  }
}

export class ConceptLogicVar extends LogicVar {}

export abstract class LogicNode extends L_FactNode {
  constructor(
    public vars: LogicVar[] = [],
    public req: L_FactNode[] = [],
    public onlyIfs: L_FactNode[] = [],
    isT: boolean = true
    // public varsFormReq: IfVarsFormReqType[] // public varsForm: [L_Singleton, L_Singleton[], L_Symbol][]
  ) {
    super(isT);
  }

  private addPrefixToVars(env: L_Env): boolean {
    // this.vars = this.vars.map((e) => new L_Singleton(L_KW.IfVarPrefix + e));
    const newVars: LogicVar[] = [];
    for (const v of this.vars) {
      if (v instanceof SingletonLogicVar) {
        newVars.push(new SingletonLogicVar(v.name.withIfVarPrefix()));
      } else if (v instanceof CompositeLogicVar) {
        const newKey = v.name.withIfVarPrefix();
        const newFreeVars = v.freeVars.map((e) => e.withIfVarPrefix());
        // TODO form is not done
        const freeFixedPairs: [L_Symbol, L_Symbol][] = v.freeVars.map(
          (e, i) => [e, newFreeVars[i]]
        );
        const newForm = v.form.fix(env, freeFixedPairs) as L_Composite;
        const newVar = new CompositeLogicVar(newKey, newFreeVars, newForm);
        newVars.push(newVar);
      }

      this.vars = newVars;
    }

    for (const r of this.req) {
      if (r instanceof LogicNode) {
        r.addPrefixToVars(env);
      }
    }

    for (const onlyIf of this.onlyIfs) {
      if (onlyIf instanceof LogicNode) {
        onlyIf.addPrefixToVars(env);
      }
    }

    return true;
  }

  fixUsingIfPrefix(env: L_Env, freeFixPairs: [L_Symbol, L_Symbol][]): boolean {
    try {
      let newFreeFixPairs: [L_Symbol, L_Symbol][] = [];

      for (const v of this.vars) {
        if (v instanceof SingletonLogicVar) {
          freeFixPairs.push([v.name, v.name.withIfVarPrefix()]);
        } else if (v instanceof CompositeLogicVar) {
          for (const formFreeVar of v.freeVars) {
            newFreeFixPairs.push([
              formFreeVar,
              new L_Singleton(L_KW.IfVarPrefix + formFreeVar.value),
            ]);
          }
        } else if (v instanceof ConceptLogicVar) {
          freeFixPairs.push([v.name, v.name.withIfVarPrefix()]);
        }
      }

      // let newFreeFixPairs: [L_Symbol, L_Symbol][] = this.vars.map((e) => [
      //   e,
      //   new L_Singleton(L_KW.IfVarPrefix + e.value),
      // ]);
      // for (const formReq of this.varsFormReq) {
      //   for (const formFreeVar of formReq.freeVars) {
      //     newFreeFixPairs.push([
      //       formFreeVar,
      //       new L_Singleton(L_KW.IfVarPrefix + formFreeVar.value),
      //     ]);
      //   }
      // }

      freeFixPairs = [...freeFixPairs, ...newFreeFixPairs];
      this.req = this.req.map((r) => r.fixByIfVars(env, freeFixPairs));
      this.onlyIfs = this.onlyIfs.map((onlyIf) =>
        onlyIf.fixByIfVars(env, freeFixPairs)
      );

      // this.varsFormReq.forEach((e) => (e.form = e.form.fix(env, freeFixPairs)));

      this.addPrefixToVars(env);

      return true;
    } catch (error) {
      return false;
    }
  }

  makeFreeFixPairs(env: L_Env) {}

  static makeFreeFixPairs(
    fixed: L_Symbol[],
    ifNode: IfNode
    // free: L_Symbol[]
  ): [L_Symbol, L_Symbol][] {
    const out: [L_Symbol, L_Symbol][] = [];
    if (fixed.length !== ifNode.vars.length) throw Error();

    for (const [i, v] of ifNode.vars.entries()) {
      if (v instanceof SingletonLogicVar) {
        out.push([v.name, fixed[i]]);
      } else if (v instanceof CompositeLogicVar) {
        if (L_Symbol.weakStructurallyEql(v.form, fixed[i])) {
          out.push([v.name, fixed[i]]);
          //! ????????
        } else {
          throw Error();
        }
      }
    }

    return out;
  }

  override getRootOptNodes(): [OptFactNode, L_FactNode[]][] {
    const roots = this.onlyIfs.map((e) => e.getRootOptNodes()).flat();
    for (const root of roots) {
      root[1] = [this, ...root[1]];
    }
    return roots;
  }

  // override tryFactVarsDeclared(env: L_Env): void {
  //   const newEnv = new L_Env(env);
  //   for (const v of this.vars) {
  //     newEnv.tryNewPureSingleton(v.value);
  //   }

  //   for (const formReq of this.varsFormReq) {
  //     formReq.freeVars.forEach((e) => newEnv.tryNewPureSingleton(e.value));
  //   }

  //   for (const req of this.req) {
  //     req.tryFactVarsDeclared(newEnv);
  //   }

  //   for (const onlyIf of this.onlyIfs) {
  //     onlyIf.tryFactVarsDeclared(newEnv);
  //   }
  // }
}

// export class IffNode extends LogicNode {
//   override fixByIfVars(
//     env: L_Env,
//     freeFixPairs: [L_Symbol, L_Symbol][]
//   ): LogicNode {
//     const newReq: L_FactNode[] = [];
//     for (const r of this.req) {
//       newReq.push(r.fixByIfVars(env, freeFixPairs));
//     }

//     const newOnlyIf: L_FactNode[] = [];
//     for (const onlyIf of this.onlyIfs) {
//       newOnlyIf.push(onlyIf.fixByIfVars(env, freeFixPairs));
//     }

//     return new IffNode(this.vars, newReq, newOnlyIf, this.isT);
//   }

//   override copyWithIsTReverse(): IffNode {
//     return new IffNode(
//       this.vars,
//       this.req,
//       this.onlyIfs,
//       !this.isT,
//       this.varsFormReq
//     );
//   }

//   override toString() {
//     const mainPart = `iff ${this.vars.toString()} : ${this.req} {${
//       this.onlyIfs
//     }}`;
//     const notPart = !this.isT ? "[not] " : "";

//     return notPart + mainPart;
//   }
// }

export class IfNode extends LogicNode {
  override fixByIfVars(
    env: L_Env,
    freeFixPairs: [L_Symbol, L_Symbol][]
  ): LogicNode {
    const newReq: L_FactNode[] = [];
    for (const r of this.req) {
      newReq.push(r.fixByIfVars(env, freeFixPairs));
    }

    const newOnlyIf: L_FactNode[] = [];
    for (const onlyIf of this.onlyIfs) {
      newOnlyIf.push(onlyIf.fixByIfVars(env, freeFixPairs));
    }

    return new IfNode(this.vars, newReq, newOnlyIf, this.isT);
  }

  override copyWithIsTReverse(): IfNode {
    return new IfNode(this.vars, this.req, this.onlyIfs, !this.isT);
  }

  override toString() {
    let varsFormReqStr: string = "";

    const mainPart = `if ${this.vars.toString()} ${varsFormReqStr}: ${
      this.req
    } {${this.onlyIfs}}`;
    const notPart = !this.isT ? "[not] " : "";

    return notPart + mainPart;
  }
}

export class IfReqNode {
  constructor(public fact: L_FactNode, public vars: L_Symbol[]) {}
}

export class OptFactNode extends L_FactNode {
  constructor(
    public optSymbol: OptSymbol,
    public vars: L_Symbol[],
    isT: boolean = true,
    public checkVars: L_Symbol[][] | undefined
  ) {
    super(isT);
  }

  newToChecks(checkVars: L_Symbol[][]): OptFactNode {
    return new OptFactNode(this.optSymbol, this.vars, this.isT, checkVars);
  }

  static literallyIdentical(
    env: L_Env,
    given: OptFactNode,
    expects: OptFactNode
  ): boolean {
    if (given.optSymbol.name !== expects.optSymbol.name) return false;
    return L_Symbol.symbolArrLiteralEql(env, given.vars, expects.vars);
  }

  copyCommutatively(): OptFactNode | undefined {
    if (this.vars.length !== 2) {
      return undefined;
    }
    const newVars: L_Symbol[] = [this.vars[1], this.vars[0]];
    return new OptFactNode(this.optSymbol, newVars, this.isT, this.checkVars);
  }

  override getRootOptNodes(): [OptFactNode, L_FactNode[]][] {
    return [[this, []]];
  }

  override fixByIfVars(
    env: L_Env,
    freeFixPairs: [L_Symbol, L_Symbol][]
  ): OptFactNode {
    const newVars: L_Symbol[] = [];
    for (let v of this.vars) {
      let fixed = false;
      v = v.fix(env, freeFixPairs); // if v is singleton, then fix itself; if v is composite, then fix its variables.
      if (!fixed) newVars.push(v);
    }

    const newCheckVars = this.checkVars?.map((e) =>
      e.map((v) => v.fix(env, freeFixPairs))
    );

    return new OptFactNode(this.optSymbol, newVars, this.isT, newCheckVars);
  }

  override copyWithIsTReverse(): OptFactNode {
    return new OptFactNode(
      this.optSymbol,
      this.vars,
      !this.isT,
      this.checkVars
    );
  }

  override toString() {
    const notPart = !this.isT ? "[not] " : "";
    const checkVarsStr =
      this.checkVars === undefined
        ? ""
        : "[" +
          this.checkVars
            .map((e) => e.map((j) => j.toString()).join(", "))
            .join("; ") +
          "]";
    let mainPart = "";
    if (this.vars.length === 2) {
      mainPart = `${this.vars[0]} ${this.optSymbol.name} ${this.vars[1]}`;
    } else if (this.vars.length === 1) {
      mainPart = `${this.vars[0]} ${L_KW.Is} ${this.optSymbol.name}`;
    } else {
      mainPart = "$" + this.optSymbol.name + `(${this.vars})`;
    }
    return notPart + mainPart + checkVarsStr;
  }
}

export class FreeOptNode extends OptFactNode {}
export class EqualFact extends OptFactNode {
  constructor(opt: OptFactNode) {
    super(opt.optSymbol, opt.vars, opt.isT, opt.checkVars);
  }
}

export abstract class BuiltinCheckNode extends L_FactNode {}

// TODO IsProperty logic is not implemented
export class IsConceptNode extends BuiltinCheckNode {
  constructor(
    public concepts: L_Singleton[],
    public facts: L_FactNode[],
    isT: boolean
  ) {
    super(isT);
  }

  override getRootOptNodes(): [OptFactNode, L_FactNode[]][] {
    throw Error();
  }

  override copyWithIsTReverse(): L_FactNode {
    return new IsConceptNode(this.concepts, this.facts, !this.isT);
  }

  override fixByIfVars(
    env: L_Env,
    freeFixPairs: [L_Symbol, L_Symbol][]
  ): L_FactNode {
    return this;
  }

  toString() {
    return `${L_KW.isConcept}(${this.concepts})`;
  }

  // override tryFactVarsDeclared(env: L_Env): void {
  //   for (const fact of this.facts) {
  //     fact.tryFactVarsDeclared(env);
  //   }
  // }
}

export class IsFormNode extends BuiltinCheckNode {
  constructor(
    public candidate: L_Symbol,
    public baseline: L_Composite,
    public facts: L_FactNode[],
    isT: boolean
  ) {
    super(isT);
  }

  override getRootOptNodes(): [OptFactNode, L_FactNode[]][] {
    throw Error();
  }

  override copyWithIsTReverse(): L_FactNode {
    return new IsFormNode(this.candidate, this.baseline, this.facts, !this.isT);
  }

  override fixByIfVars(
    env: L_Env,
    freeFixPairs: [L_Symbol, L_Symbol][]
  ): L_FactNode {
    let fixed: L_Symbol | undefined = undefined;
    for (const freeFix of freeFixPairs) {
      if (L_Symbol.literalEql(env, freeFix[0], this.candidate)) {
        fixed = freeFix[1];
      }
    }

    if (fixed === undefined) {
      env.report(`IsFormNode.fix failed`);
      throw Error();
    } else {
      return new IsFormNode(fixed, this.baseline, this.facts, this.isT);
    }
  }

  // override tryFactVarsDeclared(env: L_Env): void {}

  toString(): string {
    const notStr = this.isT ? "" : "[not]";
    const mainStr = `${L_KW.isForm}(${this.candidate}, ${this.baseline}, {${this.facts}})`;
    return notStr + mainStr;
  }
}

export abstract class FormulaFactNode extends L_FactNode {
  constructor(
    public left: OptFactNode | FormulaFactNode,
    public right: OptFactNode | FormulaFactNode,
    isT: boolean
  ) {
    super(isT);
  }

  getWhereIsGivenFactAndAnotherBranch(fact: L_FactNode): {
    itself: FormulaSubNode;
    anotherBranch: FormulaSubNode;
  } {
    if (fact === this.left) {
      return { itself: this.left, anotherBranch: this.right };
    } else if (fact === this.right) {
      return { itself: this.right, anotherBranch: this.left };
    }

    throw Error();
  }

  // override tryFactVarsDeclared(env: L_Env): void {
  //   this.left.tryFactVarsDeclared(env);
  //   this.right.tryFactVarsDeclared(env);
  // }

  override fixByIfVars(
    env: L_Env,
    freeFixPairs: [L_Symbol, L_Symbol][]
  ): FormulaFactNode {
    const left = this.left.fixByIfVars(env, freeFixPairs);
    const right = this.right.fixByIfVars(env, freeFixPairs);
    if (this instanceof OrToCheckNode) {
      return new OrToCheckNode(left, right, this.isT);
    } else if (this instanceof AndToCheckNode) {
      return new AndToCheckNode(left, right, this.isT);
    }

    throw Error();
  }

  override copyWithIsTReverse(): L_FactNode {
    throw Error();
  }

  getLeftRight(): L_FactNode[] {
    return [this.left, this.right];
  }

  whereIsOpt(opt: OptFactNode) {
    const out = { left: false, right: false };
    if (this.left instanceof OptFactNode) {
      if (opt.optSymbol.name === this.left.optSymbol.name) {
        out.left = true;
      }
    } else if (this.left instanceof FormulaFactNode) {
      const got = this.left.whereIsOpt(opt);
      if (got.left || got.right) out.left = true;
    }

    if (this.right instanceof OptFactNode) {
      if (opt.optSymbol.name === this.right.optSymbol.name) {
        out.right = true;
      }
    } else if (this.right instanceof FormulaFactNode) {
      const got = this.right.whereIsOpt(opt);
      if (got.left || got.right) out.right = true;
    }

    return out;
  }
}

export class OrToCheckNode extends FormulaFactNode {
  override copyWithIsTReverse(): L_FactNode {
    return new OrToCheckNode(this.left, this.right, !this.isT);
  }

  override getRootOptNodes(): [OptFactNode, L_FactNode[]][] {
    const out: [OptFactNode, L_FactNode[]][] = [];
    for (const node of this.getLeftRight()) {
      const roots = node.getRootOptNodes();
      for (const root of roots) {
        root[1] = [this, ...root[1]];
      }
      out.push(...roots);
    }
    return out;
  }

  toString() {
    return `(${this.left} or ${this.right})`;
  }

  getRootOpts(): OptFactNode[] | null {
    const allRoots: OptFactNode[] = [];
    for (const subNode of this.getLeftRight()) {
      if (subNode instanceof OrToCheckNode) {
        const roots = subNode.getRootOpts();
        if (roots === null) {
          return null;
        } else {
          allRoots.push(...roots);
        }
      } else if (subNode instanceof OptFactNode) {
        allRoots.push(subNode);
      } else {
        return null;
      }
    }

    return allRoots;
  }
}

export class AndToCheckNode extends FormulaFactNode {
  override copyWithIsTReverse(): L_FactNode {
    return new AndToCheckNode(this.left, this.right, !this.isT);
  }

  override getRootOptNodes(): [OptFactNode, L_FactNode[]][] {
    const out: [OptFactNode, L_FactNode[]][] = [];
    for (const node of this.getLeftRight()) {
      const roots = node.getRootOptNodes();
      for (const root of roots) {
        root[1] = [this, ...root[1]];
      }
      out.push(...roots);
    }
    return out;
  }

  toString() {
    return `(${this.left} and ${this.right})`;
  }
}

export type FormulaSubNode = FormulaFactNode | OptFactNode;

export class FactsNode extends L_FactNode {
  constructor(
    public varsPairs: [L_Singleton, L_Symbol][][],
    public facts: L_FactNode[],
    isT: boolean
  ) {
    super(isT);
  }

  // override tryFactVarsDeclared(env: L_Env): void {
  //   for (const v of this.varsPairs) {
  //     v.forEach((e) => e[1].tryVarsDeclared(env));
  //   }

  //   for (const fact of this.facts) {
  //     fact.tryFactVarsDeclared(env);
  //   }
  // }

  override fixByIfVars(
    env: L_Env,
    freeFixPairs: [L_Symbol, L_Symbol][]
  ): L_FactNode {
    const newFixedVars: [L_Singleton, L_Symbol][][] = this.varsPairs.map((e) =>
      e.map((v: [L_Singleton, L_Symbol]) => [v[0], v[1].fix(env, freeFixPairs)])
    );

    const newFacts = this.facts.map((e) => e.fixByIfVars(env, freeFixPairs));

    return new FactsNode(newFixedVars, newFacts, this.isT);
  }

  override copyWithIsTReverse(): L_FactNode {
    return new FactsNode(this.varsPairs, this.facts, !this.isT);
  }

  override getRootOptNodes(): [OptFactNode, L_FactNode[]][] {
    throw Error();
  }

  toString() {
    const vars = this.varsPairs
      .map((arr) => arr.map((e) => `${e[0]}:${e[1]}`))
      .toString();
    return `[${vars}] {${this.facts}}`;
  }
}

export class FactVarsDeclaredChecker {
  static check(env: L_Env, fact: L_FactNode): void {
    if (fact instanceof OptFactNode) {
      return this.checkOpt(env, fact);
    } else if (fact instanceof IfNode) {
      return this.checkLogicNode(env, fact);
    } else if (fact instanceof FactsNode) {
      return this.checkFactsNode(env, fact);
    }

    throw Error();
  }

  private static checkOpt(env: L_Env, fact: OptFactNode): void {
    for (const v of fact.vars) {
      // v.tryVarsDeclared(env);
      SymbolDeclaredChecker.check(env, v);
    }

    if (fact.checkVars === undefined) return;

    for (const layer of fact.checkVars) {
      for (const v of layer) {
        // v.tryVarsDeclared(env);
        SymbolDeclaredChecker.check(env, v);
      }
    }

    return;
  }

  private static checkLogicNode(env: L_Env, fact: LogicNode): void {
    const newEnv = new L_Env(env);
    for (const v of fact.vars) {
      if (v instanceof SingletonLogicVar) {
        newEnv.tryNewSingleton(v.name.value);
      } else if (v instanceof CompositeLogicVar) {
        newEnv.tryNewSingleton(v.name.value);
        v.freeVars.forEach((e) => newEnv.tryNewSingleton(e.value));
      }
    }

    // for (const formReq of fact.varsFormReq) {
    //   formReq.freeVars.forEach((e) => newEnv.tryNewPureSingleton(e.value));
    // }

    for (const req of fact.req) {
      // req.tryFactVarsDeclared(newEnv);
      this.check(newEnv, req);
    }

    for (const onlyIf of fact.onlyIfs) {
      // onlyIf.tryFactVarsDeclared(newEnv);
      this.check(newEnv, onlyIf);
    }
  }

  private static checkFactsNode(env: L_Env, fact: FactsNode): void {
    for (const v of fact.varsPairs) {
      // v.forEach((e) => e[1].tryVarsDeclared(env));
      // v.forEach((e) => this.check(env, e[1]));
      v.forEach((e) => SymbolDeclaredChecker.check(env, e[1]));
    }

    for (const f of fact.facts) {
      // f.tryFactVarsDeclared(env);
      this.check(env, f);
    }
  }
}
