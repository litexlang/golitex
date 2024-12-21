import { L_Env } from "./L_Env";
import {
  L_VarsInOptDoubleDeclErr,
  L_VarsInOptNotDeclaredBool,
} from "./L_Report";
import {
  CompositeSymbolInIfReq,
  L_Composite,
  L_OptSymbol,
  L_Singleton,
  L_Symbol,
} from "./L_Structs";

export abstract class L_Node {}

export abstract class ToCheckNode extends L_Node {
  constructor(public isT: boolean) {
    super();
  }

  // called by L_Memory
  abstract varsDeclared(env: L_Env): boolean;

  // called by checker
  abstract fix(env: L_Env, freeFixPairs: [L_Symbol, L_Symbol][]): ToCheckNode;

  // called by prove_by_contradiction
  abstract copyWithIsTReverse(): ToCheckNode;

  // called by "using known fact to check given fact. when doing so, get all root opts and filter opt with the same name."
  abstract getRootOptNodes(): [OptNode, ToCheckNode[]][];
}

export class LogicNode extends ToCheckNode {
  constructor(
    public vars: L_Symbol[] = [],
    public req: ToCheckNode[] = [],
    public onlyIfs: ToCheckNode[] = [],
    isT: boolean = true
  ) {
    super(isT);
  }

  getRootOptNodes(): [OptNode, ToCheckNode[]][] {
    const roots = this.onlyIfs.map((e) => e.getRootOptNodes()).flat();
    for (const root of roots) {
      root[1] = [this, ...root[1]];
    }
    return roots;
  }

  static makeFreeFixPairs(
    env: L_Env,
    fixed: L_Symbol[],
    free: L_Symbol[]
  ): [L_Symbol, L_Symbol][] {
    const out: [L_Symbol, L_Symbol][] = [];
    for (let i = 0; i < free.length; i++) {
      out.push([free[i], fixed[i]]);
    }

    return out;
  }

  varsDeclared(env: L_Env): boolean {
    // * The new variables declared as if-fact parameters are stored in newEnv
    const newEnv = new L_Env(env);

    for (const v of this.vars) {
      if (v instanceof L_Composite) {
        if (v instanceof CompositeSymbolInIfReq) {
          for (const newVar of v.newVars) {
            if (newVar.subSymbolsDeclared(newEnv)) {
              return L_VarsInOptDoubleDeclErr(env, this.varsDeclared, newVar);
            }
            newEnv.newSingletonVar(newVar.value);
          }

          if (!v.subSymbolsDeclared(newEnv)) {
            return L_VarsInOptNotDeclaredBool(newEnv, this.varsDeclared, v);
          }
        }
      } else if (v instanceof L_Singleton) {
        if (v.subSymbolsDeclared(newEnv)) {
          return L_VarsInOptDoubleDeclErr(env, this.varsDeclared, v);
        }
        newEnv.newSingletonVar(v.value);
      }
    }

    for (const req of this.req) {
      if (!req.varsDeclared(newEnv)) {
        return L_VarsInOptNotDeclaredBool(env, this.varsDeclared, req);
      }
    }

    for (const onlyIf of this.onlyIfs) {
      if (!onlyIf.varsDeclared(newEnv)) {
        return L_VarsInOptNotDeclaredBool(env, this.varsDeclared, onlyIf);
      }
    }

    return true;
  }

  fix(env: L_Env, freeFixPairs: [L_Symbol, L_Symbol][]): LogicNode {
    const newReq: ToCheckNode[] = [];
    for (const r of this.req) {
      newReq.push(r.fix(env, freeFixPairs));
    }

    const newOnlyIf: ToCheckNode[] = [];
    for (const onlyIf of this.onlyIfs) {
      newOnlyIf.push(onlyIf.fix(env, freeFixPairs));
    }

    if (this instanceof IfNode) {
      return new IfNode([], newReq, newOnlyIf);
    }

    throw Error();
  }

  override copyWithIsTReverse(): LogicNode {
    return new LogicNode(this.vars, this.req, this.onlyIfs, !this.isT);
  }

  override toString() {
    let type: string = "";
    type = "if";
    const mainPart = `${type} ${this.vars.toString()} : ${this.req
      .map((e) => e.toString())
      .join(", ")} {${this.onlyIfs.map((e) => e.toString()).join(", ")}}`;
    const notPart = !this.isT ? "[not] " : "";

    return notPart + mainPart;
  }
}

export class IffNode extends LogicNode {}
export class IfNode extends LogicNode {}

export class OptNode extends ToCheckNode {
  constructor(
    public optSymbol: L_OptSymbol,
    public vars: L_Symbol[],
    isT: boolean = true,
    public checkVars: L_Symbol[][] | undefined = undefined
  ) {
    super(isT);
  }

  getRootOptNodes(): [OptNode, ToCheckNode[]][] {
    return [[this, []]];
  }

  varsDeclared(env: L_Env): boolean {
    for (const v of this.vars) {
      if (!v.subSymbolsDeclared(env)) {
        return L_VarsInOptNotDeclaredBool(env, this.varsDeclared, this);
      }
    }

    if (this.checkVars === undefined) return true;

    for (const layer of this.checkVars) {
      for (const v of layer) {
        if (!v.subSymbolsDeclared(env)) {
          return L_VarsInOptNotDeclaredBool(env, this.varsDeclared, this);
        }
      }
    }

    return true;
  }

  fix(env: L_Env, freeFixPairs: [L_Symbol, L_Symbol][]): OptNode {
    const newVars: L_Symbol[] = [];
    for (let v of this.vars) {
      let fixed = false;
      v = v.fix(env, freeFixPairs); // if v is singleton, then fix itself; if v is composite, then fix its variables.
      if (!fixed) newVars.push(v);
    }

    return new OptNode(this.optSymbol, newVars, this.isT, undefined);
  }

  override copyWithIsTReverse(): OptNode {
    return new OptNode(this.optSymbol, this.vars, !this.isT, this.checkVars);
  }

  override toString() {
    const mainPart =
      this.optSymbol.name +
      `(${this.vars.map((e) => e.toString()).join(", ")})`;
    const notPart = !this.isT ? "[not] " : "";
    const checkVarsStr =
      this.checkVars === undefined
        ? ""
        : "[" +
          this.checkVars
            .map((e) => e.map((j) => j.toString()).join(", "))
            .join("; ") +
          "]";
    return notPart + mainPart + checkVarsStr;
  }
}

export class DefNode extends L_Node {
  constructor(
    public opt: OptNode,
    public cond: ToCheckNode[] = [],
    public onlyIfs: ToCheckNode[] = [] // public defName: string | undefined = undefined // public cond: ToCheckNode[] = [],
  ) {
    super();
  }

  override toString(): string {
    return `${this.opt.toString()}`;
  }
}

export class KnowNode extends L_Node {
  isKnowEverything: boolean = false;

  constructor(public facts: ToCheckNode[], public names: string[]) {
    super();
  }

  override toString(): string {
    return (
      "know: " + this.facts.map((e) => (e as ToCheckNode).toString()).join("; ")
    );
  }
}

export class LetNode extends L_Node {
  constructor(public vars: string[], public facts: ToCheckNode[]) {
    super();
  }

  override toString() {
    return `${this.vars.join(", ")}: ${this.facts
      .map((s) => s.toString())
      .join(", ")}`;
  }
}
export class LetHashNode extends LetNode {}

export class ProveNode extends L_Node {
  constructor(
    // Only one of toProve, fixedIfThenOpt exists
    public toProve: ToCheckNode,
    public block: L_Node[] // If contradict !== undefined, then prove_by_contradiction
  ) {
    super();
  }

  override toString() {
    return `prove ${this.toProve}`;
  }
}
export class ProveContradictNode extends ProveNode {
  constructor(
    toProve: ToCheckNode,
    block: L_Node[],
    public contradict: OptNode
  ) {
    super(toProve, block);
  }
}

export class LocalEnvNode extends L_Node {
  constructor(public nodes: L_Node[]) {
    super();
  }

  override toString() {
    return `{${this.nodes.map((e) => e.toString()).join("; ")}}`;
  }
}

export class ReturnNode extends L_Node {
  constructor(public facts: ToCheckNode[]) {
    super();
  }
}

export class HaveNode extends L_Node {
  constructor(public opts: OptNode[], public vars: string[]) {
    super();
  }

  override toString() {
    const varsStr = this.vars.join(", ");
    return `have ${varsStr}: ${this.opts.toString()}`;
  }
}

export class SpecialNode extends L_Node {
  constructor(public keyword: string, public extra: unknown) {
    super();
  }
}

export class ByNode extends L_Node {
  constructor(public namedKnownToChecks: OptNode[]) {
    super();
  }

  override toString() {
    return `${this.namedKnownToChecks.map((e) => e.toString).join(", ")}`;
  }
}

export class DefCompositeNode extends L_Node {
  constructor(public composite: L_Composite, public facts: ToCheckNode[]) {
    super();
  }

  toString(): string {
    return `def_composite ${this.composite.toString()}: ${this.facts
      .map((e) => e.toString())
      .join(", ")}`;
  }
}

export abstract class BuiltinCheckNode extends ToCheckNode {}

export class IsPropertyNode extends BuiltinCheckNode {
  constructor(public propertyName: string, isT: boolean) {
    super(isT);
  }

  getRootOptNodes(): [OptNode, ToCheckNode[]][] {
    throw Error();
  }

  copyWithIsTReverse(): ToCheckNode {
    return new IsPropertyNode(this.propertyName, !this.isT);
  }

  fix(env: L_Env, freeFixPairs: [L_Symbol, L_Symbol][]): ToCheckNode {
    return this;
  }

  toString() {
    return `is_property(${this.propertyName})`;
  }

  varsDeclared(env: L_Env): boolean {
    return true;
  }
}

export class IsFormNode extends BuiltinCheckNode {
  constructor(
    public candidate: L_Symbol,
    public baseline: L_Composite,
    public facts: ToCheckNode[],
    isT: boolean
  ) {
    super(isT);
  }

  getRootOptNodes(): [OptNode, ToCheckNode[]][] {
    throw Error();
  }

  copyWithIsTReverse(): ToCheckNode {
    return new IsFormNode(this.candidate, this.baseline, this.facts, !this.isT);
  }

  fix(env: L_Env, freeFixPairs: [L_Symbol, L_Symbol][]): ToCheckNode {
    let fixed: L_Symbol | undefined = undefined;
    for (const freeFix of freeFixPairs) {
      if (L_Symbol.areLiterallyIdentical(env, freeFix[0], this.candidate)) {
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

  varsDeclared(env: L_Env): boolean {
    // TODO
    return true;
  }

  toString(): string {
    const notStr = this.isT ? "" : "[not]";
    const mainStr = `is_form(${this.candidate}, ${this.baseline}, {${this.facts}})`;
    return notStr + mainStr;
  }
}

export abstract class ToCheckFormulaNode extends ToCheckNode {
  constructor(
    public left: OptNode | ToCheckFormulaNode,
    public right: OptNode | ToCheckFormulaNode,
    isT: boolean
  ) {
    super(isT);
  }

  getWhereIsGivenFactAndAnotherBranch(fact: ToCheckNode): {
    where: FormulaSubNode;
    anotherBranch: FormulaSubNode;
  } {
    if (fact === this.left) {
      return { where: this.left, anotherBranch: this.right };
    } else if (fact === this.right) {
      return { where: this.right, anotherBranch: this.left };
    }

    throw Error();
  }

  varsDeclared(env: L_Env): boolean {
    //TODO
    return true;
  }

  fix(env: L_Env, freeFixPairs: [L_Symbol, L_Symbol][]): ToCheckFormulaNode {
    const left = this.left.fix(env, freeFixPairs);
    const right = this.right.fix(env, freeFixPairs);
    if (this instanceof OrToCheckNode) {
      return new OrToCheckNode(left, right, this.isT);
    } else if (this instanceof AndToCheckNode) {
      return new AndToCheckNode(left, right, this.isT);
    }

    throw Error();
  }

  copyWithIsTReverse(): ToCheckNode {
    throw Error();
  }

  getLeftRight(): ToCheckNode[] {
    return [this.left, this.right];
  }

  whereIsOpt(opt: OptNode) {
    const out = { left: false, right: false };
    if (this.left instanceof OptNode) {
      if (opt.optSymbol.name === this.left.optSymbol.name) {
        out.left = true;
      }
    } else if (this.left instanceof ToCheckFormulaNode) {
      const got = this.left.whereIsOpt(opt);
      if (got.left || got.right) out.left = true;
    }

    if (this.right instanceof OptNode) {
      if (opt.optSymbol.name === this.right.optSymbol.name) {
        out.right = true;
      }
    } else if (this.right instanceof ToCheckFormulaNode) {
      const got = this.right.whereIsOpt(opt);
      if (got.left || got.right) out.right = true;
    }

    return out;
  }
}

export class OrToCheckNode extends ToCheckFormulaNode {
  copyWithIsTReverse(): ToCheckNode {
    return new OrToCheckNode(this.left, this.right, !this.isT);
  }

  getRootOptNodes(): [OptNode, ToCheckNode[]][] {
    const out: [OptNode, ToCheckNode[]][] = [];
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

  getRootOpts(): OptNode[] | null {
    const allRoots: OptNode[] = [];
    for (const subNode of this.getLeftRight()) {
      if (subNode instanceof OrToCheckNode) {
        const roots = subNode.getRootOpts();
        if (roots === null) {
          return null;
        } else {
          allRoots.push(...roots);
        }
      } else if (subNode instanceof OptNode) {
        allRoots.push(subNode);
      } else {
        return null;
      }
    }

    return allRoots;
  }

  // If not all subNodes are either orNode or optNode, return null;
  getEquivalentIfs(): IfNode[] | null {
    const roots = this.getRootOpts();
    if (roots === null) return null;

    const out = roots.map((root, i) => {
      let others = roots.filter((e, j) => j !== i);
      others = others.map((e) => e.copyWithIsTReverse());
      return new IfNode([], others, [root]);
    });

    return out;
  }
}

export class AndToCheckNode extends ToCheckFormulaNode {
  copyWithIsTReverse(): ToCheckNode {
    return new AndToCheckNode(this.left, this.right, !this.isT);
  }

  getRootOptNodes(): [OptNode, ToCheckNode[]][] {
    const out: [OptNode, ToCheckNode[]][] = [];
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

export type FormulaSubNode = ToCheckFormulaNode | OptNode;

export class LetsNode extends L_Node {
  constructor(
    public name: string,
    public regex: RegExp,
    public facts: ToCheckNode[]
  ) {
    super();
  }

  toString() {
    return `lets ${this.name} ${this.regex} : ${this.facts
      .map((e) => e.toString())
      .join(", ")}`;
  }
}
