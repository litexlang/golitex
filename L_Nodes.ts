import { L_Env } from "./L_Env";
import { L_Composite, L_OptSymbol, L_Singleton, L_Symbol } from "./L_Structs";

export abstract class L_Node {}

export abstract class ToCheckNode extends L_Node {
  constructor(public isT: boolean) {
    super();
  }

  // called by L_Memory
  abstract varsDeclared(env: L_Env, varsFromAbove: L_Symbol[]): boolean;

  // called by checker
  abstract fix(env: L_Env, freeFixPairs: [L_Symbol, L_Symbol][]): ToCheckNode;

  // called by prove_by_contradiction
  abstract copyWithIsTReverse(): ToCheckNode;

  static getRootOptNodes(
    currentNode: ToCheckFormulaNode | IfNode,
    fromAbove: (ToCheckFormulaNode | IfNode)[] = []
  ): [OptNode, (ToCheckFormulaNode | IfNode)[]][] {
    let toGets: ToCheckNode[] = [];
    if (currentNode instanceof ToCheckFormulaNode) {
      toGets = currentNode.getLeftRight();
    } else if (currentNode instanceof IfNode) {
      toGets = currentNode.onlyIfs;
    }
    const out: [OptNode, (ToCheckFormulaNode | IfNode)[]][] = [];

    for (const toGet of toGets) {
      if (toGet instanceof OptNode) {
        out.push([toGet, [...fromAbove, currentNode]]);
      } else if (toGet instanceof ToCheckFormulaNode) {
        let below: [OptNode, (ToCheckFormulaNode | IfNode)[]][] =
          ToCheckNode.getRootOptNodes(toGet, [...fromAbove, currentNode]);
        out.push(...below);
      } else if (toGet instanceof IfNode) {
        let below: [OptNode, (ToCheckFormulaNode | IfNode)[]][] =
          ToCheckNode.getRootOptNodes(toGet, [...fromAbove, currentNode]);
        below = below.map((e) => [e[0], [...fromAbove, currentNode, ...e[1]]]);
        out.push(...below);
      }
    }

    return out;
  }
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

  varsDeclared(env: L_Env, varsFromAbove: L_Symbol[]): boolean {
    // TODO make sure composite in vars are declared
    const singletonsInVars = [];
    for (const v of this.vars) {
      if (v instanceof L_Composite) {
        //TODO I am not satisfied with this semantics
        if (!v.declared(env, [...varsFromAbove, ...singletonsInVars])) {
          return false;
        }
      } else if (v instanceof L_Singleton) {
        singletonsInVars.push(v);
      }
    }

    return (
      this.req.every((e) =>
        e.varsDeclared(env, [...varsFromAbove, ...this.vars])
      ) &&
      this.onlyIfs.every((e) =>
        e.varsDeclared(env, [...varsFromAbove, ...this.vars])
      )
    );
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

  examineVarsNotDoubleDecl(varsFromAboveIf: string[]): boolean {
    return false;
    // TODO
    // const ok = this.vars.every((e) => !varsFromAboveIf.includes(e));
    // if (!ok) return false;
    // varsFromAboveIf = [...varsFromAboveIf, ...this.vars];
    // return this.onlyIfs.every(
    //   (e) =>
    //     !(e instanceof LogicNode) || e.examineVarsNotDoubleDecl(varsFromAboveIf)
    // );
  }

  override copyWithIsTReverse(): LogicNode {
    return new LogicNode(this.vars, this.req, this.onlyIfs, !this.isT);
  }

  override toString() {
    let type: string = "";
    let separator = "";

    type = "if";

    const mainPart = `${type} ${this.vars.toString()} : ${this.req
      .map((e) => e.toString())
      .join(", ")} {${this.onlyIfs.map((e) => e.toString()).join(", ")}}`;
    const notPart = !this.isT ? "[not] " : "";

    // const defName = this.defName === undefined ? "" : `[${this.defName}]`;

    return notPart + mainPart;
  }

  // extract root of if-then. get operator-fact and its requirements. return operator-fact-requirement-pair.
  // getRootOptNodes(
  //   fromAbove: ToCheckFormulaNode[] = []
  // ): [OptNode, (IfNode | ToCheckFormulaNode)[]][] {
  //   const out: [OptNode, (IfNode | ToCheckFormulaNode)[]][] = [];
  //   for (const onlyIf of this.onlyIfs) {
  //     if (onlyIf instanceof OptNode) {
  //       out.push([onlyIf, [this]]);
  //     } else if (onlyIf instanceof LogicNode) {
  //       const roots = onlyIf.getRootOptNodes();
  //       for (const root of roots) {
  //         out.push([root[0], [this, ...root[1]]]);
  //       }
  //     } else if (onlyIf instanceof ToCheckFormulaNode) {
  //       const below = onlyIf.getRootOptNodes([...fromAbove, this]);
  //       out.push(...below);
  //     }
  //   }
  //   return out;
  // }
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

  varsDeclared(env: L_Env, varsFromAbove: L_Symbol[]): boolean {
    return (
      this.vars.every((e) => e.declared(env, varsFromAbove)) &&
      (this.checkVars === undefined ||
        this.checkVars.every((arr) =>
          arr.every((e) => e.declared(env, varsFromAbove))
        ))
    );
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

  override copyWithIsTReverse(): ToCheckNode {
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

export class PostfixProve extends L_Node {
  constructor(
    public facts: ToCheckNode[],
    public block: L_Node[],
    public names: string[]
  ) {
    super();
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

export class MacroNode extends L_Node {
  constructor(
    public regexString: string,
    public varName: string,
    public facts: ToCheckNode[]
  ) {
    super();
  }

  override toString() {
    return `regex string: ${this.regexString}, var: ${this.varName}, facts: ${this.facts}`;
  }

  testRegex(testStr: string): boolean {
    try {
      const regex = new RegExp(this.regexString);
      return regex.test(testStr);
    } catch (error) {
      console.error("Invalid Regular Expression:", error);
      return false;
    }
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

  copyWithIsTReverse(): ToCheckNode {
    return new IsPropertyNode(this.propertyName, !this.isT);
  }

  fix(env: L_Env, freeFixPairs: [L_Symbol, L_Symbol][]): ToCheckNode {
    return this;
  }

  toString() {
    return `is_property(${this.propertyName})`;
  }

  varsDeclared(env: L_Env, varsFromAbove: L_Symbol[]): boolean {
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

  copyWithIsTReverse(): ToCheckNode {
    return new IsFormNode(this.candidate, this.baseline, this.facts, !this.isT);
  }

  fix(env: L_Env, freeFixPairs: [L_Symbol, L_Symbol][]): ToCheckNode {
    let fixed: L_Symbol | undefined = undefined;
    for (const freeFix of freeFixPairs) {
      if (
        L_Symbol.literallyCompareTwoSymbols(env, freeFix[0], this.candidate)
      ) {
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

  varsDeclared(env: L_Env, varsFromAbove: L_Symbol[]): boolean {
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
    public left: ToCheckNode,
    public right: ToCheckNode,
    isT: boolean
  ) {
    super(isT);
  }

  // getRootOptNodes(
  //   fromAbove: (ToCheckFormulaNode | IfNode)[] = []
  // ): [OptNode, (ToCheckFormulaNode | IfNode)[]][] {
  //   const out: [OptNode, (ToCheckFormulaNode | IfNode)[]][] = [];
  //   const toGets = [this.left, this.right];
  //   for (const toGet of toGets) {
  //     if (toGet instanceof OptNode) {
  //       out.push([toGet, [...fromAbove, this]]);
  //     } else if (toGet instanceof ToCheckFormulaNode) {
  //       const below = toGet.getRootOptNodes([...fromAbove, this]);
  //       out.push(...below);
  //     } else if (toGet instanceof IfNode) {
  //       let below: [OptNode, (ToCheckFormulaNode | IfNode)[]][] =
  //         toGet.getRootOptNodes();
  //       below = below.map((e) => [e[0], [...fromAbove, this, ...e[1]]]);
  //       out.push(...below);
  //     }
  //   }

  //   return out;
  // }

  varsDeclared(env: L_Env, varsFromAbove: L_Symbol[]): boolean {
    //TODO
    return true;
  }

  fix(env: L_Env, freeFixPairs: [L_Symbol, L_Symbol][]): ToCheckNode {
    this.left.fix(env, freeFixPairs);
    this.right.fix(env, freeFixPairs);
    return this;
  }

  copyWithIsTReverse(): ToCheckNode {
    throw Error();
  }

  getLeftRight(): ToCheckNode[] {
    return [this.left, this.right];
  }
}

export class OrToCheckNode extends ToCheckFormulaNode {
  copyWithIsTReverse(): ToCheckNode {
    return new OrToCheckNode(this.left, this.right, !this.isT);
  }

  toString() {
    return `(${this.left} or ${this.right})`;
  }
}

export class AndToCheckNode extends ToCheckFormulaNode {
  copyWithIsTReverse(): ToCheckNode {
    return new AndToCheckNode(this.left, this.right, !this.isT);
  }

  toString() {
    return `(${this.left} and ${this.right})`;
  }
}
