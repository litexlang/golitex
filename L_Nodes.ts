import { L_Env } from "./L_Env";
import { L_Composite, L_OptSymbol, L_Singleton, L_Symbol } from "./L_Structs";

export abstract class L_Node {}

export class ToCheckNode extends L_Node {
  constructor(public isT: boolean) {
    super();
  }

  // called by checker
  fix(env: L_Env, freeFixPairs: [L_Symbol, L_Symbol][]): ToCheckNode {
    throw Error();
  }

  // called by prove_by_contradiction
  copyWithIsTReverse(): ToCheckNode {
    return new ToCheckNode(!this.isT);
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
  getRootNodes(): [OptNode, IfNode[]][] {
    const out: [OptNode, IfNode[]][] = [];
    for (const onlyIf of this.onlyIfs) {
      if (onlyIf instanceof OptNode) {
        out.push([onlyIf, [this]]);
      } else if (onlyIf instanceof LogicNode) {
        const roots = onlyIf.getRootNodes();
        for (const root of roots) {
          out.push([root[0], [this, ...root[1]]]);
        }
      }
    }
    return out;
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
  constructor(
    public vars: string[],
    public facts: ToCheckNode[],
    public names: string[]
  ) {
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

export class BuiltinCheckNode extends ToCheckNode {}

export class IsPropertyNode extends BuiltinCheckNode {
  constructor(public propertyName: string, isT: boolean) {
    super(isT);
  }

  toString() {
    return `is_property(${this.propertyName})`;
  }
}

export class OrNode extends BuiltinCheckNode {
  constructor(public opts: OptNode[], isT: boolean) {
    super(isT);
  }
}

export class isSymbolShapeNode extends BuiltinCheckNode {
  constructor(
    public templateSymbol: L_Symbol,
    public givenSymbol: L_Symbol,
    public factsEMustSatisfy: ToCheckNode[],
    isT: boolean
  ) {
    super(isT);
  }
}
