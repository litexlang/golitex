import { L_Env } from "./L_Env";
import { L_KW } from "./L_Keywords";
import { OptSymbol } from "./L_Structs";
import { L_Composite, L_Singleton, L_Symbol } from "./L_Symbols";
import { OptFactNode, L_FactNode } from "./L_Facts";

export abstract class L_Node {}

export class DefConceptNode extends L_Node {
  constructor(
    public opt: OptFactNode,
    public cond: L_FactNode[], // TODO, 类似composite的要求
    public onlyIfs: L_FactNode[],
    public commutative: boolean
  ) {
    super();
  }

  override toString(): string {
    return `${this.opt.toString()};`;
  }
}

export class KnowNode extends L_Node {
  isKnowEverything: boolean = false;

  constructor(public facts: L_FactNode[], public names: string[]) {
    super();
  }

  override toString(): string {
    return `${L_KW.Know} ${this.facts};`;
  }
}

export class LetNode extends L_Node {
  constructor(public vars: string[], public facts: L_FactNode[]) {
    super();
  }

  override toString() {
    return `${L_KW.Let} ${this.vars}: ${this.facts};`;
  }
}

// export class LetFormalSymbolNode extends L_Node {
//   constructor(public vars: string[], public facts: L_FactNode[]) {
//     super();
//   }

//   override toString() {
//     return `${L_KW.LetFormal} ${this.vars}: ${this.facts};`;
//   }
// }

export class ProveNode extends L_Node {
  constructor(public toProve: L_FactNode, public block: L_Node[]) {
    super();
  }

  override toString() {
    return `${L_KW.Prove} ${this.toProve}`;
  }
}
export class ProveContradictNode extends L_Node {
  constructor(
    public toProve: L_FactNode,
    public block: L_Node[],
    public contradict: OptFactNode
  ) {
    super();
  }

  override toString() {
    return `${L_KW.ProveByContradiction} ${this.toProve}`;
  }
}

export class LocalEnvNode extends L_Node {
  constructor(public nodes: L_Node[], public localEnv: L_Env) {
    super();
  }

  override toString() {
    return `{${this.nodes.map((e) => e.toString()).join("; ")}}`;
  }
}

export class HaveNode extends L_Node {
  constructor(public vars: L_Singleton[], public fact: OptFactNode) {
    super();
  }

  override toString() {
    return `${L_KW.Have} ${this.vars}: ${this.fact}`;
  }
}

export class DefOperatorNode extends L_Node {
  constructor(public composite: L_Composite, public facts: L_FactNode[]) {
    super();
  }

  toString(): string {
    return `${L_KW.DefOperator} ${this.composite}: ${this.facts}`;
  }
}

export class LetsNode extends L_Node {
  constructor(
    public name: string,
    public regex: RegExp,
    public facts: L_FactNode[]
  ) {
    super();
  }

  toString() {
    return `lets ${this.name} ${this.regex} : ${this.facts
      .map((e) => e.toString())
      .join(", ")}`;
  }
}

export class IncludeNode extends L_Node {
  constructor(public path: string) {
    super();
  }

  toString() {
    return `include "${this.path}";`;
  }
}

export class DefLiteralOptNode extends L_Node {
  constructor(
    public name: string,
    public vars: L_Symbol[],
    public facts: L_FactNode[],
    public path: string,
    public func: string
  ) {
    super();
  }
}

// export class DefFunctionalSymbolNode extends L_Node {
//   constructor(
//     public functional: FunctionalSymbol,
//     public facts: ToCheckNode[]
//   ) {
//     super();
//   }

//   toString(): string {
//     return `${L_Keywords.DefFunctional} ${this.functional}: ${this.facts}`;
//   }
// }

export class LetAliasNode extends L_Node {
  constructor(public name: L_Singleton, public toBeAliased: L_Symbol[]) {
    super();
  }

  toString() {
    return `${L_KW.LetAlias} ${this.name} ${this.toBeAliased}`;
  }
}

// The Followings are half implemented. --------------------------------------
