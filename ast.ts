export abstract class L_Node {}

// FactType does not have logical effects, it's only used when printing.
export enum FactType {
  Or = 1, // make sure all FactType is true in if
  IfThen,
  Def,
  OnlyIf,
  Exist,
}

export abstract class FactNode extends L_Node {
  isT: Boolean = true;
  useName: string = "";

  abstract hashVars(varsToHash: string[]): void;
}

export class OrNode extends FactNode {
  constructor(public facts: FactNode[]) {
    super();
  }

  hashVars(varsToHash: string[]) {}
}

export class IfThenNode extends FactNode {
  constructor(
    public freeVars: string[] = [],
    public req: FactNode[] = [],
    //! I think we should onlyIfs: FactNode[] because despite we can not store if-then
    //! we can still check it.
    public onlyIfs: FactNode[] = []
  ) {
    super();
  }

  toString() {
    const mainPart = `if ${this.freeVars.toString()} | ${this.req.map((e) => e.toString()).join(", ")} => {${this.onlyIfs.map((e) => e.toString()).join(", ")}}`;
    const useNamePart = this.useName !== "" ? `[${this.useName}]` : "";
    const notPart = !this.isT ? "[not] " : "";
    return notPart + mainPart + useNamePart;
  }

  hashVars(varsToHash: string[]) {
    this.freeVars = this.freeVars.map((s) =>
      varsToHash.includes(s) ? "#" + s : s
    );
    this.req.forEach((e) => e.hashVars(varsToHash));
    this.onlyIfs.forEach((e) => e.hashVars(varsToHash));
  }
}

export class ShortCallOptNode extends FactNode {
  constructor(
    public fullName: string,
    public vars: string[]
  ) {
    super();
  }

  toString() {
    const mainPart = this.fullName + `(${this.vars.join(", ")})`;
    const useNamePart = this.useName !== "" ? `[${this.useName}]` : "";
    const notPart = !this.isT ? "[not] " : "";
    return notPart + mainPart + useNamePart;
  }

  hashVars(varsToHash: string[]) {
    this.vars = this.vars.map((s) => (varsToHash.includes(s) ? "#" + s : s));
  }
}

export class ByNode extends FactNode {
  constructor(
    public facts: FactNode[],
    public block: FactNode[]
  ) {
    super();
  }

  hashVars(varsToHash: string[]) {}
}

export abstract class DeclNode extends L_Node {
  constructor(
    public name: string = "",
    public freeVars: string[] = [],
    public req: FactNode[] = [],
    public onlyIfs: ShortCallOptNode[] = []
  ) {
    super();
  }

  toString() {
    return `${this.name}(${this.freeVars})`;
  }
}

export class ExistNode extends DeclNode {
  public isT = false;
}
export class DefDeclNode extends DeclNode {}
export class IfThenDeclNode extends DeclNode {}
export class OnlyIfDeclNode extends DeclNode {}

export class KnowNode extends L_Node {
  isKnowEverything: Boolean = false;

  constructor(public facts: FactNode[] = []) {
    super();
  }

  toString(): string {
    return (
      "know: " + this.facts.map((e) => (e as FactNode).toString()).join("; ")
    );
  }
}

export class LetNode extends L_Node {
  constructor(
    public vars: string[],
    public facts: FactNode[]
  ) {
    super();
  }

  toString() {
    return `${this.vars.join(", ")}| ${this.facts.map((s) => s.toString()).join(", ")}`;
  }
}

export class ProveNode extends L_Node {
  constructor(
    public toProve: IfThenNode,
    public block: L_Node[]
  ) {
    super();
  }

  toString() {
    return `prove ${this.toProve}`;
  }
}

export class HaveNode extends L_Node {
  constructor(
    public vars: string[],
    public facts: FactNode[]
  ) {
    super();
  }

  toString() {
    return `${this.vars.join(", ")}| ${this.facts.map((s) => s.toString()).join(", ")}`;
  }
}

export class AssumeByContraNode extends L_Node {
  constructor(
    public assume: FactNode,
    public block: L_Node[],
    public contradict: FactNode
  ) {
    super();
  }

  toString() {
    return `assume_by_contradiction ${this.assume}`;
  }
}
