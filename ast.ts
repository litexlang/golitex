import { IffKeywords, IfKeywords, OnlyIfKeywords } from "./common";

export abstract class L_Node {}

export abstract class FactNode extends L_Node {
  isT: Boolean = true;
  useName: string = "";

  /**
   * Currently, when executing declaration of facts, we update all facts within the declNode in-place by adding or removing #prefix
   * @param varsToHash
   */
  abstract hashVars(varsToHash: string[]): void;
  abstract rmvHashFromVars(varsToHash: string[]): void;

  /**
   * Used when replacing all free variables in the declared node with the given variables
   * @param mapping key = free variable, value = given variable
   */
  abstract replaceVars(mapping: Map<string, string>): void;

  /**
   * copy() is necessary because when we store hashed facts by using declNode (to improve performance) but when proving we need to fix declNode with given variables.
   */
  abstract copy(): FactNode;
}

export class OrNode extends FactNode {
  constructor(public facts: FactNode[]) {
    super();
  }

  hashVars(varsToHash: string[]) {}
  rmvHashFromVars(varsToHash: string[]): void {}
  replaceVars(mapping: Map<string, string>): void {}
  copy(): OrNode {
    return new OrNode([]);
  }
}

export abstract class LogicalOptNode extends FactNode {
  constructor(
    public vars: string[] = [],
    public req: FactNode[] = [],
    //! I think we should onlyIfs: FactNode[] because despite we can not store if-then
    //! we can still check it.
    public onlyIfs: FactNode[] = []
  ) {
    super();
  }

  toString() {
    let type: string = "";
    let separator = "";
    if (this instanceof IffNode) {
      type = "iff";
      separator = "<=>";
    } else if (this instanceof IfThenNode) {
      type = "if";
      separator = "=>";
    } else if (this instanceof OnlyIfNode) {
      type = "only_if";
      separator = "<=";
    }

    const mainPart = `${type} ${this.vars.toString()} | ${this.req.map((e) => e.toString()).join(", ")} ${separator} ${this.onlyIfs.map((e) => e.toString()).join(", ")}`;
    const useNamePart = this.useName !== "" ? `[${this.useName}]` : "";
    const notPart = !this.isT ? "[not] " : "";

    return notPart + mainPart + useNamePart;
  }

  hashVars(varsToHash: string[]) {
    this.vars = this.vars.map((s) => (varsToHash.includes(s) ? "#" + s : s));
    this.req.forEach((e) => e.hashVars(varsToHash));
    this.onlyIfs.forEach((e) => e.hashVars(varsToHash));
  }

  rmvHashFromVars(varsToHash: string[]): void {
    this.vars = this.vars.map((s) =>
      varsToHash.includes(s.slice(1)) && s[0] === "#" ? s.slice(1) : s
    );
    this.req.forEach((e) => e.rmvHashFromVars(varsToHash));
    this.onlyIfs.forEach((e) => e.rmvHashFromVars(varsToHash));
  }

  replaceVars(mapping: Map<string, string>): void {
    for (let i = 0; i < this.vars.length; i++) {
      const fixed = mapping.get(this.vars[i]);
      if (fixed !== undefined) this.vars[i] = fixed;
    }
    this.req.forEach((e) => e.replaceVars(mapping));
    this.onlyIfs.forEach((e) => e.replaceVars(mapping));
  }

  copy(): LogicalOptNode {
    const req: FactNode[] = [];
    for (const r of this.req) {
      req.push(r.copy());
    }
    const onlyIfs: FactNode[] = [];
    for (const onlyIf of this.onlyIfs) {
      onlyIfs.push(onlyIf.copy());
    }
    const vars = [...this.vars];

    if (this instanceof IfThenNode) {
      return new IfThenNode(vars, req, onlyIfs);
    }
    if (this instanceof IffNode) {
      return new IffNode(vars, req, onlyIfs);
    }
    if (this instanceof OnlyIfNode) {
      return new OnlyIfNode(vars, req, onlyIfs);
    }
    throw Error();
  }

  static create(
    type: string,
    vars: string[],
    req: FactNode[],
    onlyIfs: FactNode[]
  ): LogicalOptNode {
    if (IfKeywords.includes(type)) {
      return new IfThenNode(vars, req, onlyIfs);
    } else if (IffKeywords.includes(type)) {
      return new IffNode(vars, req, onlyIfs);
    } else if (OnlyIfKeywords.includes(type)) {
      return new OnlyIfNode(vars, req, onlyIfs);
    }
    throw Error();
  }
}

export class IfThenNode extends LogicalOptNode {}
export class OnlyIfNode extends LogicalOptNode {}
export class IffNode extends LogicalOptNode {}

export class OptNode extends FactNode {
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

  rmvHashFromVars(varsToHash: string[]): void {
    this.vars = this.vars.map((s) =>
      varsToHash.includes(s.slice(1)) && s[0] === "#" ? s.slice(1) : s
    );
  }

  replaceVars(mapping: Map<string, string>): void {
    this.vars.forEach((v, i) => {
      const fixed = mapping.get(v);
      if (fixed !== undefined) this.vars[i] = fixed;
    });
  }

  copy(): OptNode {
    return new OptNode(this.fullName, [...this.vars]);
  }
}

export abstract class DeclNode extends L_Node {
  // WHEN ADDING FIELD HERE, DON'T FORGET TO UPDATE copyTo()
  constructor(
    public name: string = "",
    public vars: string[] = [],
    public req: FactNode[] = [],
    public onlyIfs: FactNode[] = []
  ) {
    super();
  }

  static create(name: string, node: LogicalOptNode): DeclNode {
    if (node instanceof IfThenNode) {
      return new IfThenDeclNode(name, node.vars, node.req, node.onlyIfs);
    } else if (node instanceof IffNode) {
      return new IffDeclNode(name, node.vars, node.req, node.onlyIfs);
    } else if (node instanceof OnlyIfNode) {
      return new OnlyIfDeclNode(name, node.vars, node.req, node.onlyIfs);
    }
    throw Error();
  }

  toString() {
    return `${this.name}(${this.vars})`;
  }

  replaceVars(givenOpt: OptNode) {
    const mapping = new Map<string, string>();
    this.vars.forEach((v, i) => {
      mapping.set(v, givenOpt.vars[i]);
    });
    this.vars.forEach((v, i) => (this.vars[i] = givenOpt.vars[i]));
    this.req.forEach((v) => v.replaceVars(mapping));
    this.onlyIfs.forEach((v) => v.replaceVars(mapping));
  }

  // NOTE: vars of DeclNode itself are not hashed, only its subNodes are hashed.
  hashVars(varsToHash: string[]) {
    this.req.forEach((v) => v.hashVars(varsToHash));
    this.onlyIfs.forEach((v) => v.hashVars(varsToHash));
  }

  rmvHashFromVars(varsToHash: string[]) {
    this.req.forEach((v) => v.rmvHashFromVars(varsToHash));
    this.onlyIfs.forEach((v) => v.rmvHashFromVars(varsToHash));
  }

  copyTo(copyTo: DeclNode) {
    const vars = [...this.vars];
    const req: FactNode[] = [];
    for (const r of this.req) {
      req.push(r.copy());
    }
    const onlyIfs: FactNode[] = [];
    for (const onlyIf of this.onlyIfs) {
      onlyIfs.push(onlyIf.copy());
    }

    copyTo.name = this.name;
    copyTo.vars = vars;
    copyTo.onlyIfs = onlyIfs;
    copyTo.req = req;
  }
}

export class ExistNode extends DeclNode {
  public isT = false;
}
export class IffDeclNode extends DeclNode {}
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
    // Only one of toProve, fixedIfThenOpt exists
    public toProve: IfThenNode | null,
    public fixedIfThenOpt: OptNode | null,
    public block: L_Node[]
  ) {
    super();
  }

  toString() {
    if (this.toProve) return `prove ${this.toProve}`;
    else return `prove ${this.fixedIfThenOpt}`;
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

export class ByNode extends L_Node {
  constructor(
    public facts: FactNode[],
    public block: L_Node[]
  ) {
    super();
  }
}
