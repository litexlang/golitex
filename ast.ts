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
}

export class OrNode extends FactNode {
  constructor(public facts: FactNode[]) {
    super();
  }

  hashVars(varsToHash: string[]) {}
  rmvHashFromVars(varsToHash: string[]): void {}
  replaceVars(mapping: Map<string, string>): void {}
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

  rmvHashFromVars(varsToHash: string[]): void {
    this.freeVars = this.freeVars.map((s) =>
      varsToHash.includes(s.slice(1)) && s[0] === "#" ? s.slice(1) : s
    );
    this.req.forEach((e) => e.rmvHashFromVars(varsToHash));
    this.onlyIfs.forEach((e) => e.rmvHashFromVars(varsToHash));
  }

  replaceVars(mapping: Map<string, string>): void {
    for (let i = 0; i < this.freeVars.length; i++) {
      const fixed = mapping.get(this.freeVars[i]);
      if (fixed !== undefined) this.freeVars[i] = fixed;
    }
    this.req.forEach((e) => e.replaceVars(mapping));
    this.onlyIfs.forEach((e) => e.replaceVars(mapping));
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
}

export class ByNode extends FactNode {
  constructor(
    public facts: FactNode[],
    public block: FactNode[]
  ) {
    super();
  }

  hashVars(varsToHash: string[]) {}
  rmvHashFromVars(varsToHash: string[]): void {}
  replaceVars(mapping: Map<string, string>): void {}
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

  replaceVars(givenOpt: ShortCallOptNode) {
    const mapping = new Map<string, string>();
    this.freeVars.forEach((v, i) => {
      mapping.set(v, givenOpt.vars[i]);
    });
    this.freeVars.forEach((v, i) => (this.freeVars[i] = givenOpt.vars[i]));
    this.req.forEach((v) => v.replaceVars(mapping));
    this.onlyIfs.forEach((v) => v.replaceVars(mapping));
  }

  rmvHashFromVars(varsToHash: string[]) {
    this.req.forEach((v) => v.rmvHashFromVars(varsToHash));
    this.onlyIfs.forEach((v) => v.rmvHashFromVars(varsToHash));
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
    // Only one of toProve, fixedIfThenOpt exists
    public toProve: IfThenNode | null,
    public fixedIfThenOpt: ShortCallOptNode | null,
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
