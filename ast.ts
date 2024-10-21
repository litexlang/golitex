export abstract class L_Node {}

export enum FactType {
  Or,
  IfThen,
  Def,
}

export abstract class FactNode extends L_Node {
  isT: Boolean = true;
  useName: string = "";
}

export class OrNode extends FactNode {
  constructor(public facts: FactNode[]) {
    super();
    this.facts = facts;
  }
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
    this.req = req;
    this.onlyIfs = onlyIfs;
  }

  toString() {
    const mainPart = `if ${this.freeVars.toString()} | ${this.req.map((e) => e.toString()).join(", ")} => {${this.onlyIfs.map((e) => e.toString()).join(", ")}}`;
    const useNamePart = this.useName !== "" ? `[${this.useName}]` : "";
    return mainPart + useNamePart;
  }
}

export class ShortCallOptNode extends FactNode {
  constructor(
    public fullName: string,
    public params: string[][]
  ) {
    super();
    this.fullName = fullName;
    this.params = params;
  }

  nameAsLst() {
    return this.fullName.split(":");
  }

  toString() {
    const mainPart = this.nameAsLst()
      .map((name, i) => `${name}(${this.params[i]})`)
      .join(":");
    const useNamePart = this.useName !== "" ? `[${this.useName}]` : "";
    return mainPart + useNamePart;
  }
}

export class ByNode extends FactNode {
  constructor(
    public fact: FactNode,
    public bys: FactNode[]
  ) {
    super();
  }
}

export abstract class DeclNode extends L_Node {
  constructor(
    public name: string = "",
    public freeVars: string[] = [],
    public req: FactNode[] = [],
    public onlyIfs: ShortCallOptNode[] = []
  ) {
    super();
    this.name = name;
    this.freeVars = freeVars;
    this.req = req;
    this.onlyIfs = onlyIfs;
  }
}

export class DefDeclNode extends DeclNode {}
export class IfThenDeclNode extends DeclNode {}

export class KnowNode extends L_Node {
  isKnowEverything: Boolean = false;

  constructor(public facts: FactNode[] = []) {
    super();
    this.facts = facts;
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
    this.vars = vars;
    this.facts = facts;
  }

  toString() {
    return `${this.vars.join(", ")}| ${this.facts.map((s) => s.toString()).join(", ")}`;
  }
}
