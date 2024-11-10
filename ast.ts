import { L_Env } from "./L_Env.ts";

export abstract class L_Node {}

export class FactNode extends L_Node {
  useName: string = "";

  constructor(public isT: boolean) {
    super();
  }

  varsDeclared(env: L_Env, freeVars: string[]): boolean {
    env;
    freeVars;
    return false;
  }

  factsDeclared(env: L_Env): boolean {
    env;
    return false;
  }

  useMapToCopy(map: Map<string, string>): FactNode {
    map;
    return new FactNode(true);
  }

  copyWithoutIsT(newIsT: boolean): FactNode {
    return new FactNode(newIsT);
  }
}

export class OrNode extends FactNode {
  constructor(public facts: FactNode[], isT: boolean = true) {
    super(isT);
  }

  override varsDeclared(env: L_Env, freeVars: string[]): boolean {
    return this.facts.every((e) => e.varsDeclared(env, freeVars));
  }

  override factsDeclared(env: L_Env): boolean {
    return this.facts.every((e) => e.factsDeclared(env));
  }

  override copyWithoutIsT(newIsT: boolean): FactNode {
    return new OrNode(this.facts, newIsT);
  }

  override toString(): string {
    return `ors{${this.facts.map((e) => e.toString()).join(", ")}}`;
  }
}

export class IfIffNode extends FactNode {
  constructor(
    public vars: string[] = [],
    public req: FactNode[] = [],
    //! I think we should onlyIfs: FactNode[] because despite we can not store if-then
    //! we can still check it.
    public onlyIfs: FactNode[] = [],
    isT: boolean = true,
    public byName: undefined | string = undefined,
    public isIff: boolean = false
  ) {
    super(isT);
  }

  override copyWithoutIsT(newIsT: boolean): IfIffNode {
    return new IfIffNode(
      this.vars,
      this.req,
      this.onlyIfs,
      newIsT,
      this.byName,
      this.isIff
    );
  }

  override useMapToCopy(map: Map<string, string>): IfIffNode {
    const newVars = [...this.vars];
    const req = this.req.map((e) => e.useMapToCopy(map));
    const onlyIfs = this.onlyIfs.map((e) => e.useMapToCopy(map));

    if (this instanceof IfIffNode)
      return new IfIffNode(newVars, req, onlyIfs, this.isT, this.byName);

    throw Error();
  }

  override toString() {
    let type: string = "";
    let separator = "";

    type = "if";
    separator = "=>";

    const mainPart = `${type} ${this.vars.toString()} : ${this.req
      .map((e) => e.toString())
      .join(", ")} ${separator} {${this.onlyIfs
      .map((e) => e.toString())
      .join(", ")}}`;
    const useNamePart = this.useName !== "" ? `[${this.useName}]` : "";
    const notPart = !this.isT ? "[not] " : "";

    return notPart + mainPart + useNamePart;
  }

  override varsDeclared(env: L_Env, freeVars: string[]): boolean {
    return [...this.req, ...this.onlyIfs].every((e) =>
      e.varsDeclared(env, [...this.vars, ...freeVars])
    );
  }

  override factsDeclared(env: L_Env): boolean {
    return [...this.req, ...this.onlyIfs].every((e) => e.factsDeclared(env));
  }
}

export class ExistNode extends IfIffNode {
  override toString(): string {
    return `${this.vars}: ${[...this.req, ...this.onlyIfs].join(", ")}`;
  }

  getContraPositive() {
    const nots = new OrNode(
      this.onlyIfs.map((e) => {
        e.isT = !e.isT;
        return e;
      }),
      true
    );
    const ifThen = new IfIffNode(
      this.vars,
      this.req,
      [nots],
      true,
      this.byName,
      false
    );
    return ifThen;
  }

  static ifThenToExist(ifThen: IfIffNode): ExistNode {
    if (ifThen.isT !== false || ifThen.byName === undefined) throw Error;
    const nots = new OrNode(
      ifThen.onlyIfs.map((e) => {
        e.isT = !e.isT;
        return e;
      })
    );

    return new ExistNode(
      ifThen.vars,
      ifThen.req,
      [nots],
      true,
      ifThen.byName,
      false
    );
  }
}

// export class IfIffNode extends LogicalOptNode {}
// export class OnlyIfNode extends LogicalOptNode {}
// export class IffNode extends LogicalOptNode {}

export class OptNode extends FactNode {
  constructor(
    public fullName: string,
    public vars: string[],
    isT: boolean = true
  ) {
    super(isT);
  }

  override copyWithoutIsT(newIsT: boolean): OptNode {
    return new OptNode(this.fullName, this.vars, newIsT);
  }

  override useMapToCopy(map: Map<string, string>): OptNode {
    const newVars: string[] = [];
    for (const v of this.vars) {
      const fixed = map.get(v);
      if (fixed === undefined) throw Error();
      else {
        newVars.push(fixed);
      }
    }
    return new OptNode(this.fullName, newVars, this.isT);
  }

  override toString() {
    const mainPart = this.fullName + `(${this.vars.join(", ")})`;
    const useNamePart = this.useName !== "" ? `[${this.useName}]` : "";
    const notPart = !this.isT ? "[not] " : "";
    return notPart + mainPart + useNamePart;
  }

  override varsDeclared(env: L_Env, freeVars: string[]): boolean {
    for (const v of this.vars) {
      const declared = env.varDeclared(v) || freeVars.includes(v);
      if (!declared) {
        env.newMessage(`${v} not declared in ${this.fullName}`);
        return false;
      }
    }
    return true;
  }

  override factsDeclared(env: L_Env): boolean {
    if (env.optDeclared(this.fullName)) {
      return true;
    } else {
      env.newMessage(`${this.fullName} not declared.`);
      return false;
    }
  }
}

export class DeclNode extends L_Node {
  constructor(
    public name: string = "",
    public vars: string[] = [],
    public req: FactNode[] = [],
    public onlyIfs: FactNode[] = [],
    public byName: string | undefined = undefined
  ) {
    super();
  }

  override toString() {
    if (this instanceof IfThenDeclNode)
      return `def if ${this.name}(${this.vars})`;
    else if (this instanceof IffDeclNode)
      return `def iff ${this.name}(${this.vars})`;
    else if (this instanceof OnlyIfDeclNode)
      return `def only_if ${this.name}(${this.vars})`;
    else return `Declaration Error`;
  }
}

export class IffDeclNode extends DeclNode {}
export class IfThenDeclNode extends DeclNode {}
export class OnlyIfDeclNode extends DeclNode {}

export class KnowNode extends L_Node {
  isKnowEverything: boolean = false;

  constructor(public facts: FactNode[] = [], public strict: boolean) {
    super();
  }

  override toString(): string {
    return (
      "know: " + this.facts.map((e) => (e as FactNode).toString()).join("; ")
    );
  }
}

export class LetNode extends L_Node {
  constructor(
    public vars: string[],
    public facts: FactNode[],
    public strict: boolean
  ) {
    super();
  }

  override toString() {
    return `${this.vars.join(", ")}: ${this.facts
      .map((s) => s.toString())
      .join(", ")}`;
  }
}

export class ProveNode extends L_Node {
  constructor(
    // Only one of toProve, fixedIfThenOpt exists
    public toProve: IfIffNode | null,
    public fixedIfThenOpt: OptNode | null,
    public block: L_Node[],
    // If contradict !== undefined, then prove_by_contradiction
    public contradict: OptNode | undefined = undefined
  ) {
    super();
  }

  override toString() {
    if (this.toProve) return `prove ${this.toProve}`;
    else return `prove ${this.fixedIfThenOpt}`;
  }
}

export class HaveNode extends L_Node {
  constructor(public vars: string[], public facts: OptNode[]) {
    super();
  }

  override toString() {
    return `${this.vars.join(", ")}| ${this.facts
      .map((s) => s.toString())
      .join(", ")}`;
  }
}

export class PostfixProve extends L_Node {
  constructor(public facts: FactNode[], public block: L_Node[]) {
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
  constructor(public facts: FactNode[]) {
    super();
  }
}

// export class ReturnExistNode extends L_Node {
//   constructor(public factNames: string[]) {
//     super();
//   }
// }

export class ByNode extends L_Node {
  constructor(
    public byName: string,
    public vars: string[],
    public onlyIfs: FactNode[]
  ) {
    super();
  }

  override toString() {
    return `${this.byName}(${this.vars.join(", ")}) is valid`;
  }
}

export class STNode extends L_Node {
  constructor(public byName: string, public vars: string[]) {
    super();
  }

  override toString() {
    return `${this.byName}(${this.vars.join(", ")}) is valid`;
  }
}
