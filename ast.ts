import { L_Env } from "./L_Env.ts";

export abstract class L_Node {}

export class ToCheckNode extends L_Node {
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

  useMapToCopy(map: Map<string, string>): ToCheckNode {
    map;
    return new ToCheckNode(true);
  }

  copyWithoutIsT(newIsT: boolean): ToCheckNode {
    return new ToCheckNode(newIsT);
  }
}

export class OrNode extends ToCheckNode {
  constructor(public facts: ToCheckNode[], isT: boolean = true) {
    super(isT);
  }

  override varsDeclared(env: L_Env, freeVars: string[]): boolean {
    return this.facts.every((e) => e.varsDeclared(env, freeVars));
  }

  override factsDeclared(env: L_Env): boolean {
    return this.facts.every((e) => e.factsDeclared(env));
  }

  override copyWithoutIsT(newIsT: boolean): ToCheckNode {
    return new OrNode(this.facts, newIsT);
  }

  override toString(): string {
    return `ors{${this.facts.map((e) => e.toString()).join(", ")}}`;
  }
}

export class LogicNode extends ToCheckNode {
  constructor(
    public vars: string[] = [],
    public req: ToCheckNode[] = [],
    //! I think we should onlyIfs: ToCheckNode[] because despite we can not store if-then
    //! we can still check it.
    public onlyIfs: ToCheckNode[] = [],
    isT: boolean = true,
    public byName: undefined | string = undefined // public isIff: boolean = false
  ) {
    super(isT);
  }

  override copyWithoutIsT(newIsT: boolean): LogicNode {
    return new LogicNode(
      this.vars,
      this.req,
      this.onlyIfs,
      newIsT,
      this.byName
      // this.isIff
    );
  }

  override useMapToCopy(map: Map<string, string>): LogicNode {
    const newVars = [...this.vars];
    const req = this.req.map((e) => e.useMapToCopy(map));
    const onlyIfs = this.onlyIfs.map((e) => e.useMapToCopy(map));

    if (this instanceof LogicNode)
      return new LogicNode(newVars, req, onlyIfs, this.isT, this.byName);

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

export class ExistNode extends LogicNode {
  constructor(
    vars: string[] = [],
    req: ToCheckNode[] = [],
    onlyIfs: ToCheckNode[] = [],
    isT: boolean = true,
    byName: undefined | string = undefined
  ) {
    super(vars, req, onlyIfs, isT, byName);
  }

  override toString(): string {
    return `exist ${this.vars}: ${[...this.req, ...this.onlyIfs].join(", ")}`;
  }

  getContraPositive() {
    const nots = new OrNode(
      this.onlyIfs.map((e) => {
        e.isT = !e.isT;
        return e;
      }),
      true
    );
    const ifThen = new LogicNode(
      this.vars,
      this.req,
      [nots],
      true,
      this.byName
      // false
    );
    return ifThen;
  }

  static ifThenToExist(ifThen: LogicNode): ExistNode {
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
      ifThen.byName
      // false
    );
  }

  override useMapToCopy(map: Map<string, string>): ExistNode {
    const newVars = [...this.vars];
    const req = this.req.map((e) => e.useMapToCopy(map));
    const onlyIfs = this.onlyIfs.map((e) => e.useMapToCopy(map));

    return new ExistNode(newVars, req, onlyIfs, this.isT, this.byName);
  }

  override copyWithoutIsT(newIsT: boolean): ExistNode {
    return new ExistNode(
      this.vars,
      this.req,
      this.onlyIfs,
      newIsT,
      this.byName
    );
  }

  override varsDeclared(env: L_Env, freeVars: string[]): boolean {
    return super.varsDeclared(env, freeVars);
  }

  override factsDeclared(env: L_Env): boolean {
    return super.factsDeclared(env);
  }
}
export class IffNode extends LogicNode {}
export class IfNode extends LogicNode {
  useByToDecl(): IfThenDeclNode {
    return new DeclNode(this.byName, this.vars, this.req, this.onlyIfs);
  }
}

// export class LogicNode extends LogicalOptNode {}
// export class OnlyIfNode extends LogicalOptNode {}

export class OptNode extends ToCheckNode {
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
      if (fixed === undefined) {
        //! I DON'T KNOW WHETHER I SHOULD THROW ERROR OR PUSH PREVIOUS SYMBOL
        // throw Error();
        newVars.push(v);
      } else {
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
    public req: ToCheckNode[] = [],
    public onlyIfs: ToCheckNode[] = [],
    public byName: string | undefined = undefined
  ) {
    super();
  }

  override toString(): string {
    return "";
  }
}

export class IffDeclNode extends DeclNode {
  override toString(): string {
    return `def iff ${this.name}(${this.vars})`;
  }
}
export class IfThenDeclNode extends DeclNode {
  override toString(): string {
    return `def if ${this.name}(${this.vars})`;
  }
}
export class OnlyIfDeclNode extends DeclNode {
  override toString(): string {
    return `def only_if ${this.name}(${this.vars})`;
  }
}
export class ExistDeclNode extends DeclNode {
  override toString(): string {
    return `def exist ${this.name}(${this.vars})`;
  }
}

export class KnowNode extends L_Node {
  isKnowEverything: boolean = false;

  constructor(public facts: ToCheckNode[] = [], public strict: boolean) {
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
    public toProve: LogicNode | null,
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
  constructor(public facts: ToCheckNode[], public block: L_Node[]) {
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

// export class ReturnExistNode extends L_Node {
//   constructor(public factNames: string[]) {
//     super();
//   }
// }

export class ByNode extends L_Node {
  constructor(
    public byName: string,
    public vars: string[],
    public onlyIfs: ToCheckNode[]
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
