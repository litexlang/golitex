import { L_Builtins } from "./L_Builtins.ts";
import { L_Env } from "./L_Env.ts";
import { DefNameDecl, MemorizedExistDecl } from "./L_Memory.ts";

export abstract class L_Node {}

export class ToCheckNode extends L_Node {
  constructor(public isT: boolean, public defName: string | undefined) {
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
    return new ToCheckNode(true, undefined);
  }

  copyWithoutIsT(newIsT: boolean): ToCheckNode {
    return new ToCheckNode(newIsT, undefined);
  }

  getSubFactsWithDefName(): DefNameDecl[] {
    if (this.defName === undefined) {
      return [];
    } else {
      return [new DefNameDecl(this.defName, [], [], this)];
    }
  }
}

export class OrNode extends ToCheckNode {
  constructor(
    public facts: ToCheckNode[],
    isT: boolean,
    defName: string | undefined
  ) {
    super(isT, defName);
  }

  override varsDeclared(env: L_Env, freeVars: string[]): boolean {
    return this.facts.every((e) => e.varsDeclared(env, freeVars));
  }

  override factsDeclared(env: L_Env): boolean {
    return this.facts.every((e) => e.factsDeclared(env));
  }

  override copyWithoutIsT(newIsT: boolean): ToCheckNode {
    return new OrNode(this.facts, newIsT, this.defName);
  }

  override toString(): string {
    return `ors{${this.facts.map((e) => e.toString()).join(", ")}}`;
  }

  override getSubFactsWithDefName(): DefNameDecl[] {
    return [];
  }
}

export class LogicNode extends ToCheckNode {
  constructor(
    public vars: string[] = [],
    public req: ToCheckNode[] = [],
    public onlyIfs: ToCheckNode[] = [],
    isT: boolean = true,
    defName: undefined | string = undefined, // public isIff: boolean = false
    public reqName: null | string = null
  ) {
    super(isT, defName);
  }

  override copyWithoutIsT(newIsT: boolean): LogicNode {
    return new LogicNode(
      this.vars,
      this.req,
      this.onlyIfs,
      newIsT,
      this.defName,
      this.reqName
      // this.isIff
    );
  }

  override useMapToCopy(map: Map<string, string>): LogicNode {
    const newVars = [...this.vars];
    const req = this.req.map((e) => e.useMapToCopy(map));
    const onlyIfs = this.onlyIfs.map((e) => e.useMapToCopy(map));

    if (this instanceof LogicNode)
      return new LogicNode(
        newVars,
        req,
        onlyIfs,
        this.isT,
        this.defName,
        this.reqName
      );

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
    const notPart = !this.isT ? "[not] " : "";

    const defName = this.defName === undefined ? "" : `[${this.defName}]`;

    return notPart + mainPart + defName;
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

export class IffNode extends LogicNode {}
export class IfNode extends LogicNode {
  useByToDecl(): IfDefNode {
    return new DefNode(this.defName, this.vars, this.req, this.onlyIfs);
  }

  override getSubFactsWithDefName(): DefNameDecl[] {
    // get def from req
    let out: DefNameDecl[] = [];
    for (const fact of this.req) {
      const defNameDecls = fact.getSubFactsWithDefName();
      out = [...out, ...defNameDecls];
    }

    for (const r of this.onlyIfs) {
      const defNameDecls = r.getSubFactsWithDefName();
      addCurLayer(this, defNameDecls);
      out = [...out, ...defNameDecls];
    }

    if (this.defName !== undefined) {
      out = [...out, new DefNameDecl(this.defName, [], [], this)];
    }

    return out;

    function addCurLayer(ifThen: IfNode, defs: DefNameDecl[]): DefNameDecl[] {
      for (let i = 0; i < defs.length; i++) {
        defs[i].pushBeginNewReq(ifThen);
      }
      return defs;
    }
  }
}

// export class LogicNode extends LogicalOptNode {}
// export class OnlyIfNode extends LogicalOptNode {}

export class OptNode extends ToCheckNode {
  constructor(
    public name: string,
    public vars: string[],
    isT: boolean = true,
    defName: string | undefined = undefined
  ) {
    super(isT, defName);
  }

  override copyWithoutIsT(newIsT: boolean): OptNode {
    return new OptNode(this.name, this.vars, newIsT, this.defName);
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
    return new OptNode(this.name, newVars, this.isT, this.defName);
  }

  override toString() {
    const mainPart = this.name + `(${this.vars.join(", ")})`;
    const notPart = !this.isT ? "[not] " : "";
    const defName = this.defName === undefined ? "" : `[${this.defName}]`;
    return notPart + mainPart + defName;
  }

  override varsDeclared(env: L_Env, freeVars: string[]): boolean {
    const builtin = L_Builtins.get(this.name);
    if (builtin) {
      // ! Not A Good Implementation.
      return true;
    }

    for (const v of this.vars) {
      const declared = env.varDeclared(v) || freeVars.includes(v);
      if (!declared) {
        env.newMessage(`${v} not declared in ${this.name}`);
        return false;
      }
    }
    return true;
  }

  override factsDeclared(env: L_Env): boolean {
    if (env.optDeclared(this.name) || L_Builtins.get(this.name)) {
      return true;
    } else {
      env.newMessage(`${this.name} not declared.`);
      return false;
    }
  }

  override getSubFactsWithDefName(): DefNameDecl[] {
    if (this.defName === undefined) return [];
    else return [new DefNameDecl(this.defName, [], [], this)];
  }
}

export class ExistNode extends ToCheckNode {
  constructor(
    public vars: string[],
    public facts: ToCheckNode[],
    isT: boolean = true,
    defName: string | undefined = undefined
  ) {
    super(isT, defName);
  }

  //! MAYBE NOT GOOD
  override factsDeclared(env: L_Env): boolean {
    env;
    return true;
    // if (this.defName !== undefined) {
    //   defExist(
    //     env,
    //     new ExistDefNode(this.defName, [], [], this.vars, this.facts)
    //   );
    //   return true;
    // } else {
    //   return false;
    // }
  }
}

export class DefNode extends L_Node {
  constructor(
    public name: string = "",
    public vars: string[] = [],
    public req: ToCheckNode[] = [],
    public onlyIfs: ToCheckNode[] = [] // public defName: string | undefined = undefined
  ) {
    super();
  }

  override toString(): string {
    return "";
  }
}

export class IffDefNode extends DefNode {
  override toString(): string {
    return `def iff ${this.name}(${this.vars})`;
  }
}
export class IfDefNode extends DefNode {
  override toString(): string {
    return `def if ${this.name}(${this.vars})`;
  }
}
export class OnlyIfDefNode extends DefNode {
  override toString(): string {
    return `def only_if ${this.name}(${this.vars})`;
  }
}
export class ExistDefNode extends DefNode {
  constructor(
    name: string = "",
    vars: string[] = [],
    req: ToCheckNode[] = [],
    private existVars: string[] = [],
    private existFacts: ToCheckNode[] = []
  ) {
    super(name, vars, req, []); // We don't use onlyIfs field in ExistDecl.
  }

  toMemorized(): MemorizedExistDecl {
    return new MemorizedExistDecl(this.vars, this.existVars, this.existFacts);
  }

  override toString(): string {
    return `def exist ${this.name}(${this.vars})`;
  }

  getIfNode(): IfNode {
    const itself = [new OptNode(this.name, this.vars, true, undefined)];
    return new IfNode(this.vars, this.req, itself, true, undefined, null);
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

export class HaveNode extends L_Node {
  constructor(public opt: OptNode, public vars: string[]) {
    super();
  }

  override toString() {
    const varsStr = this.vars.join(", ");
    return `have ${this.opt.toString()} ${varsStr}`;
  }
}

export class SpecialNode extends L_Node {
  constructor(public keyword: string, public extra: unknown) {
    super();
  }
}

export class CallNode extends L_Node {
  constructor(
    public reqSpaceName: string,
    public vars: string[],
    public block: L_Node[]
  ) {
    super();
  }

  override toString() {
    return `${this.reqSpaceName}(${this.vars})`;
  }
}
