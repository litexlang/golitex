import { L_BuiltinsKeywords } from "./L_Builtins";
import { L_Env } from "./L_Env";
import { compositeSymbolParse } from "./L_Parser";

export abstract class L_Node {}

export class ToCheckNode extends L_Node {
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

  // MAIN FUNCTION OF THE WHOLE PROJECT
  useMapToCopy(env: L_Env, map: Map<string, string>): ToCheckNode {
    map;
    return new ToCheckNode(true);
  }

  copyWithoutIsT(newIsT: boolean): ToCheckNode {
    return new ToCheckNode(newIsT);
  }

  containOptAsIfThenReqOnlyIf(opt: OptNode): boolean {
    opt;
    return true;
  }
}

export class OrNode extends ToCheckNode {
  constructor(public facts: ToCheckNode[], isT: boolean) {
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
    public onlyIfs: ToCheckNode[] = [],
    isT: boolean = true
  ) {
    super(isT);
  }

  examineVarsNotDoubleDecl(varsFromAboveIf: string[]): boolean {
    const ok = this.vars.every((e) => !varsFromAboveIf.includes(e));
    if (!ok) return false;
    varsFromAboveIf = [...varsFromAboveIf, ...this.vars];
    return this.onlyIfs.every(
      (e) =>
        !(e instanceof LogicNode) || e.examineVarsNotDoubleDecl(varsFromAboveIf)
    );
  }

  override containOptAsIfThenReqOnlyIf(opt: OptNode): boolean {
    return this.onlyIfs.some((e) => e.containOptAsIfThenReqOnlyIf(opt));
  }

  override copyWithoutIsT(newIsT: boolean): LogicNode {
    return new LogicNode(
      this.vars,
      this.req,
      this.onlyIfs,
      newIsT
      // this.defName,
      // this.reqName,
      // this.isIff
    );
  }

  override useMapToCopy(env: L_Env, map: Map<string, string>): LogicNode {
    const newVars = [...this.vars];
    const req = this.req.map((e) => e.useMapToCopy(env, map));
    const onlyIfs = this.onlyIfs.map((e) => e.useMapToCopy(env, map));

    if (this instanceof LogicNode) {
      return new LogicNode(
        newVars,
        req,
        onlyIfs,
        this.isT
        // this.defName,
        // this.reqName,
      );
    }

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

    // const defName = this.defName === undefined ? "" : `[${this.defName}]`;

    return notPart + mainPart;
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
export class IfNode extends LogicNode {}

export class OptNode extends ToCheckNode {
  constructor(
    public name: string,
    public vars: string[],
    isT: boolean = true,
    public checkVars: string[][] | undefined = undefined
  ) {
    super(isT);
  }

  override containOptAsIfThenReqOnlyIf(opt: OptNode): boolean {
    return (
      opt.name === this.name && opt.vars.every((e, i) => e === this.vars[i])
    );
  }

  override copyWithoutIsT(newIsT: boolean): OptNode {
    return new OptNode(
      this.name,
      this.vars,
      newIsT,
      // this.defName,
      this.checkVars
    );
  }

  override useMapToCopy(env: L_Env, map: Map<string, string>): OptNode {
    const newVars: string[] = [];
    for (const v of this.vars) {
      const fixed = map.get(v);
      if (fixed === undefined) {
        //! I DON'T KNOW WHETHER I SHOULD THROW ERROR OR PUSH PREVIOUS SYMBOL
        // throw Error();
        newVars.push(v);

        // if (!fixed.startsWith("\\")) {
        // } else {
        //   const regex = new RegExp(`\\s${v}\\s`);
        //   if regex.test(v);
        // }
      } else {
        newVars.push(fixed);
      }
    }
    return new OptNode(
      this.name,
      newVars,
      this.isT,
      // this.defName,
      this.checkVars
    );
  }

  override toString() {
    const mainPart = this.name + `(${this.vars.join(", ")})`;
    const notPart = !this.isT ? "[not] " : "";
    return notPart + mainPart;
  }

  override varsDeclared(env: L_Env, freeVars: string[]): boolean {
    const isBuiltin = L_BuiltinsKeywords.includes(this.name);
    if (isBuiltin) {
      // ! Not A Good Implementation.
      return true;
    }

    for (const v of this.vars) {
      const declared =
        env.varDeclared(v) || freeVars.includes(v) || v.startsWith("\\");
      if (!declared) {
        env.newMessage(
          `variable ${v} not declared in called operator ${this.name}`
        );
        return false;
      }
    }
    return true;
  }

  override factsDeclared(env: L_Env): boolean {
    if (env.optDeclared(this.name) || L_BuiltinsKeywords.includes(this.name)) {
      return true;
    } else {
      env.newMessage(`operator ${this.name} not declared.`);
      return false;
    }
  }
}

export class DefNode extends L_Node {
  constructor(
    public name: string = "",
    public vars: string[] = [],
    public cond: ToCheckNode[] = [],
    public onlyIfs: ToCheckNode[] = [] // public defName: string | undefined = undefined // public cond: ToCheckNode[] = [],
  ) {
    super();
  }

  override toString(): string {
    return "";
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
