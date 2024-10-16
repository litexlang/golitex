import { isNull } from "lodash";
import { L_Keywords, OptsConnectionSymbol } from "./common";
import { L_Env } from "./env";
import { hInfo, RType } from "./executor";
import { cEnvRType, fixOpt, relTNotFoundEnvErr } from "./shared";

export abstract class L_Node {}

export abstract class FactNode extends L_Node {
  isT: Boolean = true;
}

export class OrNode extends FactNode {
  facts: FactNode[];
  constructor(facts: FactNode[]) {
    super();
    this.facts = facts;
  }
}

export class ShortCallOptNode extends FactNode {
  fullName: string;
  params: string[][];

  constructor(fullName: string, params: string[][]) {
    super();
    this.fullName = fullName;
    this.params = params;
  }
}

export class IfThenNode extends FactNode {
  req: FactNode[];
  onlyIfs: FactNode[];

  constructor(req: FactNode[], onlyIfs: FactNode[]) {
    super();
    this.req = req;
    this.onlyIfs = onlyIfs;
  }
}

export class CallOptNode extends FactNode {
  optName: string;
  optParams: string[][];
  optNameAsLst: string[];

  //! req and onlyIfs are used in some completely unrelated situations
  //! this is highly related to how # works: 1. when prove : introduce local var, bind req 2. when being checked: literally true?
  //! 1. used in prove/TNode/by/... req (emit or check)
  //! 2. used as opening a local env and check whether onlyIf works under req. If true, emit.
  //! 3. know (emit)
  req: CallOptNode[] = [];
  onlyIFs: CallOptNode[] = [];

  constructor(
    opts: [string, string[]][],
    req: CallOptNode[][] = [],
    onlyIfs: CallOptNode[] = []
  ) {
    super();

    this.optName = opts.map((e) => e[0]).join(OptsConnectionSymbol);
    this.optParams = opts.map((e) => e[1]);
    this.optNameAsLst = opts.map((e) => e[0]);
    this.req = req.flat();
    this.onlyIFs = onlyIfs;
  }

  static create(
    name: string,
    params: string[][],
    req: CallOptNode[][] = [],
    onlyIfs: CallOptNode[] = []
  ) {
    const names = name.split(OptsConnectionSymbol);
    return new CallOptNode(
      names.map((e, i) => [e, params[i]]),
      req,
      onlyIfs
    );
  }

  toString() {
    let s = this.optNameAsLst
      .map((v, i) => `${v}(${this.optParams[i].join(", ")})`)
      .join(":");
    if (this.onlyIFs.length > 0)
      s += " => {" + this.onlyIFs.map((v, i) => v.toString()).join(", ") + "}";
    return s;
  }
}

// Main data structure of the whole project
export abstract class TNode extends L_Node {
  name: string;
  freeVars: string[];
  requirements: CallOptNode[] = [];
  onlyIfs: L_Node[] = []; // After declaration, this becomes CallOpt[]
  declaredTemplates = new Map<string, TNode>();
  private fathers: TNode[] = [];
  isRedefine: Boolean = false;

  constructor(
    name: string,
    freeVars: string[],
    requirements: CallOptNode[],
    onlyIfs: L_Node[] = []
  ) {
    super();
    this.name = name;
    this.freeVars = freeVars;
    this.requirements = requirements;
    this.onlyIfs = onlyIfs;
  }
  // Input a full name with colons and get descendants from any depth
  getDeclaredSubTemplate(s: string): undefined | TNode {
    const names: string[] = s.split(":");
    let curTemplate: TNode | undefined = this;
    for (let i = 1; i < names.length; i++) {
      curTemplate = curTemplate?.declaredTemplates.get(names[i]);
      if (!curTemplate) {
        return undefined;
      }
    }
    return curTemplate;
  }

  allReq(): CallOptNode[] {
    const out: CallOptNode[] = [];
    this.fathers.forEach((e) => e.requirements.forEach((req) => out.push(req)));
    this.requirements.forEach((e) => out.push(e));
    return out;
  }

  allVars() {
    const out: string[][] = [];
    for (const father of this.fathers) {
      out.push(father.freeVars);
    }
    out.push(this.freeVars);
    return out;
  }

  allNames() {
    const out: string[] = [];
    for (const father of this.fathers) {
      out.push(father.name);
    }
    out.push(this.name);
    return out;
  }

  // If a node is DollarMarkNode or TNode, i.e. it is the son template of this, then it is pushed into this.declaredTemplates and it is removed from this.onlyIfs. If there is non-def, non-call node in block, report error
  //! REFACTOR THIS SO THAT DEF IN REQ CAN APPEAR HERE.
  initDeclaredTemplates(env: L_Env, fathers: TNode[] = []): RType {
    this.fathers = fathers;

    // process DollarMarks
    for (let i = this.onlyIfs.length - 1; i >= 0; i--) {
      const value = this.onlyIfs[i];
    }

    // eliminate template declarations in onlyIfs, retain callOpts
    for (let i = this.onlyIfs.length - 1; i >= 0; i--) {
      const value = this.onlyIfs[i];
      if (value instanceof TNode) {
        if (L_Keywords.includes(value.name))
          return cEnvRType(env, RType.Error, ``);
        value.initDeclaredTemplates(env, [...fathers, this]);
        this.declaredTemplates.set(value.name, value);
        this.onlyIfs.splice(i, 1);
      }
    }

    // make sure everything is done well.
    for (let i = 0; i < this.onlyIfs.length; i++) {
      if (!(this.onlyIfs[i] instanceof CallOptNode)) {
        return cEnvRType(
          env,
          RType.Error,
          `arguments of def block should have type callOpt-type or def-type.`
        );
      }
    }
    return RType.True;
  }

  // Fix all free variables in this template, no matter it's declared in fathers or itself
  // callOptParams: the fullOpt that calls this template
  fix(
    callOptParams: CallOptNode | string[][]
  ): Map<string, string> | undefined {
    if (callOptParams instanceof CallOptNode) {
      callOptParams = callOptParams.optParams;
    }
    callOptParams = callOptParams as string[][];

    const freeFixMap = new Map<string, string>();

    const relTs = [...this.fathers, this];

    if (
      !areArraysEqual(
        callOptParams,
        relTs.map((e) => e.freeVars)
      )
    ) {
      return undefined;
    }

    for (let [i, template] of relTs.entries()) {
      template.freeVars.forEach((v, j: number) =>
        freeFixMap.set(v, callOptParams[i][j])
      );
    }

    return freeFixMap;

    function areArraysEqual(arr1: string[][], arr2: string[][]): boolean {
      if (arr1.length !== arr2.length) {
        return false;
      }

      for (let i = 0; i < arr1.length; i++) {
        if (arr1[i].length !== arr2[i].length) {
          return false;
        }
      }

      return true;
    }
  }

  toString(): string {
    const typeName =
      this instanceof DefNode
        ? "def"
        : this instanceof InferNode
          ? "infer"
          : this instanceof ExistNode
            ? "exist"
            : "";

    const names = this.allNames();
    const vars = this.allVars();

    let result = `${typeName} ${names.map((v, i) => `${v}(${vars[i].toString()})`).join(":")}`;

    const reqStr = this.allReq()
      .map((e) => e.toString())
      .join(", ");
    if (reqStr) {
      result += ` req: ${reqStr}`;
    }

    const onlyIfsStr = this.onlyIfs
      .map((e) => (e as CallOptNode).toString())
      .join(", ");
    if (onlyIfsStr) {
      result += ` onlyIfs: ${onlyIfsStr}`;
    }

    return result;
  }

  abstract checkReq(env: L_Env, node: CallOptNode, emit: Boolean): RType;
  abstract emitTOnlyIf(env: L_Env, node: CallOptNode): RType;
}

export class DefNode extends TNode {
  checkReq(env: L_Env, node: CallOptNode, emit: Boolean = false): RType {
    const tmp = fixOpt(env, node, this.allVars(), this.allReq());
    if (isNull(tmp.v)) return relTNotFoundEnvErr(env, node);
    else {
      if (tmp.v.every((opt) => env.checkEmit(opt).v)) {
        env.newFactEmit(node, emit);
        return RType.True;
      }
      return RType.Unknown;
    }
  }

  emitTOnlyIf(env: L_Env, node: CallOptNode): RType {
    const tmp = fixOpt(env, node, this.allVars(), this.allReq());
    if (isNull(tmp.v)) return relTNotFoundEnvErr(env, node);
    tmp.v.forEach((e) => env.newFactEmit(e, true));
    return RType.True;
  }
}

export class InferNode extends TNode {
  checkReq(env: L_Env, node: CallOptNode, emit: Boolean = false): RType {
    const fixedReq = fixOpt(env, node, this.allVars(), this.allReq());
    const isT = fixedReq.v?.every((e) => env.checkEmit(e, emit));
    if (isT === undefined) return relTNotFoundEnvErr(env, node);
    else return RType.True;
  }

  emitTOnlyIf(env: L_Env, node: CallOptNode): RType {
    const fixedReq = fixOpt(
      env,
      node,
      this.allVars(),
      this.onlyIfs as CallOptNode[]
    );
    fixedReq.v?.forEach((e) => env.newFactEmit(e, true));
    return RType.True;
  }
}

export class ExistNode extends TNode {
  isTrue = false;
  checkReq(env: L_Env, node: CallOptNode, emit: Boolean = false): RType {
    return RType.Error;
  }

  emitTOnlyIf(env: L_Env, node: CallOptNode): RType {
    return RType.Error;
  }
}

export class KnowNode extends L_Node {
  facts: FactNode[] = [];
  isKnowEverything: Boolean = false;

  constructor(facts: CallOptNode[] = []) {
    super();
    this.facts = facts;
  }

  toString(): string {
    return this.facts.map((e) => (e as CallOptNode).toString()).join("; ");
  }
}

export class LetNode extends L_Node {
  vars: string[];
  properties: FactNode[];

  constructor(node: { freeVars: string[]; properties: FactNode[] }) {
    super();
    this.vars = node.freeVars;
    this.properties = node.properties;
  }

  toString() {
    return `${this.vars.join(", ")}| ${this.properties.map((s) => s.toString()).join(", ")}`;
  }
}

export class ProveNode extends L_Node {
  opt: CallOptNode;
  proveBlock: L_Node[];
  name: string;

  constructor(opt: CallOptNode, proveBlock: L_Node[], name: string = "") {
    super();
    this.opt = opt;
    this.proveBlock = proveBlock;
    this.name = name;
  }
}

export class HaveNode extends L_Node {
  vars: string[];
  opt: CallOptNode;
  constructor(vars: string[], opt: CallOptNode) {
    super();
    this.vars = vars;
    this.opt = opt;
  }
}

export class ByNode extends L_Node {
  name: string;
  opt: CallOptNode;

  constructor(name: string, opt: CallOptNode) {
    super();
    this.name = name;
    this.opt = opt;
  }
}

export class ThmNode extends L_Node {
  opt: CallOptNode;
  proveBlock: L_Node[];

  constructor(opt: CallOptNode, proveBlock: L_Node[]) {
    super();
    this.opt = opt;
    this.proveBlock = proveBlock;
  }
}
