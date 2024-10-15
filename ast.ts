import { isNull } from "lodash";
import { L_Keywords, OptsConnectionSymbol } from "./common";
import { L_Env } from "./env";
import { hInfo, RType } from "./executor";
import {
  cEnvErrL_Out,
  cL_Out,
  ErrL_Out,
  fixOpt,
  L_Out,
  RL_Out,
} from "./shared";
import exp from "constants";
import { on } from "events";

//? There are several things in LiTex: Declaration (var, fact-template) ; check; know(let); emit
export enum L_NodeType {
  Error,
  Node,

  CallOptNode,
  CallOptsNode,

  KnowNode,
  HaveNode,
  LetNode,

  ProofNode,
  CheckInProof,
  ImpliesFactNode,

  InferNode,
  DefNode,
  ExistNode,

  FreeVarsWithFactsNode,
  DollarMarkNode,
  ByNode,
  ThmNode,
}

export abstract class L_Node {
  type: L_NodeType = L_NodeType.Node;
}

export class CallOptNode extends L_Node {
  type: L_NodeType = L_NodeType.CallOptNode;
  optName: string;
  optParams: string[][];
  optNameAsLst: string[];

  /**Extra features: used in know, prove*/
  req: CallOptNode[] = [];
  onlyIFs: CallOptNode[] = [];
  byName: string = "";

  constructor(
    opts: [string, string[]][],
    req: CallOptNode[][] = [],
    onlyIfs: CallOptNode[] = [],
    byName: string = ""
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
    onlyIfs: CallOptNode[] = [],
    byName: string = ""
  ) {
    const names = name.split(OptsConnectionSymbol);
    return new CallOptNode(
      names.map((e, i) => [e, params[i]]),
      req,
      onlyIfs,
      byName
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

export type TNodeFact = {
  params: string[][];
  onlyIfs: CallOptNode[];
  requirements: CallOptNode[];
  activated: Boolean;
};
export function makeTemplateNodeFact(
  params: string[][],
  onlyIfs: CallOptNode[] = [],
  requirements: CallOptNode[] = [],
  activated: Boolean = true
) {
  return {
    params: params,
    onlyIfs: onlyIfs,
    activated: activated,
    requirements: requirements,
  };
}

// Main data structure of the whole project
export abstract class TNode extends L_Node {
  type: L_NodeType = L_NodeType.InferNode;
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
  initDeclaredTemplates(env: L_Env, fathers: TNode[] = []): RL_Out {
    this.fathers = fathers;

    // process DollarMarks
    for (let i = this.onlyIfs.length - 1; i >= 0; i--) {
      const value = this.onlyIfs[i];

      if (value instanceof DollarMarkNode) {
        this.onlyIfs.splice(i, 1);

        const callNode = new CallOptNode([
          [value.template.name, value.template.freeVars],
        ]);
        const templateNode: TNode = value.template;

        //! Here lies a problem: the templateNode's optName should start with : and anything start with : means it inherits from all above.
        this.onlyIfs.splice(i, 0, templateNode, callNode);
      }
    }

    // eliminate template declarations in onlyIfs, retain callOpts
    for (let i = this.onlyIfs.length - 1; i >= 0; i--) {
      const value = this.onlyIfs[i];
      if (value instanceof TNode) {
        if (L_Keywords.includes(value.name))
          return cEnvErrL_Out(
            env,
            RType.DefError,
            `Template '${value.name}' is L_ keyword.`
          );
        value.initDeclaredTemplates(env, [...fathers, this]);
        this.declaredTemplates.set(value.name, value);
        this.onlyIfs.splice(i, 1);
      } else if (value instanceof CallOptsNode) {
        this.onlyIfs = insertListIntoListAndDeleteElemOnIndex(
          this.onlyIfs,
          (value as CallOptsNode).nodes,
          i
        );
      }
    }

    // make sure everything is done well.
    for (let i = 0; i < this.onlyIfs.length; i++) {
      if (this.onlyIfs[i].type !== L_NodeType.CallOptNode) {
        return cEnvErrL_Out(
          env,
          RType.DefError,
          `arguments of def block should have type callOpt-type or def-type.`
        );
      }
    }
    return cL_Out(RType.DefTrue);

    function insertListIntoListAndDeleteElemOnIndex<T>(
      originalList: T[],
      itemsToInsert: T[],
      position: number
    ): T[] {
      const newList = [...originalList];
      newList.splice(position, 1, ...itemsToInsert);
      return newList;
    }
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
          : "exist";

    const names = this.allNames();
    const vars = this.allVars();
    return `${typeName} ${names.map((v, i) => `${v}(${vars[i].toString()})`).join(":")}
req: ${this.allReq()
      .map((e) => e.toString())
      .join(", ")}
onlyIfs: ${this.onlyIfs.map((e) => (e as CallOptNode).toString()).join(", ")}`;
  }

  abstract checkReq(env: L_Env, node: CallOptNode, emit: Boolean): RL_Out;
}

export class DefNode extends TNode {
  type: L_NodeType = L_NodeType.DefNode;

  checkReq(env: L_Env, node: CallOptNode, emit: Boolean = false): RL_Out {
    const tmp = fixOpt(env, node, this.allVars(), this.allReq());
    if (isNull(tmp.v)) return cL_Out(null);
    else {
      if (tmp.v.every((opt) => env.checkEmit(opt).v)) {
        env.newFactEmit(node, emit);
        return cL_Out(RType.True, "check by requirements");
      }
      return cL_Out(RType.Unknown);
    }
  }

  emitTOnlyIf(env: L_Env, node: CallOptNode): RL_Out {
    const tmp = fixOpt(env, node, this.allVars(), this.allReq());
    if (isNull(tmp.v)) return cL_Out(null);
    tmp.v.forEach((e) => env.newFactEmit(e, true));
    return cL_Out(RType.True, "check by itself");
  }
}

export class InferNode extends TNode {
  type: L_NodeType = L_NodeType.InferNode;

  checkReq(env: L_Env, node: CallOptNode, emit: Boolean = false): RL_Out {
    const fixedReq = fixOpt(env, node, this.allVars(), this.allReq());
    const isT = fixedReq.v?.every((e) => env.checkEmit(e, emit));
    if (isT === undefined) return ErrL_Out;
    else return cL_Out(RType.True);
  }

  emitTOnlyIf(env: L_Env, node: CallOptNode): RL_Out {
    const fixedReq = fixOpt(
      env,
      node,
      this.allVars(),
      this.onlyIfs as CallOptNode[]
    );
    fixedReq.v?.forEach((e) => env.newFactEmit(e, true));
    return cL_Out(RType.InferTrue);
  }
}

export class ExistNode extends TNode {
  type = L_NodeType.ExistNode;
  isTrue = false;
  checkReq(env: L_Env, node: CallOptNode, emit: Boolean = false): RL_Out {
    return ErrL_Out;
  }

  emitTOnlyIf(env: L_Env, node: CallOptNode): RL_Out {
    return ErrL_Out;
  }
}

export type CanBeKnownNode = FactNode | TNode;
export class KnowNode extends L_Node {
  type: L_NodeType = L_NodeType.KnowNode;
  facts: CanBeKnownNode[] = [];
  isKnowEverything: Boolean = false;

  constructor(facts: CallOptNode[] = []) {
    super();
    this.facts = facts;
  }
}

export type FactNode = CallOptNode | CallOptsNode;
export enum CallOptsNodeType {
  And,
  Or,
  Not,
}
export class CallOptsNode extends L_Node {
  type: L_NodeType = L_NodeType.CallOptsNode;
  nodes: CallOptNode[] = [];
  factType: CallOptsNodeType = CallOptsNodeType.And;

  constructor(nodes: CallOptNode[]) {
    super();
    this.nodes = nodes;
  }
}

export class LetNode extends L_Node {
  type: L_NodeType = L_NodeType.LetNode;
  vars: string[];
  properties: CallOptNode[];

  constructor(node: { freeVars: string[]; properties: CallOptNode[] }) {
    super();
    this.vars = node.freeVars;
    this.properties = node.properties;
  }

  toString() {
    return `${this.vars.join(", ")}: ${this.properties.map((s) => s.toString()).join(", ")}`;
  }
}

// Declare and call at the same time.
export class DollarMarkNode extends L_Node {
  type = L_NodeType.DollarMarkNode;
  template: TNode;

  constructor(template: TNode) {
    super();
    this.template = template;
  }
}

export class ProveNode extends L_Node {
  type = L_NodeType.ProofNode;
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
  type = L_NodeType.HaveNode;
  vars: string[];
  opt: CallOptNode;
  constructor(vars: string[], opt: CallOptNode) {
    super();
    this.vars = vars;
    this.opt = opt;
  }
}

export class ByNode extends L_Node {
  type = L_NodeType.ByNode;
  name: string;
  opt: CallOptNode;

  constructor(name: string, opt: CallOptNode) {
    super();
    this.name = name;
    this.opt = opt;
  }
}

export class ThmNode extends L_Node {
  type = L_NodeType.ThmNode;
  opt: CallOptNode;
  proveBlock: L_Node[];

  constructor(opt: CallOptNode, proveBlock: L_Node[]) {
    super();
    this.opt = opt;
    this.proveBlock = proveBlock;
  }
}
