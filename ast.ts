import { isNull } from "lodash";
import { L_Keywords, OptsConnectionSymbol } from "./common";
import { L_Env } from "./env";
import { hInfo, RType } from "./executor";
import {
  cEnvRType,
  cL_Out,
  ErrL_Out,
  fixOpt,
  L_Out,
  relTNotFoundEnvErr,
  RL_Out,
} from "./shared";

//? There are several things in LiTex: Declaration (var, fact-template) ; check; know(let); emit
// export enum L_NodeType {
//   Error,
//   Node,

//   FactNode,
//   // CallOptsNode,

//   KnowNode,
//   HaveNode,
//   LetNode,

//   ProofNode,
//   CheckInProof,
//   ImpliesFactNode,

//   InferNode,
//   DefNode,
//   ExistNode,

//   FreeVarsWithFactsNode,
//   DollarMarkNode,
//   ByNode,
//   ThmNode,
// }

export abstract class L_Node {
  // type: L_NodeType = L_NodeType.Node;
}

export class FactNode extends L_Node {
  // type: L_NodeType = L_NodeType.FactNode;
  optName: string;
  optParams: string[][];
  optNameAsLst: string[];

  byName: string = "";

  //! req and onlyIfs are used in some completely unrelated situations
  //! this is highly related to how # works: 1. when prove : introduce local var, bind req 2. when being checked: literally true?
  //! 1. used in prove/TNode/by/... req (emit or check)
  //! 2. used as opening a local env and check whether onlyIf works under req. If true, emit.
  //! 3. know (emit)
  req: FactNode[] = [];
  onlyIFs: FactNode[] = [];

  constructor(
    opts: [string, string[]][],
    req: FactNode[][] = [],
    onlyIfs: FactNode[] = [],
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
    req: FactNode[][] = [],
    onlyIfs: FactNode[] = [],
    byName: string = ""
  ) {
    const names = name.split(OptsConnectionSymbol);
    return new FactNode(
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
  onlyIfs: FactNode[];
  requirements: FactNode[];
  activated: Boolean;
};
export function makeTemplateNodeFact(
  params: string[][],
  onlyIfs: FactNode[] = [],
  requirements: FactNode[] = [],
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
  // type: L_NodeType = L_NodeType.InferNode;
  name: string;
  freeVars: string[];
  requirements: FactNode[] = [];
  onlyIfs: L_Node[] = []; // After declaration, this becomes CallOpt[]
  declaredTemplates = new Map<string, TNode>();
  private fathers: TNode[] = [];
  isRedefine: Boolean = false;

  constructor(
    name: string,
    freeVars: string[],
    requirements: FactNode[],
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

  allReq(): FactNode[] {
    const out: FactNode[] = [];
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

      if (value instanceof DollarMarkNode) {
        this.onlyIfs.splice(i, 1);

        const callNode = new FactNode([
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
          return cEnvRType(env, RType.Error, ``);
        value.initDeclaredTemplates(env, [...fathers, this]);
        this.declaredTemplates.set(value.name, value);
        this.onlyIfs.splice(i, 1);
      }
      // else if (value instanceof FactNode) {
      // this.onlyIfs.push(value);
      // this.onlyIfs = insertListIntoListAndDeleteElemOnIndex(
      //   this.onlyIfs,
      //   (value as CallOptsNode).nodes,
      //   i
      // );
      // }
      // else if (value instanceof CallOptsNode) {
      //   this.onlyIfs = insertListIntoListAndDeleteElemOnIndex(
      //     this.onlyIfs,
      //     (value as CallOptsNode).nodes,
      //     i
      //   );
      // }
    }

    // make sure everything is done well.
    for (let i = 0; i < this.onlyIfs.length; i++) {
      if (!(this.onlyIfs[i] instanceof FactNode)) {
        return cEnvRType(
          env,
          RType.Error,
          `arguments of def block should have type callOpt-type or def-type.`
        );
      }
    }
    return RType.True;

    // function insertListIntoListAndDeleteElemOnIndex<T>(
    //   originalList: T[],
    //   itemsToInsert: T,
    //   position: number
    // ): T[] {
    //   const newList = [...originalList];
    //   newList.splice(position, 1, itemsToInsert);
    //   return newList;
    // }
  }

  // Fix all free variables in this template, no matter it's declared in fathers or itself
  // callOptParams: the fullOpt that calls this template
  fix(callOptParams: FactNode | string[][]): Map<string, string> | undefined {
    if (callOptParams instanceof FactNode) {
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
      .map((e) => (e as FactNode).toString())
      .join(", ");
    if (onlyIfsStr) {
      result += ` onlyIfs: ${onlyIfsStr}`;
    }

    return result;
  }

  abstract checkReq(env: L_Env, node: FactNode, emit: Boolean): RType;
  abstract emitTOnlyIf(env: L_Env, node: FactNode): RType;
}

export class DefNode extends TNode {
  // type: L_NodeType = L_NodeType.DefNode;

  checkReq(env: L_Env, node: FactNode, emit: Boolean = false): RType {
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

  emitTOnlyIf(env: L_Env, node: FactNode): RType {
    const tmp = fixOpt(env, node, this.allVars(), this.allReq());
    if (isNull(tmp.v)) return relTNotFoundEnvErr(env, node);
    tmp.v.forEach((e) => env.newFactEmit(e, true));
    return RType.True;
  }
}

export class InferNode extends TNode {
  // type: L_NodeType = L_NodeType.InferNode;

  checkReq(env: L_Env, node: FactNode, emit: Boolean = false): RType {
    const fixedReq = fixOpt(env, node, this.allVars(), this.allReq());
    const isT = fixedReq.v?.every((e) => env.checkEmit(e, emit));
    if (isT === undefined) return relTNotFoundEnvErr(env, node);
    else return RType.True;
  }

  emitTOnlyIf(env: L_Env, node: FactNode): RType {
    const fixedReq = fixOpt(
      env,
      node,
      this.allVars(),
      this.onlyIfs as FactNode[]
    );
    fixedReq.v?.forEach((e) => env.newFactEmit(e, true));
    return RType.True;
  }
}

export class ExistNode extends TNode {
  // type = L_NodeType.ExistNode;
  isTrue = false;
  checkReq(env: L_Env, node: FactNode, emit: Boolean = false): RType {
    return RType.Error;
  }

  emitTOnlyIf(env: L_Env, node: FactNode): RType {
    return RType.Error;
  }
}

export type CanBeKnownNode = FactNode | TNode;
export class KnowNode extends L_Node {
  // type: L_NodeType = L_NodeType.KnowNode;
  facts: CanBeKnownNode[] = [];
  isKnowEverything: Boolean = false;

  constructor(facts: FactNode[] = []) {
    super();
    this.facts = facts;
  }

  toString(): string {
    return this.facts.map((e) => (e as FactNode).toString()).join("; ");
  }
}

// export enum CallOptsNodeType {
//   And,
//   Or,
//   Not,
// }
// export class CallOptsNode extends L_Node {
// type: L_NodeType = L_NodeType.CallOptsNode;
//   nodes: (FactNode | CallOptsNode)[] = [];
//   factType: CallOptsNodeType = CallOptsNodeType.And;

//   constructor(nodes: FactNode[]) {
//     super();
//     this.nodes = nodes;
//   }
// }

export class LetNode extends L_Node {
  // type: L_NodeType = L_NodeType.LetNode;
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

// Declare and call at the same time.
export class DollarMarkNode extends L_Node {
  // type = L_NodeType.DollarMarkNode;
  template: TNode;

  constructor(template: TNode) {
    super();
    this.template = template;
  }
}

export class ProveNode extends L_Node {
  // type = L_NodeType.ProofNode;
  opt: FactNode;
  proveBlock: L_Node[];
  name: string;

  constructor(opt: FactNode, proveBlock: L_Node[], name: string = "") {
    super();
    this.opt = opt;
    this.proveBlock = proveBlock;
    this.name = name;
  }
}

export class HaveNode extends L_Node {
  // type = L_NodeType.HaveNode;
  vars: string[];
  opt: FactNode;
  constructor(vars: string[], opt: FactNode) {
    super();
    this.vars = vars;
    this.opt = opt;
  }
}

export class ByNode extends L_Node {
  // type = L_NodeType.ByNode;
  name: string;
  opt: FactNode;

  constructor(name: string, opt: FactNode) {
    super();
    this.name = name;
    this.opt = opt;
  }
}

export class ThmNode extends L_Node {
  // type = L_NodeType.ThmNode;
  opt: FactNode;
  proveBlock: L_Node[];

  constructor(opt: FactNode, proveBlock: L_Node[]) {
    super();
    this.opt = opt;
    this.proveBlock = proveBlock;
  }
}
