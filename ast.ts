import {
  areStrArrStructureEqual,
  freeVarsToFixedVars,
  relationBetweenStrArrArrays,
} from "./common";
import { LiTeXEnv } from "./env";
import { ResultType } from "./executor";

// There are 3 things in LiTex: Declaration (var, fact-formula) ; check; know
export enum LiTexNodeType {
  Error,
  Node,
  NotNode,
  OrNode,
  CallOptNode,
  CallOptsNode,
  KnowNode,
  ExistNode,
  IffNode,
  FactsNode,
  InferNode,
  HaveNode,
  ParamsColonFactExprsNode,
  PropertyNode,
  CheckNode,
  CallOptWithColonColonNode,
  OnlyIfNode,
  IfNode,
  InheritNode,
  LetNode,
  DefNode,
  ProofNode,
}

export class LiTeXNode {
  type: LiTexNodeType = LiTexNodeType.Node;
  constructor() {}
}
const NullNode = new LiTeXNode();

export class CallOptNode extends LiTeXNode {
  type: LiTexNodeType = LiTexNodeType.CallOptNode;
  optName: string = "";
  optParams: string[][] = [];

  constructor(opts: [string, string[]][]) {
    super();
    this.optName = opts.map((e) => e[0]).join("::");
    this.optParams = opts.map((e) => e[1]);
  }

  deepCopy() {
    return new CallOptNode(this.getOptNameParamsPairs());
  }

  getParaNames() {
    return this.optName.split("::");
  }

  getOptNameParamsPairs(): [string, string[]][] {
    const optNames = this.getParaNames();
    return optNames.map((v, i) => {
      return [this.optName, this.optParams[i]];
    });
  }

  paramsLst(): string[] {
    return this.optName.split("::");
  }

  pushNewNameParamsPair(pair: [string, string[]]) {
    if (this.optName !== "") this.optName += "::" + pair[0];
    else this.optName += pair[0];

    this.optParams.push(pair[1]);
  }
}

// when parsing FactExprNode, need to pass in isEnd
export type FactExprNode =
  | KnowNode
  | CallOptNode
  | OrNode
  | NotNode
  | IffNode
  | OnlyIfNode
  | IfNode
  | CallOptsNode;
export const FactExprNodeNames: string[] = [
  "know",
  "or",
  "not",
  "<=>",
  "<=",
  "=>",
];

export type CanBeKnownNode =
  | InferNode
  | ExistNode
  | IffNode
  | OnlyIfNode
  | IfNode
  | CallOptNode
  | OrNode
  | NotNode
  | CallOptsNode;
export const canBeKnownNodeNames: string[] = [
  "infer",
  "exist",
  "<=>",
  "not",
  "or",
  "<=",
  "=>",
];

export class FactsNode extends LiTeXNode {
  type: LiTexNodeType = LiTexNodeType.FactsNode;
  facts: FactExprNode[] = [];
  constructor(facts: FactExprNode[]) {
    super();
    this.facts = facts;
  }
}

export class InferNode extends LiTeXNode {
  type: LiTexNodeType = LiTexNodeType.InferNode;
  declOptName: string;
  params: string[][];
  requirements: LiTeXNode[] = [];
  onlyIfExprs: LiTeXNode[] = [];
  father: string = "";

  constructor(
    declOptName: string,
    params: string[][],
    requirements: LiTeXNode[]
  ) {
    super();
    this.declOptName = declOptName;
    this.params = params;
    this.requirements = requirements;
  }

  emitOnlyIfs(env: LiTeXEnv, freeToFixedMap: Map<string, string>) {
    for (const defSubNode of this.onlyIfExprs) {
      if (defSubNode.type === LiTexNodeType.CallOptsNode) {
        for (const freeCallOpt of (defSubNode as CallOptsNode).nodes) {
          env.newFact(getFixedNodeFromFreeFixMap(freeToFixedMap, freeCallOpt));
        }
      }
    }
  }

  checkRequirements(
    env: LiTeXEnv,
    freeToFixedMap: Map<string, string>
  ): ResultType {
    for (const req of this.requirements) {
      if (req.type === LiTexNodeType.CallOptsNode) {
        for (const freeOpt of (req as CallOptsNode).nodes) {
          const isFact: Boolean = env.isCallOptFact(
            // this.getFixedNodeFromFreeNode(fixedOpt.optParams, freeOpt)
            getFixedNodeFromFreeFixMap(freeToFixedMap, freeOpt)
          );
          if (!isFact) {
            return ResultType.Unknown;
          }
        }
      }
    }
    return ResultType.True;
  }
}

export class KnowNode extends LiTeXNode {
  type: LiTexNodeType = LiTexNodeType.KnowNode;
  facts: CanBeKnownNode[] = [];
}

export class HaveNode extends LiTeXNode {
  type: LiTexNodeType = LiTexNodeType.HaveNode;
  params: string[];
  properties: LiTeXNode[];

  constructor(node: ParamsColonFactExprsNode) {
    super();
    this.params = node.params;
    this.properties = node.properties;
  }
}

export class ParamsColonFactExprsNode extends LiTeXNode {
  type: LiTexNodeType = LiTexNodeType.ParamsColonFactExprsNode;
  params: string[];
  properties: CanBeKnownNode[];

  constructor(params: string[], properties: CanBeKnownNode[]) {
    super();
    this.params = params;
    this.properties = properties;
  }
}

export class CheckNode extends LiTeXNode {
  type: LiTexNodeType = LiTexNodeType.CheckNode;
  callOpts: CallOptNode[] = [];
  constructor(callOpts: CallOptNode[]) {
    super();
    this.callOpts = callOpts;
  }
}

export class IffNode extends LiTeXNode {
  type: LiTexNodeType = LiTexNodeType.IffNode;
  left: CallOptNode;
  right: CallOptNode;

  constructor(left: CallOptNode, right: CallOptNode) {
    super();
    this.left = left;
    this.right = right;
  }
}

export class OnlyIfNode extends LiTeXNode {
  type: LiTexNodeType = LiTexNodeType.OnlyIfNode;
  left: CallOptNode;
  right: CallOptsNode[]; // it's better to have CallOptsNode[] as type

  constructor(left: CallOptNode, right: CallOptsNode[]) {
    super();
    this.left = left;
    this.right = right;
  }
}

export class IfNode extends LiTeXNode {
  type: LiTexNodeType = LiTexNodeType.IfNode;
  left: CallOptsNode[]; // it's better to have CallOptsNode[] as type
  right: CallOptNode;

  constructor(left: CallOptsNode[], right: CallOptNode) {
    super();
    this.left = left;
    this.right = right;
  }
}

export class PropertyNode extends LiTeXNode {
  type: LiTexNodeType = LiTexNodeType.PropertyNode;
  optName: string;
  calledParams: string[];
  onlyIfExprs: LiTeXNode[] = [];

  constructor(optName: string, calledParams: string[]) {
    super();
    this.optName = optName;
    this.calledParams = calledParams;
  }
}

// Exist: means 2 things happen at the same time: var decl and know callOpt
export class ExistNode extends LiTeXNode {
  type: LiTexNodeType = LiTexNodeType.ExistNode;
  declOptName: string = "";
  params: string[] = [];
  requirements: LiTeXNode[] = [];

  constructor(
    declOptName: string,
    params: string[],
    requirements: LiTeXNode[]
  ) {
    super();
    this.declOptName = declOptName;
    this.params = params;
    this.requirements = requirements;
  }
}

export class NotNode extends LiTeXNode {
  type: LiTexNodeType = LiTexNodeType.NotNode;
  exprs: LiTeXNode[] = [];

  constructor(exprs: LiTeXNode[]) {
    super();
    this.exprs = exprs;
  }
}

export class OrNode extends LiTeXNode {
  type: LiTexNodeType = LiTexNodeType.OrNode;
  blocks: LiTeXNode[][] = [];
}

export class CallOptsNode extends LiTeXNode {
  type: LiTexNodeType = LiTexNodeType.CallOptsNode;
  nodes: CallOptNode[] = [];
  constructor(nodes: CallOptNode[]) {
    super();
    this.nodes = nodes;
  }
}

export class LetNode extends LiTeXNode {
  type: LiTexNodeType = LiTexNodeType.LetNode;
  params: string[];
  properties: CanBeKnownNode[];

  constructor(node: ParamsColonFactExprsNode) {
    super();
    this.params = node.params;
    this.properties = node.properties;
  }
}

export class DefNode extends LiTeXNode {
  type: LiTexNodeType = LiTexNodeType.DefNode;
  declOptName: string;
  params: string[][];
  requirements: LiTeXNode[] = [];
  onlyIfExprs: LiTeXNode[] = [];
  father: string = "";

  constructor(
    declOptName: string,
    params: string[][],
    requirements: LiTeXNode[]
  ) {
    super();
    this.declOptName = declOptName;
    this.params = params;
    this.requirements = requirements;
  }

  // replace free variables with fixed variables
  // getFixedNodeFromFreeNode(
  //   newOptParams: string[][],
  //   freeCallOpt: CallOptNode
  // ): CallOptNode {
  //   try {
  //     const node = new CallOptNode([]);
  //     node.optName = freeCallOpt.optName;
  //     if (!areStrArrStructureEqual(this.params, newOptParams)) {
  //       throw Error("Invalid number of given arguments.");
  //     }
  //     const relation: Map<string, string> = relationBetweenStrArrArrays(
  //       this.params,
  //       newOptParams
  //     );
  //     node.optParams = freeVarsToFixedVars(freeCallOpt.optParams, relation);
  //     return node;
  //   } catch (error) {
  //     throw error;
  //   }
  // }

  emitOnlyIfs(env: LiTeXEnv, freeToFixedMap: Map<string, string>) {
    for (const defSubNode of this.requirements) {
      if (defSubNode.type === LiTexNodeType.CallOptsNode) {
        for (const freeCallOpt of (defSubNode as CallOptsNode).nodes) {
          env.newFact(getFixedNodeFromFreeFixMap(freeToFixedMap, freeCallOpt));
        }
      }
    }

    for (const defSubNode of this.onlyIfExprs) {
      if (defSubNode.type === LiTexNodeType.CallOptsNode) {
        for (const freeCallOpt of (defSubNode as CallOptsNode).nodes) {
          env.newFact(getFixedNodeFromFreeFixMap(freeToFixedMap, freeCallOpt));
        }
      }
    }
  }
}

export function getFreeToFixedMap(
  templateNode: DefNode | InferNode,
  calledOpt: CallOptNode
): Map<string, string> {
  try {
    if (!areStrArrStructureEqual(templateNode.params, calledOpt.optParams)) {
      throw Error("Invalid number of given arguments.");
    }
    return relationBetweenStrArrArrays(
      templateNode.params,
      calledOpt.optParams
    );
  } catch (error) {
    throw error;
  }
}

export function getFixedNodeFromFreeFixMap(
  freeToFixedMap: Map<string, string>,
  freeCallOpt: CallOptNode
): CallOptNode {
  const node = new CallOptNode([]);
  node.optName = freeCallOpt.optName;
  node.optParams = freeVarsToFixedVars(freeCallOpt.optParams, freeToFixedMap);
  return node;
}
