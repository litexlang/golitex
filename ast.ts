import { LiTeXEnv } from "./env";
import { ResultType } from "./executor";

// There are 3 things in LiTex: Declaration (var, fact-formula) ; check; know
export enum LiTexNodeType {
  Error,
  Node,
  NotNode,
  OrNode,
  OnlyIfFactNode,
  LiTexNodeType,
  CallOptNode,
  CallOptsNode,
  KnowNode,
  ExistNode,
  IffNode,
  FactsNode,
  InferNode,
  HaveNode,
  FreeVarsWithFactsNode,
  PropertyNode,
  CheckNode,
  CallOptWithColonColonNode,
  OnlyIfNode,
  IfNode,
  InheritNode,
  LetNode,
  DefNode,
  ProofNode,
  QuestionMarkNode,
}

export type TemplateNode = DefNode | InferNode;

export class LiTeXNode {
  type: LiTexNodeType = LiTexNodeType.Node;
  constructor() {}
}
const NullNode = new LiTeXNode();

export function makeCallOptNode(
  optName: string,
  optParams: string[][],
  optNameAsLst: string[]
) {
  const node = new CallOptNode([]);
  node.optName = optName;
  node.optParams = optParams;
  node.optNameAsLst = optNameAsLst;
  return node;
}

export class CallOptNode extends LiTeXNode {
  type: LiTexNodeType = LiTexNodeType.CallOptNode;
  optName: string = "";
  optParams: string[][] = [];
  optNameAsLst: string[] = [];

  constructor(opts: [string, string[]][]) {
    super();
    this.optName = opts.map((e) => e[0]).join(":");
    this.optParams = opts.map((e) => e[1]);
    this.optNameAsLst = opts.map((e) => e[0]);
  }

  getOptNameParamsPairs(): [string, string[]][] {
    return this.optNameAsLst.map((v, i) => {
      return [this.optName, this.optParams[i]];
    });
  }

  // paramsLst(): string[] {
  //   return this.optName.split(":");
  // }

  pushNewNameParamsPair(pair: [string, string[]]) {
    if (this.optName !== "") this.optName += ":" + pair[0];
    else this.optName += pair[0];

    this.optParams.push(pair[1]);
  }
}

// export class OnlyIfFactNode extends LiTeXNode {
//   type: LiTexNodeType = LiTexNodeType.OnlyIfFactNode;
//   // notice ifNode and onlyIfs can not be OnlyIfFactNode itself.
//   ifNode: CallOptNode;
//   onlyIfs: CallOptNode[];

//   constructor(ifNode: CallOptNode, onlyIfs: CallOptNode[]) {
//     super();
//     this.ifNode = ifNode;
//     this.onlyIfs = onlyIfs;
//   }
// }

export type FactNode = CallOptNode; // | OnlyIfFactNode;

export class InferNode extends LiTeXNode {
  type: LiTexNodeType = LiTexNodeType.InferNode;
  declOptName: string;
  params: string[][];
  requirements: LiTeXNode[] = [];
  onlyIfExprs: LiTeXNode[] = [];
  father: string = "";
  declaredTemplates: Map<string, TemplateNode> = new Map<
    string,
    TemplateNode
  >();

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

export type CanBeKnownNode = FactNode | InferNode | DefNode;
export class KnowNode extends LiTeXNode {
  type: LiTexNodeType = LiTexNodeType.KnowNode;
  facts: CanBeKnownNode[] = [];
}

export class HaveNode extends LiTeXNode {
  type: LiTexNodeType = LiTexNodeType.HaveNode;
  params: string[];
  properties: CallOptNode[];

  constructor(node: FreeVarsWithFactsNode) {
    super();
    this.params = node.params;
    this.properties = node.properties;
  }
}

export class FreeVarsWithFactsNode extends LiTeXNode {
  type: LiTexNodeType = LiTexNodeType.FreeVarsWithFactsNode;
  params: string[];
  properties: CallOptNode[];

  constructor(params: string[], properties: CallOptNode[]) {
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

export class ExistNode extends LiTeXNode {
  type: LiTexNodeType = LiTexNodeType.ExistNode;
  declOptName: string = "";
  params: string[] = [];
  requirements: CallOptNode[] = [];

  constructor(
    declOptName: string,
    params: string[],
    requirements: CallOptNode[]
  ) {
    super();
    this.declOptName = declOptName;
    this.params = params;
    this.requirements = requirements;
  }
}

export class NotNode extends LiTeXNode {
  type: LiTexNodeType = LiTexNodeType.NotNode;
  exprs: CallOptNode[] = [];

  constructor(exprs: CallOptNode[]) {
    super();
    this.exprs = exprs;
  }
}

export class OrNode extends LiTeXNode {
  type: LiTexNodeType = LiTexNodeType.OrNode;
  blocks: CallOptNode[][] = [];
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
  properties: CallOptNode[];

  constructor(node: FreeVarsWithFactsNode) {
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
  declaredTemplates: Map<string, TemplateNode> = new Map<
    string,
    TemplateNode
  >();

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

export class QuestionMarkNode extends LiTeXNode {
  type = LiTexNodeType.QuestionMarkNode;
  template: TemplateNode;

  constructor(template: TemplateNode) {
    super();
    this.template = template;
  }
}

export function getFreeToFixedMap(
  templateNode: TemplateNode,
  calledOpt: CallOptNode
): Map<string, string> {
  function relationBetweenStrArrArrays(
    usedAsKey: string[][],
    usedAsValue: string[][]
  ): Map<string, string> {
    const result = new Map<string, string>();

    for (let i = 0; i < usedAsKey.length; i++) {
      for (let j = 0; j < usedAsValue[i].length; j++) {
        result.set(usedAsKey[i][j], usedAsValue[i][j]);
      }
    }

    return result;
  }

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
  function freeVarsToFixedVars(
    strArrToChange: string[][],
    relation: Map<string, string>
  ): string[][] {
    const result: string[][] = [];

    for (const item of strArrToChange) {
      const cur: string[] = [];
      for (const subitem of item) {
        cur.push(relation.get(subitem) as string);
      }
      result.push(cur);
    }

    return result;
  }

  const node = new CallOptNode([]);
  node.optName = freeCallOpt.optName;
  node.optParams = freeVarsToFixedVars(freeCallOpt.optParams, freeToFixedMap);
  return node;
}

export function areStrArrStructureEqual(
  arr1: string[][],
  arr2: string[][]
): Boolean {
  // Check if the outer arrays have the same length
  if (arr1.length !== arr2.length) {
    return false;
  }

  // Check if each corresponding inner array has the same length
  for (let i = 0; i < arr1.length; i++) {
    if (arr1[i].length !== arr2[i].length) {
      return false;
    }
  }

  // If we've made it this far, the structures are equal
  return true;
}
