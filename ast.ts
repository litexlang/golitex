// There are 3 things in LiTex: Declaration (var, fact-formula) ; check; know
export enum LiTexNodeType {
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
}
