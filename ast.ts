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
  DefNode,
  HaveNode,
  ParamsColonFactExprsNode,
  PropertyNode,
  CheckNode,
  CallOptWithColonColonNode,
  OnlyIfNode,
  IfNode,
}

export class LiTeXNode {
  type: LiTexNodeType = LiTexNodeType.Node;
  constructor() {}
}
const NullNode = new LiTeXNode();

export class CallOptNode extends LiTeXNode {
  type: LiTexNodeType = LiTexNodeType.CallOptNode;
  opts: [string, string[]][];

  constructor(opts: [string, string[]][]) {
    super();
    this.opts = opts;
  }
}

// when parsing FactExprNode, need to pass in isEnd
export type FactExprNode =
  | KnowNode
  | CallOptNode
  | OrNode
  | NotNode
  | IffNode
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
  | DefNode
  | ExistNode
  | IffNode
  | CallOptNode
  | OrNode
  | NotNode;
export const canBeKnownNodeNames: string[] = [
  "def",
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

export class DefNode extends LiTeXNode {
  type: LiTexNodeType = LiTexNodeType.DefNode;
  declOptName: string;
  params: string[];
  requirements: LiTeXNode[] = [];
  onlyIfExprs: LiTeXNode[] = [];

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
  properties: LiTeXNode[];

  constructor(params: string[], properties: LiTeXNode[]) {
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
  right: LiTeXNode[];

  constructor(left: CallOptNode, right: LiTeXNode[]) {
    super();
    this.left = left;
    this.right = right;
  }
}

export class IfNode extends LiTeXNode {
  type: LiTexNodeType = LiTexNodeType.IfNode;
  left: LiTeXNode[];
  right: CallOptNode;

  constructor(left: LiTeXNode[], right: CallOptNode) {
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
