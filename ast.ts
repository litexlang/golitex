import exp from "constants";

// There are 3 things in LiTex: Declaration (var, fact-formula) ; check; know
export enum LiTexNodeType {
  Node,
  CallOptNode,
  KnowNode,
  ExistNode,
  IffNode,
}

export class LiTeXNode {
  type: LiTexNodeType = LiTexNodeType.Node;
  constructor() {}
}
const NullNode = new LiTeXNode();

export class CallOptNode extends LiTeXNode {
  optName: string;
  calledParams: string[];

  constructor(optName: string, calledParams: string[]) {
    super();
    this.optName = optName;
    this.calledParams = calledParams;
  }
}

export class CallOptEqlNode extends CallOptNode {
  type: LiTexNodeType = LiTexNodeType.CallOptNode;
  eqlNodes: CallOptNode[];

  constructor(
    optName: string,
    calledParams: string[],
    eqlNodes: CallOptNode[]
  ) {
    super(optName, calledParams);
    this.eqlNodes = eqlNodes;
  }
}

// when parsing FactExprNode, need to pass in isEnd
export type FactExprNode = KnowNode | CallOptNode | OrNode | NotNode;

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
  "iff",
  "not",
  "or",
];

export class FactsNode extends LiTeXNode {
  facts: FactExprNode[] = [];
  constructor(facts: FactExprNode[]) {
    super();
    this.facts = facts;
  }
}

export class DefNode extends LiTeXNode {
  declOptName: string;
  params: string[];
  requirements: FactExprNode[] = [];
  onlyIfExprs: LiTeXNode[] = [];

  constructor(
    declOptName: string,
    params: string[],
    requirements: FactExprNode[]
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
  params: string[];
  properties: FactExprNode[];

  constructor(node: ParamsColonFactExprsNode) {
    super();
    this.params = node.params;
    this.properties = node.properties;
  }
}

export class ParamsColonFactExprsNode extends LiTeXNode {
  params: string[];
  properties: FactExprNode[];

  constructor(params: string[], properties: FactExprNode[]) {
    super();
    this.params = params;
    this.properties = properties;
  }
}

export class CheckNode extends LiTeXNode {
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

export class PropertyNode extends LiTeXNode {
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
  requirements: FactExprNode[] = [];

  constructor(
    declOptName: string,
    params: string[],
    requirements: FactExprNode[]
  ) {
    super();
    this.declOptName = declOptName;
    this.params = params;
    this.requirements = requirements;
  }
}

export class NotNode extends LiTeXNode {
  exprs: LiTeXNode[] = [];

  constructor(exprs: LiTeXNode[]) {
    super();
    this.exprs = exprs;
  }
}

export class OrNode extends LiTeXNode {
  blocks: LiTeXNode[][] = [];
}
