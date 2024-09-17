// There are 3 things in LiTex: Declaration (var, fact-formula) ; check; know
export class LiTeXNode {
  constructor() {}
}

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

type FactExprNode = CallOptNode | IffNode | KnowNode;

export class DefNode extends LiTeXNode {
  declOptName: string;
  params: string[];
  requirements: FactExprNode[] = [];
  onlyIfExprs: FactExprNode[] = [];
  iffExprs: FactExprNode[] = [];

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
  callNodes: FactExprNode[] = [];
  defNodes: DefNode[] = [];
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
  properties: CallOptNode[];

  constructor(params: string[], properties: CallOptNode[]) {
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
  onlyIfExprs: FactExprNode[] = [];
  iffExprs: FactExprNode[] = [];

  constructor(optName: string, calledParams: string[]) {
    super();
    this.optName = optName;
    this.calledParams = calledParams;
  }
}

// Exist: means both var decl and know callOpt
export class ExistNode extends LiTeXNode {
  declOptName: string = "";
  params: string[] = [];
  requirements: FactExprNode[] = [];
  onlyIfExprs: FactExprNode[] = [];
  iffExprs: FactExprNode[] = [];

  constructor() {
    super();
  }
}
