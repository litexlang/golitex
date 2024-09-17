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

type PropertyNode = CallOptNode | IffNode | KnowNode;

export class DefNode extends LiTeXNode {
  declOptName: string;
  params: string[];
  requirements: PropertyNode[] = [];
  onlyIfExprs: PropertyNode[] = [];
  iffExprs: PropertyNode[] = [];

  constructor(
    declOptName: string,
    params: string[],
    requirements: PropertyNode[]
  ) {
    super();
    this.declOptName = declOptName;
    this.params = params;
    this.requirements = requirements;
  }
}

export class KnowNode extends LiTeXNode {
  callNodes: PropertyNode[] = [];
  defNodes: DefNode[] = [];
}

export class HaveNode extends LiTeXNode {
  params: string[];
  properties: PropertyNode[];

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
