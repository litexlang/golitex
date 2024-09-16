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

export class DefNode extends LiTeXNode {
  declOptName: string;
  params: string[];
  requirements: CallOptNode[] = [];
  onlyIfExprs: CallOptNode[] = [];
  iffExprs: CallOptNode[][] = [];

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

export class KnowNode extends LiTeXNode {
  callNodes: CallOptNode[] = [];
}

export class HaveNode extends LiTeXNode {
  params: string[];
  properties: CallOptNode[];

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
