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

export class DefNode extends LiTeXNode {
  declOptName: string;
  params: string[];
  requirements: CallOptNode[] = [];
  onlyIfExprs: CallOptNode[] = [];
  iffExprs: CallOptNode[] = [];

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
