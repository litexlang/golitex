export class LiTeXNode {
  constructor() {}
}

export class callOptNode extends LiTeXNode {
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
  onlyIfExprs: callOptNode[] = [];
  iffExprs: callOptNode[] = [];

  constructor(declOptName: string, params: string[]) {
    super();
    this.declOptName = declOptName;
    this.params = params;
  }

  pushOnlyIf(optName: string, calledParams: string[]) {
    this.onlyIfExprs.push(new callOptNode(optName, calledParams));
  }

  pushIff(optName: string, calledParams: string[]) {
    this.iffExprs.push(new callOptNode(optName, calledParams));
  }
}
