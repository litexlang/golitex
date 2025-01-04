import { OptFactNode, L_FactNode, L_Node } from "./L_Nodes";

export class OptSymbol {
  constructor(public name: string) {}

  toString() {
    return this.name;
  }

  fix(optMap: Map<string, string>) {
    const newName = optMap.get(this.name);
    if (newName !== undefined) return new OptSymbol(newName);
    else return this;
  }
}

export class FreeOptSymbol extends OptSymbol {}

export enum L_Out {
  Error,
  True,
  Unknown,
  False,
}

export type ExampleItem = {
  name: string;
  code: string[];
  debug: boolean;
  print: boolean;
  // test?: string[] | undefined;
  // runTest?: boolean;
};

export abstract class L_KnownFactReq {
  constructor() {}
}

export class OptKnownFactReq extends L_KnownFactReq {
  constructor(public opt: OptFactNode) {
    super();
  }
}

export class IfKnownFactReq extends L_KnownFactReq {
  constructor(public req: L_FactNode[]) {
    super();
  }
}

export class FormulaKnownFactReq extends L_KnownFactReq {
  constructor(public req: L_FactNode[]) {
    super();
  }
}

export class ParsedNode {
  constructor(public node: L_Node, public sc: string) {}
}
