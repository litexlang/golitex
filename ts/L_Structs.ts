import { OptFactNode, L_FactNode } from "./L_Facts";
import { L_Node } from "./L_Nodes";

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
  print?: boolean;
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
