import { on } from "events";
import { OptsConnectionSymbol } from "./common";
import { LiTeXEnv } from "./env";
import {
  _paramsInOptAreDeclared,
  _VarsAreNotDeclared,
  ExecInfo,
  execInfo,
  ResultType,
} from "./executor";

// There are several things in LiTex: Declaration (var, fact-template) ; check; know(let); emit
export enum LiTexNodeType {
  Error,
  Node,

  // Fact
  CallOptNode,
  CallOptsNode,

  // Operators
  KnowNode,
  ExistNode,
  HaveNode,
  LetNode,
  ProofNode,
  CheckInProof,

  // Template
  InferNode,
  DefNode,

  // Helper
  FreeVarsWithFactsNode,
  DollarMarkNode,
}

export abstract class LiTeXNode {
  type: LiTexNodeType = LiTexNodeType.Node;
  constructor() {}
}

export class CallOptNode extends LiTeXNode {
  type: LiTexNodeType = LiTexNodeType.CallOptNode;
  optName: string = "";
  optParams: string[][] = [];
  optNameAsLst: string[] = [];

  constructor(opts: [string, string[]][]) {
    super();

    this.optName = opts.map((e) => e[0]).join(OptsConnectionSymbol);
    this.optParams = opts.map((e) => e[1]);
    this.optNameAsLst = opts.map((e) => e[0]);
  }

  static create(name: string, params: string[][]) {
    const names = name.split(OptsConnectionSymbol);
    return new CallOptNode(names.map((e, i) => [e, params[i]]));
  }
}

export type TemplateNodeFact = {
  params: string[][];
  onlyIfs: CallOptNode[];
  requirements: CallOptNode[];
  activated: Boolean;
};
export function makeTemplateNodeFact(
  params: string[][],
  onlyIfs: CallOptNode[] = [],
  requirements: CallOptNode[] = [],
  activated: Boolean = true
) {
  return {
    params: params,
    onlyIfs: onlyIfs,
    activated: activated,
    requirements: requirements,
  };
}

// Main data structure of the whole project
export abstract class TemplateNode extends LiTeXNode {
  type: LiTexNodeType = LiTexNodeType.InferNode;
  declOptName: string;
  freeVars: string[];
  requirements: LiTeXNode[] = [];
  onlyIfExprs: LiTeXNode[] = [];
  declaredTemplates = new Map<string, TemplateNode>();
  facts: TemplateNodeFact[] = [];

  constructor(
    declOptName: string,
    freeVars: string[],
    requirements: LiTeXNode[]
  ) {
    super();
    this.declOptName = declOptName;
    this.freeVars = freeVars;
    this.requirements = requirements;
  }

  newFact(env: LiTeXEnv, fact: TemplateNodeFact): ExecInfo {
    if (!_paramsInOptAreDeclared(env, fact.params))
      return _VarsAreNotDeclared(fact);
    else {
      env.newSymbolsFactsPair(fact.params, this);
      // this.facts.push(fact);
    }
    return execInfo(ResultType.True);
  }

  // Input a full name with colons and get descendants from any depth
  getDeclaredSubTemplate(s: string): undefined | TemplateNode {
    const names: string[] = s.split(":");
    let curTemplate: TemplateNode | undefined = this;
    for (let i = 1; i < names.length; i++) {
      curTemplate = curTemplate?.declaredTemplates.get(names[i]);
      if (!curTemplate) {
        return undefined;
      }
    }
    return curTemplate;
  }

  // If a node is DollarMarkNode or TemplateNode, i.e. it is the son template of this, then it is pushed into this.declaredTemplates and it is removed from this.onlyIfExprs. If there is non-def, non-call node in block, report error
  initDeclaredTemplates(): ExecInfo {
    for (let i = this.onlyIfExprs.length - 1; i >= 0; i--) {
      const value = this.onlyIfExprs[i];

      if (value instanceof DollarMarkNode) {
        this.onlyIfExprs.splice(i, 1);

        const callNode = new CallOptNode([
          [value.template.declOptName, value.template.freeVars],
        ]);
        const templateNode: TemplateNode = value.template;

        //! Here lies a problem: the templateNode's optName should start with : and anything start with : means it inherits from all above.
        this.onlyIfExprs.splice(i, 0, templateNode, callNode);
      }
    }

    for (let i = this.onlyIfExprs.length - 1; i >= 0; i--) {
      const value = this.onlyIfExprs[i];
      if (value instanceof TemplateNode) {
        value.initDeclaredTemplates();
        // Here we overwrite the original declared functions.
        this.declaredTemplates.set(value.declOptName, value);
        this.onlyIfExprs.splice(i, 1);
      } else if (value instanceof CallOptsNode) {
        this.onlyIfExprs = insertListIntoListAndDeleteElemOnIndex(
          this.onlyIfExprs,
          (value as CallOptsNode).nodes,
          i
        );
      }
    }

    for (let i = 0; i < this.onlyIfExprs.length; i++) {
      if (this.onlyIfExprs[i].type !== LiTexNodeType.CallOptNode) {
        return execInfo(
          ResultType.DefError,
          `arguments of def block should have type callOpt-type or def-type.`
        );
      }
    }
    return execInfo(ResultType.DefTrue);

    function insertListIntoListAndDeleteElemOnIndex<T>(
      originalList: T[],
      itemsToInsert: T[],
      position: number
    ): T[] {
      const newList = [...originalList];
      newList.splice(position, 1, ...itemsToInsert);
      return newList;
    }
  }
}

export class DefNode extends TemplateNode {
  type: LiTexNodeType = LiTexNodeType.DefNode;
}

export class InferNode extends TemplateNode {
  type: LiTexNodeType = LiTexNodeType.InferNode;
}

export class ExistNode extends TemplateNode {
  type = LiTexNodeType.ExistNode;
}

export type CanBeKnownNode = FactNode | TemplateNode;
export class KnowNode extends LiTeXNode {
  type: LiTexNodeType = LiTexNodeType.KnowNode;
  facts: CanBeKnownNode[] = [];
  isKnowEverything: Boolean = false;
}

export type FactNode = CallOptNode | CallOptsNode;
export enum CallOptsNodeType {
  And,
  Or,
  Not,
}
export class CallOptsNode extends LiTeXNode {
  type: LiTexNodeType = LiTexNodeType.CallOptsNode;
  nodes: CallOptNode[] = [];
  factType: CallOptsNodeType = CallOptsNodeType.And;

  constructor(nodes: CallOptNode[]) {
    super();
    this.nodes = nodes;
  }
}

export class LetNode extends LiTeXNode {
  type: LiTexNodeType = LiTexNodeType.LetNode;
  vars: string[];
  properties: CallOptNode[];

  constructor(node: { freeVars: string[]; properties: CallOptNode[] }) {
    super();
    this.vars = node.freeVars;
    this.properties = node.properties;
  }
}

// Declare and call at the same time.
export class DollarMarkNode extends LiTeXNode {
  type = LiTexNodeType.DollarMarkNode;
  template: TemplateNode;

  constructor(template: TemplateNode) {
    super();
    this.template = template;
  }
}

export class ProveNode extends LiTeXNode {
  type = LiTexNodeType.ProofNode;
  templateName: string;
  freeVars: string[];
  requirements: LiTeXNode[];
  onlyIfExprs: LiTeXNode[];

  constructor(
    templateName: string,
    freeVars: string[],
    requirements: LiTeXNode[],
    onlyIfExprs: LiTeXNode[]
  ) {
    super();
    this.templateName = templateName;
    this.freeVars = freeVars;
    this.requirements = requirements;
    this.onlyIfExprs = onlyIfExprs;
  }
}
