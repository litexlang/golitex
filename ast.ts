import { OptsConnectionSymbol } from "./common";
import { LiTeXEnv } from "./env";
import { ExecInfo, knowFactExec, resultInfo, ResultType } from "./executor";

// There are 3 things in LiTex: Declaration (var, fact-template) ; check; know
export enum LiTexNodeType {
  Error,
  Node,

  // Logic
  NotNode,
  OrNode,

  // Fact
  CallOptNode,
  CallOptsNode,

  // Operators
  KnowNode,
  ExistNode,
  HaveNode,
  LetNode,
  ProofNode,

  // Template
  InferNode,
  DefNode,

  // Helper
  FreeVarsWithFactsNode,
  QuestionMarkNode,
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

  getOptNameParamsPairs(): [string, string[]][] {
    return this.optNameAsLst.map((v, i) => {
      return [this.optName, this.optParams[i]];
    });
  }

  pushNewNameParamsPair(pair: [string, string[]]) {
    if (this.optName !== "") this.optName += OptsConnectionSymbol + pair[0];
    else this.optName += pair[0];

    this.optParams.push(pair[1]);
  }
}

export type TemplateNodeFact = {
  params: string[][];
  onlyIfs: CallOptNode[];
  activated: Boolean;
};
export function makeTemplateNodeFact(
  params: string[][],
  onlyIfs: CallOptNode[],
  activated: Boolean = true
) {
  return { params: params, onlyIfs: onlyIfs, activated: activated };
}

// Main data structure of the whole project
export abstract class TemplateNode extends LiTeXNode {
  type: LiTexNodeType = LiTexNodeType.InferNode;
  declOptName: string;
  requirements: LiTeXNode[] = [];
  onlyIfExprs: LiTeXNode[] = [];
  declaredTemplates = new Map<string, TemplateNode>();
  facts: TemplateNodeFact[] = [];
  freeVars: string[];

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

  initDeclaredTemplates() {
    for (let i = this.onlyIfExprs.length - 1; i >= 0; i--) {
      const value = this.onlyIfExprs[i];

      if (value instanceof QuestionMarkNode) {
        this.onlyIfExprs.splice(i, 1);

        const callNode = new CallOptNode([
          [value.template.declOptName, value.template.freeVars],
        ]);
        const templateNode: TemplateNode = value.template;

        this.onlyIfExprs.splice(i, 0, callNode, templateNode);
      }
    }

    for (let i = this.onlyIfExprs.length - 1; i >= 0; i--) {
      const value = this.onlyIfExprs[i];
      if (value instanceof TemplateNode) {
        value.initDeclaredTemplates();
        this.declaredTemplates.set(value.declOptName, value);
        this.onlyIfExprs.splice(i, 1);
      }
    }
  }

  abstract knowFactExecCheck(node: FactNode): ExecInfo;

  abstract emitFactByFixingFreeVars(
    env: LiTeXEnv,
    fixedNode: FactNode,
    emitWhat: LiTeXNode[] // pass in template.requirement or template.onlyIfExprs
  ): ExecInfo;
}

export class InferNode extends TemplateNode {
  type: LiTexNodeType = LiTexNodeType.InferNode;

  constructor(
    declOptName: string,
    freeVars: string[],
    requirements: LiTeXNode[]
  ) {
    super(declOptName, freeVars, requirements);
  }

  knowFactExecCheck(node: FactNode): ExecInfo {
    let template: undefined | TemplateNode = this as TemplateNode;
    for (let i = 0; ; i++) {
      if (template.freeVars.length !== node.optParams[i].length) {
        return resultInfo(
          ResultType.KnowError,
          `${template.declOptName} has ${template.freeVars.length} parameters, get ${node.optNameAsLst[i].length} instead.`
        );
      }

      if (i + 1 < node.optNameAsLst.length) {
        template = template.declaredTemplates.get(node.optNameAsLst[i + 1]);
        if (!template)
          return resultInfo(
            ResultType.KnowError,
            "Undefined operator " + node.optName
          );
      } else {
        break;
      }
    }
    return resultInfo(ResultType.KnowTrue);
  }

  emitFactByFixingFreeVars(env: LiTeXEnv, fixedNode: FactNode): ExecInfo {
    return resultInfo(ResultType.True);
  }
}

export type CanBeKnownNode = FactNode | InferNode | DefNode | TemplateNode;
export class KnowNode extends LiTeXNode {
  type: LiTexNodeType = LiTexNodeType.KnowNode;
  facts: CanBeKnownNode[] = [];
  isKnowEverything: Boolean = false;
}

export class HaveNode extends LiTeXNode {
  type: LiTexNodeType = LiTexNodeType.HaveNode;
  params: string[];
  properties: CallOptNode[];

  constructor(node: FreeVarsWithFactsNode) {
    super();
    this.params = node.params;
    this.properties = node.properties;
  }
}

export class FreeVarsWithFactsNode extends LiTeXNode {
  type: LiTexNodeType = LiTexNodeType.FreeVarsWithFactsNode;
  params: string[];
  properties: CallOptNode[];

  constructor(params: string[], properties: CallOptNode[]) {
    super();
    this.params = params;
    this.properties = properties;
  }
}

export class ExistNode extends LiTeXNode {
  type: LiTexNodeType = LiTexNodeType.ExistNode;
  declOptName: string = "";
  params: string[] = [];
  requirements: CallOptNode[] = [];

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

export class NotNode extends LiTeXNode {
  type: LiTexNodeType = LiTexNodeType.NotNode;
  exprs: CallOptNode[] = [];

  constructor(exprs: CallOptNode[]) {
    super();
    this.exprs = exprs;
  }
}

export class OrNode extends LiTeXNode {
  type: LiTexNodeType = LiTexNodeType.OrNode;
  blocks: CallOptNode[][] = [];
}

export type FactNode = CallOptNode;
export class CallOptsNode extends LiTeXNode {
  type: LiTexNodeType = LiTexNodeType.CallOptsNode;
  nodes: CallOptNode[] = [];
  constructor(nodes: CallOptNode[]) {
    super();
    this.nodes = nodes;
  }
}

export class LetNode extends LiTeXNode {
  type: LiTexNodeType = LiTexNodeType.LetNode;
  params: string[];
  properties: CallOptNode[];

  constructor(node: FreeVarsWithFactsNode) {
    super();
    this.params = node.params;
    this.properties = node.properties;
  }
}

export class DefNode extends TemplateNode {
  type: LiTexNodeType = LiTexNodeType.DefNode;

  constructor(
    declOptName: string,
    freeVars: string[],
    requirements: LiTeXNode[]
  ) {
    super(declOptName, freeVars, requirements);
  }

  // When a fact is to be stored, whether it satisfies requirements must be checked
  knowFactExecCheck(node: FactNode): ExecInfo {
    let template: undefined | TemplateNode = this as TemplateNode;
    for (let i = 0; ; i++) {
      if (template.freeVars.length !== node.optParams[i].length) {
        return resultInfo(
          ResultType.KnowError,
          template.declOptName +
            " has " +
            template.freeVars.length +
            " parameters, get " +
            node.optNameAsLst[i].length +
            " instead."
        );
      }

      if (i + 1 < node.optNameAsLst.length) {
        template = template.declaredTemplates.get(node.optNameAsLst[i + 1]);
        if (!template)
          return resultInfo(
            ResultType.KnowError,
            "Undefined operator " + node.optName
          );
      } else {
        break;
      }
    }
    return resultInfo(ResultType.KnowTrue);
  }

  emitFactByFixingFreeVars(
    env: LiTeXEnv,
    fixedNode: FactNode,
    emitWhat: LiTeXNode[] = this.onlyIfExprs
  ): ExecInfo {
    //! Chain reaction is not allowed, maybe I should add some syntax to allow user to use chain reaction.
    const freeToFixed = new Map<string, string>();

    for (let optIndex = 0; optIndex < fixedNode.optParams.length; optIndex++) {
      const argumentsOfCurrentOpt: string[] = fixedNode.optParams[optIndex];
      const curTemplateName = fixedNode.optNameAsLst
        .slice(0, optIndex + 1)
        .join(":");
      const curTemplate = env.getDeclaredTemplate(curTemplateName);
      if (!curTemplate) return resultInfo(ResultType.Error);

      for (
        let argIndex = 0;
        argIndex < argumentsOfCurrentOpt.length;
        argIndex++
      ) {
        if (argIndex < curTemplate.freeVars.length) {
          freeToFixed.set(
            curTemplate.freeVars[argIndex] as string,
            argumentsOfCurrentOpt[argIndex]
          );
        }
      }
    }

    for (let i = 0; i < emitWhat.length; i++) {
      if (emitWhat[i] instanceof CallOptsNode) {
        for (const onlyIfFact of (emitWhat[i] as CallOptsNode).nodes) {
          moreFactByMakingFreeVarsIntoFixed(onlyIfFact);
        }
      } else if (emitWhat[i] instanceof CallOptNode) {
        moreFactByMakingFreeVarsIntoFixed(emitWhat[i] as CallOptNode);
      }
    }

    //TODO: Has not emitted onlyIfs that binds to specific fact instead of Template.onlyIfs.
    return resultInfo(ResultType.KnowTrue);

    function moreFactByMakingFreeVarsIntoFixed(factToBeEmitted: CallOptNode) {
      // replace freeVars with fixedVars
      const newParams: string[][] = [];
      for (let j = 0; j < factToBeEmitted.optParams.length; j++) {
        const subParams: string[] = [];
        for (let k = 0; k < factToBeEmitted.optParams[j].length; k++) {
          const fixed = freeToFixed.get(factToBeEmitted.optParams[j][k]);
          if (fixed) subParams.push(fixed);
          else subParams.push(factToBeEmitted.optParams[j][k]);
        }
        newParams.push(subParams);
      }

      const relatedTemplate = env.getDeclaredTemplate(factToBeEmitted);
      relatedTemplate?.facts.push(makeTemplateNodeFact(newParams, []));
    }
  }
}

export function makeMapBetweenFreeVarsAndFixedVar(
  env: LiTeXEnv,
  opt: CallOptNode
): Map<string, string> | undefined {
  const names = opt.optName.split(OptsConnectionSymbol);
  const res = new Map<string, string>();

  let template = env.getDeclaredTemplate(names[0]);
  if (template?.facts.length !== opt.optParams[0].length) {
    return undefined;
  }
  for (let i = 0; i < opt.optParams[0].length; i++) {
    res.set(template?.freeVars[i], opt.optParams[0][i]);
  }

  for (let i = 1; i < names.length; i++) {
    template = template?.declaredTemplates.get(names[i]);
    if (template?.facts.length !== opt.optParams[i].length) {
      return undefined;
    }
    for (let j = 0; j < opt.optParams[i].length; j++) {
      res.set(template?.freeVars[j], opt.optParams[i][j]);
    }
  }

  return res;
}

export class QuestionMarkNode extends LiTeXNode {
  type = LiTexNodeType.QuestionMarkNode;
  template: TemplateNode;

  constructor(template: TemplateNode) {
    super();
    this.template = template;
  }
}
