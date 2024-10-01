import {
  CallOptNode,
  TemplateNode,
  makeTemplateNodeFact,
  TemplateNodeFact,
} from "./ast";
import { OptsConnectionSymbol } from "./common";
import {
  _paramsInOptAreDeclared,
  ExecInfo,
  execInfo,
  ResultType,
} from "./executor";

export class LiTeXEnv {
  errors: string[] = [];
  declaredVars: string[] = [];
  declaredTemplates: Map<string, TemplateNode> = new Map<
    string,
    TemplateNode
  >();
  constructor() {}

  varsAreNotDeclared(vars: string[] | string): Boolean {
    if (Array.isArray(vars)) {
      const duplicateVars = vars.filter((v) => this.declaredVars.includes(v));
      return duplicateVars.length > 0 ? false : true;
    } else {
      return !this.declaredVars.includes(vars as string);
    }
  }

  pushErrorMessage(s: string) {
    this.errors.push(s);
  }

  pushCallOptFact(fact: CallOptNode): ExecInfo {
    if (!_paramsInOptAreDeclared(this, fact.optParams)) {
      return execInfo(
        ResultType.Error,
        `Not all of referred symbols ${(fact as CallOptNode).optParams} are declared.`
      );
    }

    const declaredTemplate = this.getDeclaredTemplate(fact.optName);
    if (!declaredTemplate)
      return execInfo(ResultType.Error, fact.optName + "has not been declared");
    declaredTemplate?.facts.push(makeTemplateNodeFact(fact.optParams));
    return execInfo(ResultType.KnowTrue);
  }

  // Main function of the whole project
  // input full name of an opt, output the template of the lowest hierarchy
  getDeclaredTemplate(node: string | CallOptNode): TemplateNode | undefined {
    const isTop = (s: string): Boolean => {
      return !s.includes(OptsConnectionSymbol);
    };

    const getBeforeFirstColon = (str: string): string => {
      const colonIndex = str.indexOf(OptsConnectionSymbol);
      return colonIndex !== -1 ? str.slice(0, colonIndex) : str;
    };

    let s = "";
    if (node instanceof CallOptNode) s = node.optName;
    else s = node;

    let relatedTemplate: TemplateNode | undefined;
    if (isTop(s)) {
      relatedTemplate = this.declaredTemplates.get(s);
    } else {
      relatedTemplate = this.declaredTemplates
        .get(getBeforeFirstColon(s))
        ?.getDeclaredSubTemplate(s);
    }

    return relatedTemplate;
  }

  getFact(s: string): TemplateNodeFact[] | undefined {
    const node = this.getDeclaredTemplate(s);
    return node?.facts;
  }

  printCallOptFacts() {
    console.log("-----facts-------\n");
    for (const template of this.declaredTemplates.values()) {
      printFact(template);
    }
    console.log("");

    function printFact(template: TemplateNode, fatherName: string = "") {
      const name = fatherName + OptsConnectionSymbol + template.declOptName;
      console.log(name);
      console.log(template.facts.map((e) => e.params));
      for (const subTemplate of template.declaredTemplates.values()) {
        printFact(subTemplate, name);
      }
    }
  }

  printDeclaredTemplates() {
    console.log("-----template-----\n");

    for (const value of this.declaredTemplates) {
      console.log(value);
      console.log("");
    }
  }
}
