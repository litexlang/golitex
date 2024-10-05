import {
  CallOptNode,
  CallOptsNode,
  InferNode,
  ExistNode,
  // HaveNode,
  KnowNode,
  LiTeXNode,
  LetNode,
  DefNode,
  FactNode,
  TemplateNode,
  DollarMarkNode,
  ProveNode,
  YAProveNode,
  HaveNode,
} from "./ast";
import { LiTeXEnv } from "./env";
import {
  KnowTypeKeywords,
  TemplateDeclarationKeywords,
  specialChars,
  DefBlockDeclareAndCall,
  ExistKeywords,
  SeparationBetweenSymbolsAndTheirFacts,
  ProveKeywords,
} from "./common";

function skip(tokens: string[], s: string | string[] = "") {
  if (typeof s === "string") {
    if (s === "") {
      return tokens.shift();
    } else if (s === tokens[0]) {
      return tokens.shift();
    } else {
      throw Error("unexpected symbol: " + tokens[0]);
    }
  } else {
    for (const value of s) {
      if (value === tokens[0]) {
        return tokens.shift();
      }
    }
    throw Error("unexpected symbol: " + tokens[0]);
  }
}

//! Not only gets symbol, in the future it will parse $$
function shiftVar(tokens: string[]): string {
  const token = tokens.shift();
  if (typeof token !== "string") {
    throw new Error("No more tokens");
  }
  return token;
}

function isCurToken(s: string, tokens: string[]) {
  return s === tokens[0];
}

function handleParseError(
  // tokens: string[],
  env: LiTeXEnv,
  m: string,
  index: number,
  start: string = "",
  addErrorDepth: Boolean = true
) {
  const errorIndex = index;
  env.pushNewError(`At ${start}[${errorIndex * -1}]: ${m}`, addErrorDepth);
}

const KeywordFunctionMap: {
  [key: string]: (env: LiTeXEnv, tokens: string[]) => any;
} = {
  ";": (env: LiTeXEnv, tokens: string[]) => {
    tokens.shift();
  },
  know: knowParse,
  "@": knowParse,
  have: haveParse,
  // not: notParse,
  // or: orParse,
  let: letParse,
  def: templateParse,
  ":": templateParse,
  exist: existParse,
  "?": templateParse,
  know_everything: (env: LiTeXEnv, tokens: string[]) => {
    const node = knowParse(env, tokens);
    node.isKnowEverything = true;
    return node;
  },
  "!": (env: LiTeXEnv, tokens: string[]) => {
    const node = knowParse(env, tokens);
    node.isKnowEverything = true;
    return node;
  },
  prove: yaProveParse,
  "&": yaProveParse,
};

export function LiTeXStmtsParse(
  env: LiTeXEnv,
  tokens: string[]
): LiTeXNode[] | null {
  try {
    const result: LiTeXNode[] = [];

    while (tokens[0] !== "_EOF") {
      const node = LiTexStmtParse(env, tokens);
      if (node) {
        result.push(node);
      }
    }
    return result;
  } catch (error) {
    return null;
  }
}

export function LiTexStmtParse(
  env: LiTeXEnv,
  tokens: string[]
): LiTeXNode | null {
  const start = tokens[0];
  const index = tokens.length;

  try {
    const func = KeywordFunctionMap[tokens[0]];
    const funcName = tokens[0];
    if (func) {
      const node = func(env, tokens);
      if (KnowTypeKeywords.includes(funcName)) {
        skip(tokens, ";");
      }
      if (node) {
        return node;
      } else {
        return null;
      }
    } else {
      const node = callOptsParse(env, tokens);
      return node;
    }
  } catch (error) {
    handleParseError(env, "Stmt", index, start);
    throw error;
  }
}

function knowParse(env: LiTeXEnv, tokens: string[]): KnowNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    const knowNode: KnowNode = new KnowNode();

    skip(tokens, KnowTypeKeywords);
    while (1) {
      let node: LiTeXNode;
      switch (tokens[0]) {
        case ":":
        case "def":
          node = templateParse(env, tokens);
          knowNode.facts.push(node as TemplateNode);
          break;
        default:
          node = callOptParse(env, tokens, true);
          knowNode.facts.push(node as FactNode);
      }

      if (tokens[0] === ",") skip(tokens, ",");
      else break;
    }

    return knowNode;
  } catch (error) {
    handleParseError(env, "know", index, start);
    throw error;
  }
}

// skips begin and end
function freeVarsAndTheirFactsParse(
  env: LiTeXEnv,
  tokens: string[],
  begin: string = "(",
  end: string = ")"
): { freeVars: string[]; properties: CallOptNode[] } {
  const requirements: CallOptNode[] = [];
  const freeVars: string[] = [];

  skip(tokens, begin);

  if (!(tokens[0] === end)) {
    while (1) {
      const freeVar = tokens.shift() as string;
      freeVars.push(freeVar);
      if (tokens[0] === ",") tokens.shift();
      else if (tokens[0] === SeparationBetweenSymbolsAndTheirFacts) break;
      else if (tokens[0] === end) break;
      else throw Error("infer parameters");
    }
    if (!(tokens[0] === end)) {
      skip(tokens, SeparationBetweenSymbolsAndTheirFacts);
      while (!(tokens[0] === end)) {
        const node = callOptParse(env, tokens);
        if (node) requirements.push(node as CallOptNode);

        if (tokens[0] === ",") tokens.shift();
        if (tokens[0] === end) break;
      }
    }
  }

  skip(tokens, end);

  return { freeVars: freeVars, properties: requirements };
}

function questionMarkParse(env: LiTeXEnv, tokens: string[]): DollarMarkNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    skip(tokens, DefBlockDeclareAndCall);
    tokens.unshift(":");
    const template = templateParse(env, tokens);
    return new DollarMarkNode(template);
  } catch (error) {
    handleParseError(env, "?", index, start);
    throw error;
  }
}

function nonExecutableBlockParse(env: LiTeXEnv, tokens: string[]): LiTeXNode[] {
  const start = tokens[0];
  const index = tokens.length;

  try {
    const result: LiTeXNode[] = [];
    skip(tokens, "{"); // skip {

    while (!isCurToken("}", tokens)) {
      if (isCurToken(DefBlockDeclareAndCall, tokens)) {
        const node = questionMarkParse(env, tokens);
        if (node) result.push(node);
        continue;
      }
      const node = LiTexStmtParse(env, tokens);
      if (node) result.push(node);
    }

    skip(tokens, "}"); // skip }

    return result;
  } catch (error) {
    handleParseError(env, "{}", index, start);
    throw error;
  }
}

function callOptParse(
  env: LiTeXEnv,
  tokens: string[],
  withFacts: Boolean = false
): CallOptNode {
  const index = tokens.length;
  const start = tokens[0];

  try {
    const opts: [string, string[]][] = [];
    const requirements: CallOptNode[][] = [];

    while (1) {
      const name = shiftVar(tokens) as string;

      if (!withFacts) {
        const params: string[] = [];

        skip(tokens, "(");
        if (!isCurToken(")", tokens)) {
          while (1) {
            params.push(shiftVar(tokens));
            if (isCurToken(",", tokens)) skip(tokens, ",");
            else if (isCurToken(")", tokens)) {
              skip(tokens, ")");
              break;
            } else throw Error("");
          }
        } else {
          skip(tokens, ")");
        }

        opts.push([name, params]);
      } else {
        const freeVarsAndFacts = freeVarsAndTheirFactsParse(env, tokens);
        opts.push([name, freeVarsAndFacts.freeVars]);
        requirements.push(freeVarsAndFacts.properties);
      }

      if (isCurToken(":", tokens)) {
        skip(tokens, ":");
      } else {
        break;
      }
    }

    return new CallOptNode(opts, requirements);
  } catch (error) {
    handleParseError(env, "operator", index, start);
    throw error;
  }
}

function callOptsParse(env: LiTeXEnv, tokens: string[]): CallOptsNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    const callOpts: CallOptNode[] = [];

    while (1) {
      callOpts.push(callOptParse(env, tokens));
      if (tokens[0] === ",") {
        skip(tokens, ",");
      } else if (tokens[0] === ";") {
        break;
      } else if (specialChars.includes(tokens[0]) && tokens[0] !== ";") {
        throw Error(
          tokens[0] +
            "is not expected to appear here.',' is used to split between two facts."
        );
      }
    }

    skip(tokens, ";");

    return new CallOptsNode(callOpts);
  } catch (error) {
    handleParseError(env, "operators", index, start);
    throw error;
  }
}

function templateParse(env: LiTeXEnv, tokens: string[]): TemplateNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    const declName = skip(tokens, TemplateDeclarationKeywords) as string; // KnowTypeKeywords
    const declOptName = shiftVar(tokens);

    const freeVarsFact: { freeVars: string[]; properties: CallOptNode[] } =
      freeVarsAndTheirFactsParse(env, tokens);

    // skip(tokens, ")");

    let result: LiTeXNode;
    switch (tokens[0]) {
      case "=>":
        skip(tokens, "=>");
        if (!isCurToken("{", tokens)) {
          result = new InferNode(
            declOptName,
            freeVarsFact.freeVars,
            freeVarsFact.properties
          );
          const facts = callOptsParse(env, tokens).nodes;
          for (let i = 0; i < facts.length; i++) {
            (result as InferNode).onlyIfExprs.push(facts[i]);
          }
        } else {
          const blockArrow = nonExecutableBlockParse(env, tokens);
          result = new InferNode(
            declOptName,
            freeVarsFact.freeVars,
            freeVarsFact.properties
          );
          (result as InferNode).onlyIfExprs = blockArrow;
        }

        break;

      case "{":
        const blockBrace = nonExecutableBlockParse(env, tokens);
        result = new InferNode(
          declOptName,
          freeVarsFact.freeVars,
          freeVarsFact.properties
        );
        (result as InferNode).onlyIfExprs = blockBrace;
        break;

      case "<=>":
        skip(tokens, "<=>");
        if (!isCurToken("{", tokens)) {
          result = new DefNode(
            declOptName,
            freeVarsFact.freeVars,
            freeVarsFact.properties
          );
          (result as DefNode).onlyIfExprs = (
            result as DefNode
          ).onlyIfExprs.concat(callOptsParse(env, tokens).nodes);
        } else {
          const blockDoubleArrow = nonExecutableBlockParse(env, tokens);
          result = new DefNode(
            declOptName,
            freeVarsFact.freeVars,
            freeVarsFact.properties
          );
          (result as DefNode).onlyIfExprs = blockDoubleArrow;
        }

        break;

      default:
        result = new DefNode(declOptName, freeVarsFact.freeVars, []);
        (result as TemplateNode).requirements = freeVarsFact.properties;
        break;
    }

    // env.returnToSnapShot(snapShot);
    return result as TemplateNode;
  } catch (error) {
    handleParseError(env, "declare template", index, start);
    // env.returnToSnapShot(snapShot);
    throw error;
  }
}

// function factParse(env: LiTeXEnv, tokens: string[]): FactNode {
//   try {
//     const left = callOptParse(env, tokens);

//     return left;
//   } catch (error) {
//     handleParseError(tokens, env, "fact");
//     throw error;
//   }
// }

function letParse(env: LiTeXEnv, tokens: string[]): LetNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    return new LetNode(freeVarsAndTheirFactsParse(env, tokens, "let", ";"));
  } catch (error) {
    handleParseError(env, "let", index, start);
    throw error;
  }
}

function yaProveParse(env: LiTeXEnv, tokens: string[]): YAProveNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    skip(tokens, ProveKeywords);
    const relatedOpt = callOptParse(env, tokens, true);
    const blockBrace = nonExecutableBlockParse(env, tokens);
    const result = new YAProveNode(
      relatedOpt.optNameAsLst,
      relatedOpt.optParams,
      relatedOpt.requirements,
      blockBrace
    );
    return result;
  } catch (error) {
    handleParseError(env, "prove", index, start);
    throw error;
  }
}

function existParse(env: LiTeXEnv, tokens: string[]): ExistNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    /** Copy code from templateParse */
    skip(tokens, TemplateDeclarationKeywords) as string; // KnowTypeKeywords
    const declOptName = shiftVar(tokens);

    const freeVarsFact: { freeVars: string[]; properties: CallOptNode[] } =
      freeVarsAndTheirFactsParse(env, tokens);

    let result: ExistNode;

    const blockBrace = nonExecutableBlockParse(env, tokens);
    result = new ExistNode(
      declOptName,
      freeVarsFact.freeVars,
      freeVarsFact.properties
    );
    (result as ExistNode).onlyIfExprs = blockBrace;

    return result;
  } catch (error) {
    handleParseError(env, "exist", index, start);
    throw error;
  }
}

function haveParse(env: LiTeXEnv, tokens: string[]): HaveNode {
  const start = tokens[0];
  const index = tokens.length;

  try {
    skip(tokens, "have");
    const params: string[] = [];
    while (1) {
      params.push(shiftVar(tokens));
      if (isCurToken(",", tokens)) {
        skip(tokens, ",");
        continue;
      } else if (isCurToken(":", tokens)) {
        skip(tokens, ":");
        break;
      } else {
        throw Error(`${tokens[0]} is supposed to be ',' or ':'`);
      }
    }

    const opt = callOptParse(env, tokens, false);
    return new HaveNode(params, opt);
  } catch (error) {
    handleParseError(env, "have", index, start);
    throw error;
  }
}
