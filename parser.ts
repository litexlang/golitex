import { resourceLimits } from "worker_threads";
import {
  CallOptEqlNode,
  CallOptNode,
  CanBeKnownNode,
  CheckNode,
  DefNode,
  ExistNode,
  FactExprNode,
  HaveNode,
  IffNode,
  KnowNode,
  LiTeXNode,
  LiTexNodeType,
  NotNode,
  ParamsColonFactExprsNode,
  PropertyNode,
} from "./ast";
import { LiTeXEnv } from "./env";
import { property } from "lodash";

const ExprEndings = [";"];
function isExprEnding(s: string) {
  return ExprEndings.includes(s);
}

function isCurToken(s: string, tokens: string[]) {
  return s === tokens[0];
}

function catchParseError(env: LiTeXEnv, err: any, m: string) {
  if (err instanceof Error) {
    if (err.message) handleParseError(env, err.message);
  }
  handleParseError(env, m);
}

function handleParseError(env: LiTeXEnv, message: string) {
  env.pushErrorMessage("parsing error: " + message);
}

const keywords: { [key: string]: Function } = {
  ";": (env: LiTeXEnv, tokens: string[]) => {
    tokens.shift();
  },
  def: defParse,
  know: knowParse,
  have: haveParse,
  property: propertyParse,
  exist: existParse,
  not: notParse,
};

export function LiTeXStmtsParse(
  env: LiTeXEnv,
  tokens: string[]
): LiTeXNode[] | null {
  try {
    const result: LiTeXNode[] = [];

    while (tokens[0] !== "_EOF") {
      const func = keywords[tokens[0]];
      if (func) result.push(func(env, tokens));
      else result.push(checkParse(env, tokens));
    }
    return result;
  } catch (error) {
    return null;
  }
}

export function LiTexStmtParse(env: LiTeXEnv, tokens: string[]): LiTeXNode {
  try {
    if (tokens[0] !== "_EOF") {
      const func = keywords[tokens[0]];
      if (func) return func(env, tokens);
      else {
        return checkParse(env, tokens);
      }
    } else {
      throw Error("EOF");
    }
  } catch (error) {
    handleParseError(env, "Stmt");
    throw error;
  }
}

function knowParse(env: LiTeXEnv, tokens: string[]): KnowNode {
  try {
    const knowNode: KnowNode = new KnowNode();

    tokens.shift(); // skip know
    while (!isCurToken(";", tokens)) {
      if (tokens[0] === "def") {
        const node: DefNode = defParse(env, tokens);
        knowNode.facts.push(node);
      } else if (tokens[0] === "exist") {
        const node: ExistNode = existParse(env, tokens);
        knowNode.facts.push(node);
      } else if (tokens[0] === "iff") {
        const node: IffNode = iffParse(env, tokens);
        knowNode.facts.push(node);
      } else {
        const node = factExprParse(env, tokens);
        if (node.type === LiTexNodeType.KnowNode) {
          throw Error("know can not be followed by know");
        }
        knowNode.facts.push(node as CanBeKnownNode);
      }

      if (tokens[0] === ",") tokens.shift();
      else if (isExprEnding(tokens[0])) break;
      else
        throw Error(
          "separation mark in know expression should be ',' , get '" +
            tokens[0] +
            "' instead."
        );
    }
    tokens.shift(); // skip ;

    return knowNode;
  } catch (error) {
    catchParseError(env, error, "know");
    throw error;
  }
}

function defParse(env: LiTeXEnv, tokens: string[]): DefNode {
  try {
    tokens.shift(); // skip "def"
    const declOptName = tokens.shift() as string;
    tokens.shift(); // skip '('

    const paramsColonFactExprsNode = paramsColonFactExprsParse(
      env,
      tokens,
      (s: string) => {
        return s === ")";
      }
    );

    tokens.shift(); // skip ")"

    const result = new DefNode(
      declOptName,
      paramsColonFactExprsNode.params,
      paramsColonFactExprsNode.properties
    );

    const block = blockParse(env, tokens);
    for (let i = 0; i < block.length; i++) {
      result.onlyIfExprs.push(block[i]);
    }

    return result;
  } catch (error) {
    handleParseError(env, "def");
    throw error;
  }
}

function paramsColonFactExprsParse(
  env: LiTeXEnv,
  tokens: string[],
  isEnd: (s: string) => Boolean
): ParamsColonFactExprsNode {
  const params: string[] = [];
  const requirements: FactExprNode[] = [];
  if (!isEnd(tokens[0])) {
    while (1) {
      params.push(tokens.shift() as string);
      if (tokens[0] === ",") tokens.shift();
      else if (tokens[0] === ":") break;
      else if (isEnd(tokens[0])) break;
      else throw Error("def parameters");
    }
    if (!isEnd(tokens[0])) {
      tokens.shift(); // skip :
      while (!isEnd(tokens[0])) {
        const node = factExprParse(env, tokens);
        requirements.push(node);

        if (tokens[0] === ",") tokens.shift();
        else if (isEnd(tokens[0])) break;
        else throw Error("def block parse");
      }
    }
  }

  return new ParamsColonFactExprsNode(params, requirements);
}

function factExprParse(env: LiTeXEnv, tokens: string[]): FactExprNode {
  // if (tokens[0] === "iff") {
  //   return iffParse(env, tokens);
  // } else
  if (tokens[0] === "know") {
    return knowParse(env, tokens);
  } else if (tokens[0] === "not") {
    return notParse(env, tokens);
  } else {
    return callOptParse(env, tokens);
  }
}

function blockParse(env: LiTeXEnv, tokens: string[]): LiTeXNode[] {
  try {
    const result: LiTeXNode[] = [];
    tokens.shift(); // skip {

    while (!isCurToken("}", tokens)) {
      const node = LiTexStmtParse(env, tokens);
      result.push(node);
    }

    tokens.shift(); // skip }

    return result;
  } catch (error) {
    handleParseError(env, "def: def block parse");
    throw error;
  }
}

function iffParse(env: LiTeXEnv, tokens: string[]): IffNode {
  try {
    tokens.shift();
    const left = callOptParse(env, tokens);
    const right = callOptParse(env, tokens);
    const result = new IffNode(left, right);
    tokens.shift(); // skip ;
    return result;
  } catch (error) {
    handleParseError(env, "iff");
    throw error;
  }
}

function callOptParse(env: LiTeXEnv, tokens: string[]): CallOptNode {
  try {
    if (tokens[0] === "eql") {
      return callOptEqlParse(env, tokens);
    }

    const optName = tokens.shift() as string;
    const calledParams: string[] = [];
    const temp = tokens[0];

    if (temp === "(") {
      // temp !== '(' means no parameter, which means this expression over
      // all variables that satisfy requirement are valid
      tokens.shift(); // skip (
      if (tokens[0] !== ")") {
        while (1) {
          calledParams.push(tokens.shift() as string);
          if (tokens[0] === ",") tokens.shift();
          else if (tokens[0] === ")") break;
          else throw Error("call opt parameter should be followed by , or )");
        }
      }
      tokens.shift(); // skip )
    }

    return new CallOptNode(optName, calledParams);
  } catch (error) {
    handleParseError(env, "call opt");
    throw error;
  }
}

function callOptEqlParse(env: LiTeXEnv, tokens: string[]): CallOptEqlNode {
  try {
    tokens.shift(); // skip eql
    const leftCallNode = callOptParse(env, tokens);
    tokens.shift(); // skip {
    const rightCallNodes: CallOptNode[] = [];
    while (1) {
      const opt = callOptParse(env, tokens);
      rightCallNodes.push(opt);

      if (tokens[0] === ",") tokens.shift();
      else if (tokens[0] === "}") break;
      else {
        throw Error("eql");
      }
    }
    tokens.shift(); // skip }

    return new CallOptEqlNode(
      leftCallNode.optName,
      leftCallNode.calledParams,
      rightCallNodes
    );
  } catch (error) {
    handleParseError(env, "eql");
    throw error;
  }
}

function haveParse(env: LiTeXEnv, tokens: string[]): HaveNode {
  try {
    tokens.shift();
    const node = paramsColonFactExprsParse(env, tokens, isExprEnding);
    tokens.shift(); // skip ;
    return new HaveNode(node);
  } catch (error) {
    handleParseError(env, "have");
    throw error;
  }
}

function checkParse(env: LiTeXEnv, tokens: string[]): CheckNode {
  try {
    const opts: CallOptNode[] = [];
    if (!isExprEnding(tokens[0])) {
      while (1) {
        opts.push(callOptParse(env, tokens));

        if (tokens[0] === ",") tokens.shift();
        if (isExprEnding(tokens[0])) break;
        else throw Error("check");
      }
    }
    tokens.shift();
    return new CheckNode(opts);
  } catch (error) {
    handleParseError(env, "check");
    throw error;
  }
}

function propertyParse(env: LiTeXEnv, tokens: string[]): PropertyNode {
  try {
    tokens.shift(); // skip "property"
    const declOptName = tokens.shift() as string;
    tokens.shift(); // skip '('

    const calledParams: string[] = [];
    if (!isCurToken(")", tokens)) {
      while (1) {
        calledParams.push(tokens.shift() as string);
        if (isCurToken(",", tokens)) tokens.shift();
        else if (isCurToken(")", tokens)) break;
      }
    }
    tokens.shift();
    const result = new PropertyNode(declOptName, calledParams);
    const block = blockParse(env, tokens);
    for (let i = 0; i < block.length; i++) {
      result.onlyIfExprs.push(block[i]);
    }

    return result;
  } catch (error) {
    handleParseError(env, "property");
    throw error;
  }
}

function existParse(env: LiTeXEnv, tokens: string[]): ExistNode {
  try {
    tokens.shift();
    const declOptName = tokens.shift() as string;
    tokens.shift(); // skip '('

    const paramsColonFactExprsNode = paramsColonFactExprsParse(
      env,
      tokens,
      (s: string) => {
        return s === ")";
      }
    );

    tokens.shift();

    const result = new ExistNode(
      declOptName,
      paramsColonFactExprsNode.params,
      paramsColonFactExprsNode.properties
    );

    return result;
  } catch (error) {
    handleParseError(env, "exist");
    throw error;
  }
}

function notParse(env: LiTeXEnv, tokens: string[]): NotNode {
  try {
    tokens.shift();
    const block: LiTeXNode[] = blockParse(env, tokens);
    return new NotNode(block);
  } catch (error) {
    handleParseError(env, "not");
    throw error;
  }
}
