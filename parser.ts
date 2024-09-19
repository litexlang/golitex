// ! TODO: 1. based on situations, know might not end with ; 2. introduce @def @exist as syntactic sugar of know def 3. iff should be iff(p(...), q(...)) 4. better callOpts 5. FATAL: know in (:) consumes ',' and (:) itself consumes ','
import {
  CallOptNode,
  CallOptsNode,
  CanBeKnownNode,
  canBeKnownNodeNames,
  CheckNode,
  DefNode,
  ExistNode,
  FactExprNode,
  FactsNode,
  HaveNode,
  IffNode,
  KnowNode,
  LiTeXNode,
  LiTexNodeType,
  NotNode,
  OrNode,
  ParamsColonFactExprsNode,
  PropertyNode,
  FactExprNodeNames,
  OnlyIfNode,
  IfNode,
} from "./ast";
import { LiTeXEnv } from "./env";
import { property } from "lodash";

const ExprEndings = [";"];
function skip(tokens: string[], s: string = "") {
  if (s === "") {
    return tokens.shift();
  } else if (s === tokens[0]) {
    return tokens.shift();
  } else {
    throw Error("");
  }
}

function shiftVar(tokens: string[]): string {
  const token = tokens.shift();
  if (typeof token !== "string") {
    throw new Error("No more tokens");
  }
  return token;
}

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

const stmtKeywords: { [key: string]: Function } = {
  ";": (env: LiTeXEnv, tokens: string[]) => {
    tokens.shift();
  },
  def: defParse,
  know: knowParse,
  have: haveParse,
  property: propertyParse,
  exist: existParse,
  not: notParse,
  or: orParse,
  iff: iffParse,
  onlyif: onlyIfParse,
  if: ifParse,
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
  try {
    const func = stmtKeywords[tokens[0]];
    const funcName = tokens[0];
    if (func) {
      const node = func(env, tokens);
      if (funcName === "know") {
        tokens.shift(); // skip ;
      }
      if (node) return node;
      else return null;
    } else {
      const node = callOptsParse(env, tokens);
      // tokens.shift();
      return node;
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
    while (1) {
      if (canBeKnownNodeNames.includes(tokens[0])) {
        knowNode.facts.push(stmtKeywords[tokens[0]](env, tokens));
      } else {
        // called by know
        const node = callOptParse(env, tokens);
        knowNode.facts.push(node as CallOptNode);
      }

      if (tokens[0] === ",") tokens.shift();
      else break;
    }

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

    const paramsColonFactExprsNode = paramsColonFactExprsParse(env, tokens);

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
  tokens: string[]
): ParamsColonFactExprsNode {
  const params: string[] = [];
  const requirements: LiTeXNode[] = [];
  if (!(tokens[0] === ")")) {
    while (1) {
      params.push(tokens.shift() as string);
      if (tokens[0] === ",") tokens.shift();
      else if (tokens[0] === ":") break;
      else if (tokens[0] === ")") break;
      else throw Error("def parameters");
    }
    if (!(tokens[0] === ")")) {
      tokens.shift(); // skip :
      while (!(tokens[0] === ")")) {
        const node = LiTexStmtParse(env, tokens);
        if (node) requirements.push(node as LiTeXNode);

        // if (tokens[0] === ",") tokens.shift();
        if (tokens[0] === ")") break;
      }
    }
  }

  return new ParamsColonFactExprsNode(params, requirements);
}

// called by know

function blockParse(env: LiTeXEnv, tokens: string[]): LiTeXNode[] {
  try {
    const result: LiTeXNode[] = [];
    tokens.shift(); // skip {

    while (!isCurToken("}", tokens)) {
      const node = LiTexStmtParse(env, tokens);
      if (node) result.push(node);
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
    // tokens.shift(); // skip ;
    return result;
  } catch (error) {
    handleParseError(env, "iff");
    throw error;
  }
}

function onlyIfParse(env: LiTeXEnv, tokens: string[]): OnlyIfNode {
  try {
    tokens.shift();
    const left = callOptParse(env, tokens);

    const right = blockParse(env, tokens);

    const result = new OnlyIfNode(left, right);
    // tokens.shift(); // skip ;
    return result;
  } catch (error) {
    handleParseError(env, "iff");
    throw error;
  }
}

function ifParse(env: LiTeXEnv, tokens: string[]): IfNode {
  try {
    tokens.shift();
    const left = blockParse(env, tokens);
    const right = callOptParse(env, tokens);
    const result = new IfNode(left, right);
    // tokens.shift(); // skip ;
    return result;
  } catch (error) {
    handleParseError(env, "iff");
    throw error;
  }
}

function callOptParse(env: LiTeXEnv, tokens: string[]): CallOptNode {
  try {
    const opts: [string, string[]][] = [];
    while (1) {
      const name = shiftVar(tokens) as string;
      const params: string[] = [];
      skip(tokens, "(");
      while (1) {
        params.push(shiftVar(tokens));
        if (isCurToken(",", tokens)) skip(tokens, ",");
        else if (isCurToken(")", tokens)) {
          skip(tokens, ")");
          break;
        } else throw Error("");
      }

      opts.push([name, params]);

      if (isCurToken("::", tokens)) {
        skip(tokens, "::");
      } else {
        break;
      }
    }

    return new CallOptNode(opts);
  } catch (error) {
    handleParseError(env, "call opt");
    throw error;
  }
}

function haveParse(env: LiTeXEnv, tokens: string[]): HaveNode {
  try {
    tokens.shift();
    // ! needs to put the following shift into paramsColonParse
    tokens.shift(); // skip ()
    const node = paramsColonFactExprsParse(env, tokens);
    tokens.shift(); // skip ;
    return new HaveNode(node);
  } catch (error) {
    handleParseError(env, "have");
    throw error;
  }
}

// function checkParse(env: LiTeXEnv, tokens: string[]): CheckNode {
//   try {
//     const opts: CallOptNode[] = [];
//     if (!isExprEnding(tokens[0])) {
//       while (1) {
//         opts.push(callOptParse(env, tokens));

//         if (tokens[0] === ",") tokens.shift();
//         if (isExprEnding(tokens[0])) break;
//         else throw Error("check");
//       }
//     }
//     tokens.shift();
//     return new CheckNode(opts);
//   } catch (error) {
//     handleParseError(env, "check");
//     throw error;
//   }
// }

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

    const paramsColonFactExprsNode = paramsColonFactExprsParse(env, tokens);

    tokens.shift(); // skip )

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

function callOptsParse(env: LiTeXEnv, tokens: string[]): CallOptsNode {
  try {
    const callOpts: CallOptNode[] = [];

    while (1) {
      callOpts.push(callOptParse(env, tokens));
      if (tokens[0] !== ",") {
        // tokens.shift();
        break;
      } else {
        tokens.shift();
      }
    }

    // in current version, callOpt must end with ;
    skip(tokens, ";");

    return new CallOptsNode(callOpts);
  } catch (error) {
    catchParseError(env, error, "facts");
    throw error;
  }
}

function orParse(env: LiTeXEnv, tokens: string[]) {
  try {
    tokens.shift(); // skip or
    const orNode = new OrNode();
    while (tokens[0] === "{") {
      orNode.blocks.push(blockParse(env, tokens));
    }
    return orNode;
  } catch (error) {
    catchParseError(env, error, "or");
    throw error;
  }
}
