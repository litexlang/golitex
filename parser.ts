// ! TODO: 1. based on situations, know might not end with ; 2. introduce @infer @exist as syntactic sugar of know infer 3. iff should be iff(p(...), q(...)) 4. better callOpts 5. FATAL: know in (:) consumes ',' and (:) itself consumes ','
import {
  CallOptNode,
  CallOptsNode,
  CanBeKnownNode,
  canBeKnownNodeNames,
  CheckNode,
  InferNode,
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
  LetNode,
  DefNode,
} from "./ast";
import { LiTeXEnv } from "./env";
import { property } from "lodash";
import { specialChars } from "./lexer";

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

function isCurToken(s: string, tokens: string[]) {
  return s === tokens[0];
}

function catchParseError(tokens: string[], env: LiTeXEnv, err: any, m: string) {
  if (err instanceof Error) {
    if (err.message) handleParseError(tokens, env, err.message);
  }
  handleParseError(tokens, env, m);
}

function handleParseError(tokens: string[], env: LiTeXEnv, message: string) {
  env.pushErrorMessage(
    "parsing error: " + message + ' in "' + tokens.slice(0, 5).join(" ") + '"'
  );
}

const ExprEndings = [";"];

const stmtKeywords: { [key: string]: Function } = {
  ";": (env: LiTeXEnv, tokens: string[]) => {
    tokens.shift();
  },
  infer: inferParse,
  know: knowParse,
  have: haveParse,
  // property: propertyParse,
  exist: existParse,
  not: notParse,
  or: orParse,
  "<=>": iffParse,
  "=>": onlyIfParse,
  "<=": ifParse,
  inherit: inheritParse,
  let: letParse,
  def: defParse,
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
  // env.setSnapShot();

  try {
    const func = stmtKeywords[tokens[0]];
    const funcName = tokens[0];
    if (func) {
      const node = func(env, tokens);
      if (funcName === "know") {
        skip(tokens, ";"); // skip ;
      }
      if (node) {
        // env.returnToSnapShot();
        return node;
      } else {
        // env.returnToSnapShot();
        return null;
      }
    } else {
      const node = callOptsParse(env, tokens);
      // tokens.shift();

      // env.returnToSnapShot();
      return node;
    }
  } catch (error) {
    handleParseError(tokens, env, "Stmt");
    throw error;
  }
}

function knowParse(env: LiTeXEnv, tokens: string[]): KnowNode {
  try {
    const knowNode: KnowNode = new KnowNode();

    skip(tokens, "know"); // skip know
    while (1) {
      if (canBeKnownNodeNames.includes(tokens[0])) {
        knowNode.facts.push(stmtKeywords[tokens[0]](env, tokens));
      } else {
        // called by know
        const node = callOptParse(env, tokens);
        knowNode.facts.push(node as CallOptNode);
      }

      if (tokens[0] === ",") skip(tokens, ",");
      else break;
    }

    return knowNode;
  } catch (error) {
    catchParseError(tokens, env, error, "know");
    throw error;
  }
}

function getParams(tokens: string[]): string[] {
  const params: string[] = [];
  if (!(tokens[0] === ")")) {
    for (let i = 0; i < tokens.length; i++) {
      params.push(tokens[i] as string);
      if (tokens[i + 1] === ",") i++;
      else if (tokens[i + 1] === ":") break;
      else if (tokens[i + 1] === ")") break;
      else throw Error("infer parameters");
    }
  }
  return params;
}

function inferParse(env: LiTeXEnv, tokens: string[]): InferNode {
  const snapShot = env.getSnapShot();

  try {
    tokens.shift(); // skip "infer" or fatherDefName
    const declOptName = tokens.shift() as string;
    skip(tokens, "("); // skip '('

    const curFreeVars = [...env.fatherFreeVars, getParams(tokens)];
    env.fatherFreeVars = curFreeVars;

    const paramsColonFactExprsNode = paramsColonFactExprsParse(env, tokens);

    skip(tokens, ")"); // skip ")"

    const result = new InferNode(
      declOptName,
      curFreeVars,
      paramsColonFactExprsNode.properties
    );

    const block = blockParse(env, tokens);
    for (let i = 0; i < block.length; i++) {
      result.onlyIfExprs.push(block[i]);
    }

    env.returnToSnapShot(snapShot);
    return result;
  } catch (error) {
    handleParseError(tokens, env, "infer");
    env.returnToSnapShot(snapShot);
    throw error;
  }
}

function paramsColonFactExprsParse(
  env: LiTeXEnv,
  tokens: string[]
): ParamsColonFactExprsNode {
  const params: string[] = [];
  const requirements: CanBeKnownNode[] = [];
  if (!(tokens[0] === ")")) {
    while (1) {
      params.push(tokens.shift() as string);
      if (tokens[0] === ",") tokens.shift();
      else if (tokens[0] === ":") break;
      else if (tokens[0] === ")") break;
      else throw Error("infer parameters");
    }
    if (!(tokens[0] === ")")) {
      skip(tokens, ":"); // skip :
      while (!(tokens[0] === ")")) {
        const node = LiTexStmtParse(env, tokens);
        if (node) requirements.push(node as CanBeKnownNode);

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
    skip(tokens, "{"); // skip {

    while (!isCurToken("}", tokens)) {
      const node = LiTexStmtParse(env, tokens);
      if (node) result.push(node);
    }

    skip(tokens, "}"); // skip }

    return result;
  } catch (error) {
    handleParseError(tokens, env, "infer: infer block parse");
    throw error;
  }
}

function iffParse(env: LiTeXEnv, tokens: string[]): IffNode {
  try {
    skip(tokens, "<=>");
    const left = callOptParse(env, tokens);
    const right = callOptParse(env, tokens);
    const result = new IffNode(left, right);

    // tokens.shift(); // skip ;
    return result;
  } catch (error) {
    handleParseError(tokens, env, "<=>");
    throw error;
  }
}

function onlyIfParse(env: LiTeXEnv, tokens: string[]): OnlyIfNode {
  try {
    skip(tokens, "=>");
    const left = callOptParse(env, tokens);

    const right = blockParse(env, tokens);

    const result = new OnlyIfNode(left, right as CallOptsNode[]);
    // tokens.shift(); // skip ;
    return result;
  } catch (error) {
    handleParseError(tokens, env, "=>");
    throw error;
  }
}

function ifParse(env: LiTeXEnv, tokens: string[]): IfNode {
  try {
    skip(tokens, "<=");
    const left = blockParse(env, tokens);
    const right = callOptParse(env, tokens);
    const result = new IfNode(left as CallOptsNode[], right);
    // tokens.shift(); // skip ;
    return result;
  } catch (error) {
    handleParseError(tokens, env, "<=");
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
    handleParseError(tokens, env, "call opt");
    throw error;
  }
}

function haveParse(env: LiTeXEnv, tokens: string[]): HaveNode {
  try {
    skip(tokens, "have");
    // ! needs to put the following shift into paramsColonParse
    skip(tokens, "("); // skip ()
    const node = paramsColonFactExprsParse(env, tokens);
    skip(tokens, ")");
    skip(tokens, ";");
    return new HaveNode(node);
  } catch (error) {
    handleParseError(tokens, env, "have");
    throw error;
  }
}

function letParse(env: LiTeXEnv, tokens: string[]): HaveNode {
  try {
    skip(tokens, "let");
    skip(tokens, "(");
    const node = paramsColonFactExprsParse(env, tokens);
    skip(tokens, ")"); // skip ;
    skip(tokens, ";");
    return new LetNode(node);
  } catch (error) {
    handleParseError(tokens, env, "let");
    throw error;
  }
}

// function propertyParse(env: LiTeXEnv, tokens: string[]): PropertyNode {
//   try {
//     tokens.shift(); // skip "property"
//     const declOptName = tokens.shift() as string;
//     tokens.shift(); // skip '('

//     const calledParams: string[] = [];
//     if (!isCurToken(")", tokens)) {
//       while (1) {
//         calledParams.push(tokens.shift() as string);
//         if (isCurToken(",", tokens)) tokens.shift();
//         else if (isCurToken(")", tokens)) break;
//       }
//     }
//     tokens.shift();
//     const result = new PropertyNode(declOptName, calledParams);
//     const block = blockParse(env, tokens);
//     for (let i = 0; i < block.length; i++) {
//       result.onlyIfExprs.push(block[i]);
//     }

//     return result;
//   } catch (error) {
//     handleParseError(tokens, env, "property");
//     throw error;
//   }
// }

function existParse(env: LiTeXEnv, tokens: string[]): ExistNode {
  try {
    skip(tokens, "exist");
    const declOptName = tokens.shift() as string;
    skip(tokens, "("); // skip '('

    const paramsColonFactExprsNode = paramsColonFactExprsParse(env, tokens);

    skip(tokens, ")"); // skip )

    const result = new ExistNode(
      declOptName,
      paramsColonFactExprsNode.params,
      paramsColonFactExprsNode.properties
    );

    return result;
  } catch (error) {
    handleParseError(tokens, env, "exist");
    throw error;
  }
}

function notParse(env: LiTeXEnv, tokens: string[]): NotNode {
  try {
    skip(tokens, "not");
    const block: LiTeXNode[] = blockParse(env, tokens);
    return new NotNode(block);
  } catch (error) {
    handleParseError(tokens, env, "not");
    throw error;
  }
}

function callOptsParse(env: LiTeXEnv, tokens: string[]): CallOptsNode {
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

    // in current version, callOpt must end with ;
    skip(tokens, ";");

    return new CallOptsNode(callOpts);
  } catch (error) {
    catchParseError(tokens, env, error, "facts");
    throw error;
  }
}

function orParse(env: LiTeXEnv, tokens: string[]) {
  try {
    skip(tokens, "or"); // skip or
    const orNode = new OrNode();
    while (tokens[0] === "{") {
      orNode.blocks.push(blockParse(env, tokens));
    }
    return orNode;
  } catch (error) {
    catchParseError(tokens, env, error, "or");
    throw error;
  }
}

function inheritParse(env: LiTeXEnv, tokens: string[]): InferNode {
  try {
    skip(tokens, "inherit");
    const father = tokens[0];
    const result = inferParse(env, tokens);
    result.father = father;

    return result;
  } catch (error) {
    catchParseError(tokens, env, error, "inherit");
    throw error;
  }
}

function defParse(env: LiTeXEnv, tokens: string[]): DefNode {
  const snapShot = env.getSnapShot();

  try {
    skip(tokens, "def");
    const declOptName = shiftVar(tokens);
    skip(tokens, "(");

    const curFreeVars = [...env.fatherFreeVars, getParams(tokens)];
    env.fatherFreeVars = curFreeVars;

    const paramsColonFactExprsNode = paramsColonFactExprsParse(env, tokens);

    skip(tokens, ")");

    const result = new DefNode(
      declOptName,
      curFreeVars,
      paramsColonFactExprsNode.properties
    );

    env.returnToSnapShot(snapShot);
    return result;
  } catch (error) {
    handleParseError(tokens, env, "def");
    env.returnToSnapShot(snapShot);
    throw error;
  }
}
