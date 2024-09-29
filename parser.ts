// ! TODO: 1. based on situations, know might not end with ; 2. introduce @infer @exist as syntactic sugar of know infer 3. iff should be iff(p(...), q(...)) 4. better callOpts 5. FATAL: know in (:) consumes ',' and (:) itself consumes ','
import {
  CallOptNode,
  CallOptsNode,
  InferNode,
  ExistNode,
  HaveNode,
  KnowNode,
  LiTeXNode,
  NotNode,
  OrNode,
  FreeVarsWithFactsNode,
  LetNode,
  DefNode,
  FactNode,
  TemplateNode,
  QuestionMarkNode,
} from "./ast";
import { LiTeXEnv } from "./env";
import { KnowTypeKeywords, DefTypeKeywords, specialChars } from "./common";

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

const stmtKeywords: {
  [key: string]: (env: LiTeXEnv, tokens: string[]) => any;
} = {
  ";": (env: LiTeXEnv, tokens: string[]) => {
    tokens.shift();
  },
  know: knowParse,
  "@": knowParse,
  have: haveParse,
  exist: existParse,
  not: notParse,
  or: orParse,
  let: letParse,
  def: templateParse,
  ":": templateParse,
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
    handleParseError(tokens, env, "Stmt");
    throw error;
  }
}

function knowParse(env: LiTeXEnv, tokens: string[]): KnowNode {
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
          node = factParse(env, tokens);
          knowNode.facts.push(node as FactNode);
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

function freeVarsAndTheirFactsParse(
  env: LiTeXEnv,
  tokens: string[]
): FreeVarsWithFactsNode {
  const params: string[] = [];
  const requirements: CallOptNode[] = [];

  if (!(tokens[0] === ")")) {
    while (1) {
      params.push(tokens.shift() as string);
      if (tokens[0] === ",") tokens.shift();
      else if (tokens[0] === "|") break;
      else if (tokens[0] === ")") break;
      else throw Error("infer parameters");
    }
    if (!(tokens[0] === ")")) {
      skip(tokens, "|");
      while (!(tokens[0] === ")")) {
        const node = callOptParse(env, tokens);
        if (node) requirements.push(node as CallOptNode);

        if (tokens[0] === ",") tokens.shift();
        if (tokens[0] === ")") break;
      }
    }
  }

  return new FreeVarsWithFactsNode(params, requirements);
}

function questionMarkParse(env: LiTeXEnv, tokens: string[]): QuestionMarkNode {
  try {
    skip(tokens, "?");
    tokens.unshift(":");
    const template = templateParse(env, tokens);
    return new QuestionMarkNode(template);
  } catch (error) {
    catchParseError(tokens, env, error, "?");
    throw error;
  }
}

function nonExecutableBlockParse(env: LiTeXEnv, tokens: string[]): LiTeXNode[] {
  try {
    const result: LiTeXNode[] = [];
    skip(tokens, "{"); // skip {

    while (!isCurToken("}", tokens)) {
      if (isCurToken("?", tokens)) {
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
    handleParseError(tokens, env, "infer: infer block parse");
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

      if (isCurToken(":", tokens)) {
        skip(tokens, ":");
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
    const node = freeVarsAndTheirFactsParse(env, tokens);
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
    const node = freeVarsAndTheirFactsParse(env, tokens);
    skip(tokens, ")"); // skip ;
    skip(tokens, ";");
    return new LetNode(node);
  } catch (error) {
    handleParseError(tokens, env, "let");
    throw error;
  }
}

function existParse(env: LiTeXEnv, tokens: string[]): ExistNode {
  try {
    skip(tokens, "exist");
    const declOptName = tokens.shift() as string;
    skip(tokens, "("); // skip '('

    const FreeVarsWithFactsNode = freeVarsAndTheirFactsParse(env, tokens);

    skip(tokens, ")"); // skip )

    const result = new ExistNode(
      declOptName,
      FreeVarsWithFactsNode.params,
      FreeVarsWithFactsNode.properties
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
    const block: CallOptsNode[] = nonExecutableBlockParse(
      env,
      tokens
    ) as CallOptsNode[];
    const notNode = new NotNode([]);

    for (const value of block) {
      for (const callOpt of value.nodes) {
        notNode.exprs.push(callOpt);
      }
    }

    return notNode;
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

    skip(tokens, ";");

    return new CallOptsNode(callOpts);
  } catch (error) {
    catchParseError(tokens, env, error, "facts");
    throw error;
  }
}

function orParse(env: LiTeXEnv, tokens: string[]) {
  try {
    skip(tokens, "or");
    const orNode = new OrNode();
    while (tokens[0] === "{") {
      orNode.blocks.push(nonExecutableBlockParse(env, tokens) as CallOptNode[]);
    }
    return orNode;
  } catch (error) {
    catchParseError(tokens, env, error, "or");
    throw error;
  }
}

function templateParse(env: LiTeXEnv, tokens: string[]): TemplateNode {
  function freeVars(tokens: string[]): string[] {
    const params: string[] = [];
    if (!(tokens[0] === ")")) {
      for (let i = 0; i < tokens.length; i++) {
        params.push(tokens[i] as string);
        if (tokens[i + 1] === ",") i++;
        else if (tokens[i + 1] === "|") break;
        else if (tokens[i + 1] === ")") break;
        else throw Error("infer parameters");
      }
    }
    return params;
  }

  try {
    skip(tokens, DefTypeKeywords);
    const declOptName = shiftVar(tokens);
    skip(tokens, "(");

    const curFreeVars = freeVars(tokens);

    const FreeVarsWithFactsNode = freeVarsAndTheirFactsParse(env, tokens);

    skip(tokens, ")");

    let result: LiTeXNode;
    switch (tokens[0]) {
      case "=>":
        skip(tokens, "=>");
        if (!isCurToken("{", tokens)) {
          result = new InferNode(
            declOptName,
            curFreeVars,
            FreeVarsWithFactsNode.properties
          );
          const facts = callOptsParse(env, tokens).nodes;
          for (let i = 0; i < facts.length; i++) {
            (result as InferNode).onlyIfExprs.push(facts[i]);
          }
        } else {
          const blockArrow = nonExecutableBlockParse(env, tokens);
          result = new InferNode(
            declOptName,
            curFreeVars,
            FreeVarsWithFactsNode.properties
          );
          (result as InferNode).onlyIfExprs = blockArrow;
        }

        break;

      case "{":
        const blockBrace = nonExecutableBlockParse(env, tokens);
        result = new InferNode(
          declOptName,
          curFreeVars,
          FreeVarsWithFactsNode.properties
        );
        (result as InferNode).onlyIfExprs = blockBrace;
        break;

      case "<=>":
        skip(tokens, "<=>");
        if (!isCurToken("{", tokens)) {
          result = new DefNode(
            declOptName,
            curFreeVars,
            FreeVarsWithFactsNode.properties
          );
          (result as DefNode).onlyIfExprs = (
            result as DefNode
          ).onlyIfExprs.concat(callOptsParse(env, tokens).nodes);
        } else {
          const blockDoubleArrow = nonExecutableBlockParse(env, tokens);
          result = new DefNode(
            declOptName,
            curFreeVars,
            FreeVarsWithFactsNode.properties
          );
          (result as DefNode).onlyIfExprs = blockDoubleArrow;
        }

        break;

      default:
        result = new DefNode(declOptName, curFreeVars, []);
        (result as DefNode).onlyIfExprs = FreeVarsWithFactsNode.properties;
        break;
    }

    // env.returnToSnapShot(snapShot);
    return result as TemplateNode;
  } catch (error) {
    handleParseError(tokens, env, "def");
    // env.returnToSnapShot(snapShot);
    throw error;
  }
}

function factParse(env: LiTeXEnv, tokens: string[]): FactNode {
  try {
    const left = callOptParse(env, tokens);

    return left;
  } catch (error) {
    handleParseError(tokens, env, "fact");
    throw error;
  }
}

function bracedFactsParse(env: LiTeXEnv, tokens: string[]): CallOptsNode {
  try {
    skip(tokens, "(");
    const opts: CallOptsNode = new CallOptsNode([]);
    while (1) {
      const opt = callOptParse(env, tokens);
      if (tokens[0] === ")") break;
      else if (tokens[0] === ",") {
        skip(tokens, ",");
        opts.nodes.push(opt);
      } else {
        throw Error("");
      }
    }
    skip(tokens, ")");
    return opts;
  } catch (error) {
    handleParseError(tokens, env, "braced facts");
    throw error;
  }
}
