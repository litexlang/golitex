import { CallOptNode, DefNode, KnowNode, LiTeXNode } from "./ast";
import { LiTeXEnv } from "./env";

function handleParseError(env: LiTeXEnv, message: string) {
  env.pushErrorMessage(message);
}

const keywords: { [key: string]: Function } = {
  ";": () => {},
  def: defParse,
  know: knowParse,
};

export function LiTeXParse(env: LiTeXEnv, tokens: string[]): Node[] | null {
  const result: Node[] = [];

  while (tokens[0] !== "_EOF") {
    result.push(keywords[tokens[0]](env, tokens));
  }
  return result;
}

function knowParse(env: LiTeXEnv, tokens: string[]): KnowNode {
  try {
    const knowNode: KnowNode = new KnowNode();

    tokens.shift(); // skip know
    if (tokens[0] !== ";") {
      while (1) {
        const node = callOptParse(env, tokens);
        knowNode.callNodes.push(node);

        if (tokens[0] === ",") tokens.shift();
        else if (tokens[0] === ";") break;
        else throw Error("know parse");
      }
    }
    tokens.shift(); // skip ;

    return knowNode;
  } catch (error) {
    handleParseError(env, "know");
    throw error;
  }
}

function defParse(env: LiTeXEnv, tokens: string[]): DefNode {
  try {
    tokens.shift(); // skip "def"
    const declOptName = tokens.shift() as string;
    tokens.shift(); // skip '('

    const params: string[] = [];
    if (tokens[0] !== ")") {
      while (1) {
        params.push(tokens.shift() as string);
        if (tokens[0] === ",") tokens.shift();
        else if (tokens[0] === ")") break;
        else throw Error("def parameters");
      }
    }
    tokens.shift(); // skip ;

    const result = new DefNode(declOptName, params);

    defBlockParse(env, tokens, result);

    return result;
  } catch (error) {
    handleParseError(env, "def");
    throw error;
  }
}

function defBlockParse(env: LiTeXEnv, tokens: string[], defNode: DefNode) {
  try {
    tokens.shift(); // skip {
    if (tokens[0] !== "}") {
      while (1) {
        const node = callOptParse(env, tokens);
        defNode.onlyIfExprs.push(node);

        if (tokens[0] === ",") tokens.shift();
        else if (tokens[0] === "}") break;
        else throw Error("def block parse");
      }
    }
    tokens.shift(); // skip }
  } catch (error) {
    handleParseError(env, "def: def block parse");
    throw error;
  }
}

function callOptParse(env: LiTeXEnv, tokens: string[]): CallOptNode {
  try {
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
