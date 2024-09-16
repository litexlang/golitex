import { DefNode, LiTeXNode } from "./ast";
import { LiTeXEnv } from "./env";

function handleParseError(env: LiTeXEnv, message: string) {
  env.pushErrorMessage(message);
}

const keywords: { [key: string]: Function } = {
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

function knowParse(env: LiTeXEnv, tokens: string[]): null {
  return null;
}

function defParse(env: LiTeXEnv, tokens: string[]): DefNode | null {
  try {
    tokens.shift(); // skip "def"
    const declOptName = tokens.shift() as string;
    tokens.shift(); // skip '('

    const params: string[] = [];
    while (tokens[0] !== ")") {
      if (tokens[0] === ",") {
        tokens.shift();
      } else {
        params.push(tokens.shift() as string);
      }
    }
    tokens.shift(); // skip ')'

    tokens.shift(); // skip {
    tokens.shift(); // skip }

    const result = new DefNode(declOptName, params);

    return result;
  } catch (error) {
    handleParseError(env, "def");
    return null;
  }
}
