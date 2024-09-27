import { CallOptNode } from "./ast";

export function IndexOfGivenSymbolInCallOpt(
  node: CallOptNode,
  s: string
): [number, number] | undefined {
  for (let i = 0; i < node.optNameAsLst.length; i++) {
    for (let j = 0; j < node.optNameAsLst[i].length; j++) {
      if (s === node.optNameAsLst[i][j]) {
        return [i, j];
      }
    }
  }

  return undefined;
}

export const OptsConnectionSymbol = ":";
