import { CallOptNode } from "./ast";

export function freeVarsToFixedVars(
  node: CallOptNode,
  fixedVars: string[][],
  freeVars: string[][]
) {
  const fixedNode = new CallOptNode([]);

  for (const [index, opt] of node.getOptNameParamsPairs().entries()) {
    const newOpt: [string, string[]] = [node.getParaNames()[index], []];

    for (const variable of opt[1] as string[]) {
      let hasDefined = false;
      for (let i = freeVars.length - 1; i >= 0; i--) {
        for (let j = 0; j < freeVars[i].length; j++) {
          if (variable === freeVars[i][j]) {
            hasDefined = true;
            break;
          }
        }
        if (hasDefined) break;
      }
      if (!hasDefined) newOpt[1].push(variable);
    }

    fixedNode.pushNewNameParamsPair(newOpt);
  }

  return fixedNode;
}

export function IndexOfGivenSymbol(
  node: CallOptNode,
  s: string
): [number, number] | undefined {
  for (let i = 0; i < node.paramsLst().length; i++) {
    for (let j = 0; j < node.paramsLst()[i].length; j++) {
      if (s === node.paramsLst()[i][j]) {
        return [i, j];
      }
    }
  }

  return undefined;
}
