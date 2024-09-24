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

export function areStrArrStructureEqual(
  arr1: string[][],
  arr2: string[][]
): Boolean {
  // Check if the outer arrays have the same length
  if (arr1.length !== arr2.length) {
    return false;
  }

  // Check if each corresponding inner array has the same length
  for (let i = 0; i < arr1.length; i++) {
    if (arr1[i].length !== arr2[i].length) {
      return false;
    }
  }

  // If we've made it this far, the structures are equal
  return true;
}

export function relationBetweenStrArrArrays(
  arr1: string[][],
  arr2: string[][]
): Map<string, string> {
  const result = new Map<string, string>();

  for (let i = 0; i < arr1.length; i++) {
    for (let j = 0; j < arr2.length; j++) {
      result.set(arr1[i][j], arr2[i][j]);
    }
  }

  return result;
}

export function freeVarsToFixedVars(
  strArrToChange: string[][],
  relation: Map<string, string>
): string[][] {
  const result: string[][] = [];

  for (const item of strArrToChange) {
    const cur: string[] = [];
    for (const subitem of item) {
      cur.push(relation.get(subitem) as string);
    }
    result.push(cur);
  }

  return result;
}
