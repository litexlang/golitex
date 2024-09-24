import { CallOptNode } from "./ast";

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
  usedAsKey: string[][],
  usedAsValue: string[][]
): Map<string, string> {
  const result = new Map<string, string>();

  for (let i = 0; i < usedAsKey.length; i++) {
    for (let j = 0; j < usedAsValue.length; j++) {
      result.set(usedAsKey[i][j], usedAsValue[i][j]);
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
