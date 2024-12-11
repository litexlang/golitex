import { BuiltinCheckNode, L_Node, OptNode, ToCheckNode } from "./L_Nodes";
import { L_Env } from "./L_Env";
import { isPropertyParse, isSymbolShapeParse, orParse } from "./L_Parser";

export const L_BuiltinParsers = new Map<
  string,
  (env: L_Env, tokens: string[]) => BuiltinCheckNode
>();
L_BuiltinParsers.set("is_property", isPropertyParse);
L_BuiltinParsers.set("or", orParse);
L_BuiltinParsers.set("is_symbol_shape", isSymbolShapeParse);

export function isBuiltinKeyword(key: string) {
  return L_BuiltinParsers.get(key) !== undefined;
}
