import { BuiltinCheckNode } from "./L_Nodes";
import { L_Env } from "./L_Env";
import { isPropertyParse, isFormParse, orParse } from "./L_Parser";

/**
 * Checker of builtins is in L_Checker.checkBuiltinCheckNode
 */
export const L_BuiltinParsers = new Map<
  string,
  (env: L_Env, tokens: string[]) => BuiltinCheckNode
>();
L_BuiltinParsers.set("is_property", isPropertyParse);
L_BuiltinParsers.set("or", orParse);
L_BuiltinParsers.set("is_form", isFormParse);

export function isBuiltinKeyword(key: string) {
  return L_BuiltinParsers.get(key) !== undefined;
}
