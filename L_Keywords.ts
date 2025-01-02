export const specialChars = [
  "(",
  ")",
  "{",
  "}",
  "[",
  "]",
  ":",
  ",",
  ";",
  "&",
  "|",
  "\\",
  "=",
  "$",
  '"', // for regex parser
  "~",
];

export const L_Keywords = {
  Slash: "\\",
  DefOperator: "operator",
  isConcept: "is_concept",
  isForm: "is_form",
  Know: "know",
  Then: "=>",
  Iff: "iff",
  If: "if",
  DefConcept: "concept",
  Prove: "prove",
  L_End: ";",
  Let: "let",
  Have: "have",
  ProveByContradiction: "prove_by_contradiction",
  Is: "is",
  Not: "not",
  Or: "or",
  And: "and",
  Clear: "clear",
  Run: "run",
  Macro: "macro",
  LeftBrace: "(",
  RightBrace: ")",
  LeftCurlyBrace: "{",
  RightCurlyBrace: "}",
  LeftBracket: "[",
  RightBracket: "]",
  Colon: ":",
  Comma: ",",
  Semicolon: ";",
  Ampersand: "&",
  Pipe: "|",
  Backslash: "\\",
  Equal: "=",
  Dollar: "$",
  Lets: "lets",
  Include: "include",
  Commutative: "commutative",
  DefLiteralOperator: "literal_operator",
  IfVarPrefix: "~",
  LiteralOptPrefix: "@",
  MacroPrefix: "MACRO_",
  IndexedSymbol: "at",
  // TODO EXIST and any can not appear in some composites, which is weird e.g. know \frac{\frac{EXIST, EXIST}, 2} , so in the future I should make them stricter.
  ExistSymbol: "EXIST",
  AnySymbol: "ANY", //* anySymbol can not be equal to EXIST, and it can equal to any other symbols
  LeftFactLogicalFormulaSig: "\\[?",
  RightFactLogicalFormulaSig: "\\?]",
  FunctionTypeFactOptPrefix: "$",
  LetFormal: "let_formal",
  LetAlias: "let_alias",
  DefFunctional: "def_function",
};

export const builtinFactNames = new Set<string>();
[L_Keywords.isConcept, L_Keywords.isForm].forEach((e) =>
  builtinFactNames.add(e)
);
