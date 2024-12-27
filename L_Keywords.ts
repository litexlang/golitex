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
  DollarKeyword: "$",
  SlashKeyword: "\\",
  EqualKeyword: "=",
  DefCompositeKeyword: "def_composite",
  isPropertyKeyword: "is_property",
  isFormKeyword: "is_form",
  KnowTypeKeywords: "know",
  ThenKeyword: "=>",
  IffKeyword: "iff",
  IfKeyword: "if",
  DefFactKeywords: "def",
  ProveKeywords: "prove",
  L_End: ";",
  LetKeyword: "let",
  HaveKeywords: "have",
  ProveByContradictionKeyword: "prove_by_contradiction",
  IsKeywords: "is",
  NotKeywords: "not",
  OrKeyword: "or",
  AndKeyword: "and",
  ClearKeyword: "clear",
  RunKeyword: "run",
  MacroKeywords: "macro",
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
  Macro: "macro",
  Include: "include",
  Commutative: "commutative",
  DefLiteralOperator: "def_literal_operator",
  IfVarPrefix: "~if",
  LiteralOptPrefix: "@",
  MacroPrefix: "MACRO_",
  IndexedSymbolKeyword: "at",
  // TODO EXIST and any can not appear in some composites, which is weird e.g. know \frac{\frac{EXIST, EXIST}, 2} , so in the future I should make them stricter.
  ExistSymbol: "EXIST",
  AnySymbol: "ANY", //* anySymbol can not be equal to EXIST, and it can equal to any other symbols
  LeftFactLogicalFormulaSig: "\\[?",
  RightFactLogicalFormulaSig: "\\?]",
  FunctionalStructuredFactOptPrefix: "$",
  LetFormal: "let_formal",
};
