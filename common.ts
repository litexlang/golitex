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
  "\n",
  "@",
  "!",
  "?",
  "&",
  "|",
  "$",
];

export const OptsConnectionSymbol = ":";
export const KnowTypeKeywords = [
  "@",
  "know",
  "suppose",
  "know_everything",
  "!",
];
export const ThenKeywords = ["then", "=>"];
export const IfThenKeywords = ["imply", "?"];
export const ExistKeywords = ["exist"];
export const DefKeywords = [":", "def"];
export const redefineTemplateDeclarationKeywords = ["re_def"];
export const TemplateDeclarationKeywords = [
  ...redefineTemplateDeclarationKeywords,
  ...DefKeywords,
  ...ExistKeywords,
  ...IfThenKeywords,
];

export const SymbolsFactsSeparator = "|";
export const ProveKeywords = ["&", "prove"];
export const suchThats = ["st", "is"];
export const byLBracket = "[";
export const byRBracket = "]";

export const L_Keywords = [
  ...specialChars,
  ...KnowTypeKeywords,
  ...ExistKeywords,
  ...TemplateDeclarationKeywords,
  ...ProveKeywords,
  SymbolsFactsSeparator,
  ...suchThats,
  byLBracket,
  byRBracket,
];

export const StdStmtEnds = [";", "\n"];
export const yaIfThenKeywords = ["$"];
export const LetKeywords = ["let"];
