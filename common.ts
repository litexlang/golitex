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
  "!",
  "&",
  "|",
  "$",
];

export const KnowTypeKeywords = ["know", "assume"];
export const ThenKeywords = ["then", "=>"];
export const IfKeywords = ["if"];
export const OnlyIfKeywords = ["only_if"];
export const ExistKeywords = ["exist"];
export const DefKeywords = ["def"];

export const SymbolsFactsSeparator = "|";
export const ProveKeywords = ["prove"];
export const suchThats = ["st", "is"];
export const byLBracket = "[";
export const byRBracket = "]";

export const L_Keywords = [
  ...specialChars,
  ...KnowTypeKeywords,
  ...ExistKeywords,
  ...ProveKeywords,
  SymbolsFactsSeparator,
  ...suchThats,
  byLBracket,
  byRBracket,
];

export const StdStmtEnds = [";", "\n"];
export const LetKeywords = ["let"];
export const HaveKeywords = ["have"];

export const AssumeByContraKeywords = ["assume_by_contradiction"];
