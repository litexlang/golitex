export const specialChars = [
  "(",
  ")",
  "{",
  "}",
  ":",
  ",",
  ";",
  "@",
  "!",
  "$",
  "?",
  "&",
];

export const OptsConnectionSymbol = ":";
export const KnowTypeKeywords = [
  "@",
  "know",
  "suppose",
  "know_everything",
  "!",
];
export const ExistKeywords = ["exist", "?"];
export const redefineTemplateDeclarationKeywords = ["re_def"];
export const TemplateDeclarationKeywords = [
  ":",
  "def",
  ...redefineTemplateDeclarationKeywords,
  ...ExistKeywords,
];

export const DefBlockDeclareAndCall = "$"; // sort of works like do in coffeeScript and (function (...){...}).call(...) in JS

export const SeparationBetweenSymbolsAndTheirFacts = ":";
export const ProveKeywords = ["&", "prove"];

export const L_Keywords = [
  ...specialChars,
  ...KnowTypeKeywords,
  ...ExistKeywords,
  ...TemplateDeclarationKeywords,
  ...ProveKeywords,
];
