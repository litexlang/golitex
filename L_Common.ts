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
];

export const DollarKeyword = "$";
export const SlashKeyword = "\\";
export const EqualKeyword = "=";
export const LetCompositeKeyword = "def_composite";
export const isFormKeyword = "is_form";
export const KnowTypeKeywords = ["know"];
export const ThenKeyword = "=>";
export const IffThenKeyword = "<=>";
export const IfKeyword = "if";
export const OnlyIfKeywords = ["only_if"];
export const IffKeyword = "iff";
export const DefKeywords = ["def"];

export const SymbolsFactsSeparator = ":";
export const ProveKeywords = ["prove"];

export const L_Ends = [";"];
export const LetKeyword = "let";
export const LetHashKeyword = "let#";
export const LetKeywords = ["let", "let#"];
export const HaveKeywords = ["have"];
export const ByKeyword = "by";
export const ProveByContradictionKeyword = "prove_by_contradiction";
export const IsKeywords = ["is"];
export const AreKeywords = ["are"];
export const IsAreKeywords = [...IsKeywords, ...AreKeywords];
export const NotKeywords = ["not"];
export const OrKeyword = "or";
export const AndKeyword = "and";
export const PostProveKeywords = ["because"];
export const WhenKeyword = "when";
export const ContradictionKeyword = "contradiction";
export const ReturnKeyword = ["return", "so"];
export const ReturnExistKeyword = ["return_exist"];
export const DefByKeywords = ["def_by"];
export const ClearKeyword = "clear";
export const RunKeyword = "run";

export const NotsKeyword = "nots";
// export const STKeyword = "st";

export const UseKeyword = "use";
export const MacroKeywords = "macro";

export const L_Keywords: string[] = [
  "#",
  ClearKeyword,
  MacroKeywords,
  ...specialChars,
  ByKeyword,
  WhenKeyword,
  ...KnowTypeKeywords,
  ...ThenKeyword,
  ...IffThenKeyword,
  IfKeyword,
  ...OnlyIfKeywords,
  ...IffKeyword,
  ...DefKeywords,
  ...ProveKeywords,
  ...L_Ends,
  ...LetKeywords,
  ...HaveKeywords,
  ProveByContradictionKeyword,
  ...IsKeywords,
  ...AreKeywords,
  ...NotKeywords,
  ...OrKeyword,
  ...PostProveKeywords,
  ...ReturnExistKeyword,
  ...ReturnKeyword,
  ...DefByKeywords,
  NotsKeyword,
  RunKeyword,
  EqualKeyword,
  // STKeyword,
];

export const LogicalKeywords = [IfKeyword, ...IffKeyword];
