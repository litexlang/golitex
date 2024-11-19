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
  "&",
  "|",
  "$",
];

export const KnowTypeKeywords = ["know", "assume"];
export const ThenKeywords = ["=>"];
export const OnlyIfThenKeywords = ["<="];
export const IffThenKeywords = ["<=>"];
export const IfKeywords = ["if"];
export const OnlyIfKeywords = ["only_if"];
export const IffKeywords = ["iff"];
export const ExistKeyword = "exist";
export const DefKeywords = ["def"];

export const SymbolsFactsSeparator = ":";
export const ProveKeywords = ["prove"];

export const L_Ends = [";", "\n"];
export const LetKeywords = ["let"];
export const HaveKeywords = ["have"];
export const ByKeyword = "by";
export const ProveByContradictionKeyword = "prove_by_contradiction";
export const IsKeywords = ["is"];
export const AreKeywords = ["are"];
export const IsAreKeywords = [...IsKeywords, ...AreKeywords];
export const NotKeywords = ["not"];
export const OrKeywords = ["or"];
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

export const L_Keywords: string[] = [
  "#",
  ClearKeyword,
  ...specialChars,
  ByKeyword,
  WhenKeyword,
  ...KnowTypeKeywords,
  ...ThenKeywords,
  ...OnlyIfThenKeywords,
  ...IffThenKeywords,
  ...IfKeywords,
  ...OnlyIfKeywords,
  ...IffKeywords,
  ExistKeyword,
  ...DefKeywords,
  ...ProveKeywords,
  ...L_Ends,
  ...LetKeywords,
  ...HaveKeywords,
  ProveByContradictionKeyword,
  ...IsKeywords,
  ...AreKeywords,
  ...NotKeywords,
  ...OrKeywords,
  ...PostProveKeywords,
  ...ReturnExistKeyword,
  ...ReturnKeyword,
  ...DefByKeywords,
  NotsKeyword,
  RunKeyword,
  UseKeyword,
  // STKeyword,
];

export const LogicalOptPairs: { [k: string]: string[] } = {
  if: ThenKeywords,
  iff: IffThenKeywords,
  only_if: OnlyIfThenKeywords,
  exist: ThenKeywords,
};

export const LogicalKeywords = [...IfKeywords, ...IffKeywords];
