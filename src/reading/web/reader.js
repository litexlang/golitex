/* The same component is used by local preview, static export and host websites. */
(function (global) {
  "use strict";
  const copy = {
    en: { source:"Source", why:"Why it holds", verified:"Verified", failed:"Incomplete verification", accepted:"Accepted", rejected:"Not established", premise:"Actual grounds", rules:"Rules used", concepts:"Concepts", proof:"Explore the evidence", raw:"Inspect reading data", empty:"Follow the mathematics", emptyHint:"Open a .lit file or a complete Litex project to explore its statements, definitions and proof grounds.", definition:"Definition", references:"Occurrences", rulebook:"Rule Book", search:"Search rules", usedOnly:"Used in this book", noPremise:"This record has no earlier stored-fact citation.", unavailable:"Some reading information has not been exported.", catalogueOnly:"Catalogue identity; an authored description is not available in this bundle.", previous:"Previous", next:"Next",  back:"Back", selectedLegend:"Selected statement", premiseLegend:"Cited fact", noRules:"This statement does not use a builtin rule.", sourceLine:"Source line", noDefinition:"No source declaration is recorded in this bundle.", local:"Local proof context", engine:"Built with", uses:"Used here", notFalse:"A failed check does not prove the statement false." },
    zh: { source:"源码", why:"这句话为什么成立", verified:"验证通过", failed:"验证未全部通过", accepted:"已接受", rejected:"尚未建立", premise:"实际采用的依据", rules:"本次使用的规则", concepts:"概念", proof:"展开证明依据", raw:"查看阅读数据", empty:"沿着依据，读懂数学", emptyHint:"打开 .lit 文件或完整 Litex 项目，探索陈述、定义和证明依据之间的联系。", definition:"定义", references:"出现位置", rulebook:"规则手册", search:"搜索规则", usedOnly:"只看本书使用的规则", noPremise:"本条记录没有引用更早的已存事实。", unavailable:"部分阅读信息尚未导出。", catalogueOnly:"本条目记录了规则身份；数据包尚未提供完整说明。", previous:"上一页", next:"下一页",  back:"返回", selectedLegend:"当前陈述", premiseLegend:"引用的事实", noRules:"本句没有使用内置规则。", sourceLine:"源码行", noDefinition:"数据包中没有记录对应的源码声明。", local:"局部证明上下文", engine:"构建内核", uses:"在这里使用", notFalse:"检查未通过，并不表示这句话为假。" }
  };
  Object.assign(copy.en,{title:"Interactive textbook",hint:"Select source to read its explanation; follow facts or concepts to explore further.",therefore:"Therefore",previousStep:"Previous",nextStep:"Next",occurrenceLegend:"Concept",notExported:"Execution evidence unavailable",outerProof:"Enclosing proof",context:"Context",sourceMappingGap:"Some nested execution results have no precise source mapping.",category:"Rule category",allCategories:"All categories",builtin:"Builtin rules",builtin_theorem:"Builtin theorems",infer:"Inference rules",user_trust:"User assumption",axiom:"Axiom",axiom_release:"Axiom application"});
  Object.assign(copy.zh,{title:"可交互教科书",hint:"点击源码查看说明，点击事实或概念继续探索。",therefore:"因此",previousStep:"上一步",nextStep:"下一步",occurrenceLegend:"概念",notExported:"执行依据未导出",outerProof:"上一层证明",context:"Context",sourceMappingGap:"部分内部执行结果尚无精确的源码映射。",category:"规则分类",allCategories:"全部分类",builtin:"内置规则",builtin_theorem:"内置定理",infer:"推导规则",user_trust:"用户假设",axiom:"公理",axiom_release:"公理应用"});
  Object.assign(copy.en,{declarations:"Definitions and theorems used",trust:"Assumptions and axioms",trustUsed:"This derivation depends on these explicit assumptions or axioms."});
  Object.assign(copy.zh,{declarations:"采用的定义与定理",trust:"假设与公理",trustUsed:"这条推导依赖以下显式假设或公理。"});
  Object.assign(copy.en,{inferred:"Inferred fact",inferredFacts:"Facts inferred here",inferredFrom:"Inferred from",producer:"Source statement"});
  Object.assign(copy.zh,{inferred:"推导事实",inferredFacts:"本句推导出的事实",inferredFrom:"由此推导",producer:"产生它的原语句"});
  Object.assign(copy.en,{inferredCount:"Inferred {count}",closeInferences:"Close inferred facts"});
  Object.assign(copy.zh,{inferredCount:"推导 {count}",closeInferences:"收起推导结果"});
  Object.assign(copy.en,{inferenceBasis:"Inference basis",fromNamedDefinition:"From definition {name}",fromDefinition:"From the definition",fromNamedParamType:"From {name}'s parameter types",fromParamType:"From parameter types",fromRule:"By rule {name}",originUnavailable:"Inference origin unavailable",batchRules:"Rules used in this inference batch"});
  Object.assign(copy.zh,{inferenceBasis:"推导依据",fromNamedDefinition:"由定义 {name} 展开",fromDefinition:"由定义展开",fromNamedParamType:"由 {name} 的参数类型推出",fromParamType:"由参数类型推出",fromRule:"由规则 {name} 推出",originUnavailable:"推导来源尚未细分",batchRules:"本批推导使用的规则"});
  Object.assign(copy.en,{parameterTypeRecord:"Parameter type record",definitionResult:"Definition expansion",parameterTypeHint:"This records the argument's type, as specified by the definition.",definitionResultHint:"Unfolding the definition gives this fact.",inferenceSources:"Source statements",sourceStatement:"Original statement",inferenceSeed:"Facts involved",parameterTypesRule:"Parameter types",definitionExpansionRule:"Unfold a definition"});
  Object.assign(copy.zh,{parameterTypeRecord:"参数类型记录",definitionResult:"定义展开结果",parameterTypeHint:"这条记录表示本次参数的类型，类型要求来自所用定义。",definitionResultHint:"展开所用定义后，得到这条事实。",inferenceSources:"查看来源",sourceStatement:"原语句",inferenceSeed:"涉及的事实",parameterTypesRule:"参数类型",definitionExpansionRule:"展开定义"});
  Object.assign(copy.en,{fact:"Fact",hypothesis:"Local hypothesis",declaration:"Introduced by a declaration",verifiedFact:"Established fact",formation:"Formation evidence",hypothesisHint:"This fact is assumed inside the enclosing proof context.",declarationHint:"This fact is introduced by the object or parameter declaration.",factSourceGap:"This bundle has no source producer for this fact.",factProofGap:"Fact-specific evidence is unavailable; inspect its source statement."});
  Object.assign(copy.zh,{fact:"事实",hypothesis:"局部假设",declaration:"由声明引入",verifiedFact:"已建立的事实",formation:"表达式有定义的依据",hypothesisHint:"这条事实是所在证明上下文中的假设。",declarationHint:"这条事实由对象或参数的声明引入。",factSourceGap:"数据包尚未记录这条事实的来源语句。",factProofGap:"本条事实的独立依据尚未导出，可查看来源语句。"});
  Object.assign(copy.en,{wellDefined:"Well-defined expression",registration:"Registration",registrationHint:"The engine recorded this exact expression as well-defined in this scope.",registrationProof:"Its formation evidence is retained by the source statement.",wdGap:"Some well-definedness registrations have no exported source."});
  Object.assign(copy.zh,{wellDefined:"表达式有定义",registration:"登记记录",registrationHint:"内核在此作用域中登记了这个表达式有定义。",registrationProof:"其形成依据保留在来源语句中。",wdGap:"部分有定义登记尚未关联到导出的来源。"});
  Object.assign(copy.en,{book:"Contents and search",chapters:"Chapters",dependencies:"Dependencies",bookSearch:"Search all source",loading:"Loading chapter…",loadingIndex:"Loading search index…",noMatches:"No matches",sourceText:"Source text",noStatement:"This source line has no exported execution statement.",changedBuild:"The reading data changed. Reopen the book.",loadFailed:"Could not load reading data"});
  Object.assign(copy.zh,{book:"目录与搜索",chapters:"章节",dependencies:"依赖模块",bookSearch:"搜索全书源码",loading:"正在加载章节…",loadingIndex:"正在加载搜索索引…",noMatches:"没有匹配结果",sourceText:"源码文本",noStatement:"这行源码没有对应的执行语句记录。",changedBuild:"阅读数据已更新，请重新打开这本书。",loadFailed:"无法加载阅读数据"});
  Object.assign(copy.en,{statementDetails:"Statement details",statementType:"Statement type",typeUnavailable:"This bundle does not include the statement type.",statementFactHint:"A fact assertion and its recorded verification grounds.",statementDefinitionHint:"Defines a name, interface or mathematical structure.",statementDeclarationHint:"Introduces objects and records the facts established by this declaration.",statementProofHint:"A proof step with its target and recorded grounds.",statementReleaseHint:"Unpacks an existing theorem or definition into usable facts.",statementRegistrationHint:"Registers a property for subsequent uses of this predicate.",statementTrustHint:"Introduces an explicit assumption or axiom.",statementCommandHint:"Runs a session command.",propDefinitionHint:"Defines the predicate's parameters and the conditions under which it holds.",abstractDefinitionHint:"Declares a predicate's name and parameter interface.",theoremDefinitionHint:"States a named theorem with its proof.",introducedFacts:"Facts introduced here",validationBasis:"Facts used to check this statement",referencedDefinitions:"Definitions referenced"});
  Object.assign(copy.zh,{statementDetails:"语句详情",statementType:"语句类型",typeUnavailable:"此数据包尚未提供语句类型。",statementFactHint:"陈述一条事实，并查看实际记录的验证依据。",statementDefinitionHint:"定义名称、接口或数学结构。",statementDeclarationHint:"引入对象，并记录这次声明建立的事实。",statementProofHint:"展示这一步证明的目标和实际采用的依据。",statementReleaseHint:"展开已有定理或定义，取得可用的事实。",statementRegistrationHint:"登记命题的性质，供后续使用。",statementTrustHint:"引入显式假设或公理。",statementCommandHint:"执行会话命令。",propDefinitionHint:"定义这个命题的参数和成立条件。",abstractDefinitionHint:"声明命题的名称与参数接口。",theoremDefinitionHint:"给出命名定理及其证明。",introducedFacts:"本句引入的事实",validationBasis:"检查本句时采用的事实",referencedDefinitions:"引用的定义"});
  Object.assign(copy.en,{mathematicalMeaning:"Mathematical meaning",parameterRange:"Parameter domain",iff:"if and only if",and:"and",setKind:"is a set",nonemptySetKind:"is a nonempty set",finiteSetKind:"is a finite set",takeObjects:"Choose objects in the following domains",alsoSatisfies:"Also satisfying",valueRange:"Value range",meaningUnavailable:"A mathematical explanation is not available in this bundle yet.",abstractMeaning:"This predicate is specified by its interface; no equivalent conditions are defined here.",closeHelp:"Close explanation",typeHelp:"About this statement type",inferredHelp:"A recorded consequence of processing a statement, available for later citations.",mathGrounds:"Grounds",underHypotheses:"Under the current proof assumptions",unverifiedMeaning:"This statement has not been established.",unexecutedMeaning:"This statement has not been executed in this context.",viewDefinition:"Definition: {name}",viewSource:"Locate in source"});
  Object.assign(copy.zh,{mathematicalMeaning:"数学含义",parameterRange:"参数范围",iff:"当且仅当",and:"且",setKind:"是集合",nonemptySetKind:"是非空集合",finiteSetKind:"是有限集合",takeObjects:"在以下范围内取对象",alsoSatisfies:"同时满足",valueRange:"取值范围",meaningUnavailable:"此数据包暂未提供这条语句的数学解释。",abstractMeaning:"这是由接口指定的命题，此处没有定义它的等价条件。",closeHelp:"收起说明",typeHelp:"这种语句的作用",inferredHelp:"这是处理语句时记录的推导结果，可以被后续语句引用。",mathGrounds:"依据",underHypotheses:"在当前证明假设下",unverifiedMeaning:"这条语句尚未建立。",unexecutedMeaning:"这条语句在此上下文中尚未执行。",viewDefinition:"定义：{name}",viewSource:"在源码中定位"});
  Object.assign(copy.en,{propGuideTitle:"What is a prop statement?",propGuidePurpose:"prop gives a name to a mathematical condition with parameters. You can then use that name in theorem statements and proofs.",propGuideUse:"A definition does not establish any particular instance. An instance holds when its arguments satisfy all the defining conditions.",propGuideExample:"An example",propGuideMeaning:"Here x R requires a real argument, and nonnegative(x) means that x is nonnegative. The definition does not assert that every real number is nonnegative.",propGuideProof:"by def $nonnegative(3) substitutes 3 for x and checks 3 >= 0. This establishes the fact that 3 is nonnegative, which later statements can use."});
  Object.assign(copy.zh,{propGuideTitle:"什么是 prop 语句？",propGuidePurpose:"prop 用来给一个带参数的数学条件起名字，定义一个命题。这样就能在定理和证明中反复使用这个名字。",propGuideUse:"定义本身不证明任何具体实例。代入的参数满足定义中的全部条件时，对应的命题才成立。",propGuideExample:"一个例子",propGuideMeaning:"这里 x R 要求参数是实数，nonnegative(x) 表示“x 非负”。这个定义没有声称所有实数都非负。",propGuideProof:"by def $nonnegative(3) 把 x 换成 3，检查 3 >= 0，建立“3 非负”这个事实，后面的语句就可以继续使用它。"});
  Object.assign(copy.en,{typesettingUnavailable:"Formula typesetting is unavailable; showing the retained mathematical text.",propHelpButton:"About prop"});
  Object.assign(copy.zh,{typesettingUnavailable:"公式排版暂不可用，以下保留完整的数学文本。",propHelpButton:"了解 prop 语句"});
  Object.assign(copy.en,{referenceCount:"{count} references",currentFileReferences:"Current file · {count} references",noReferences:"No source references in this file.",referenceHelp:"Source references only; excludes the declaration and inferred output.",closeReferences:"Close references",referenceFor:"References to {name}",referenceLine:"Line {line}"});
  Object.assign(copy.zh,{referenceCount:"引用 {count} 处",currentFileReferences:"当前文件 · {count} 处",noReferences:"当前文件没有源码引用。",referenceHelp:"只统计源码中的引用，不含定义本身和推导输出。",closeReferences:"收起引用",referenceFor:"{name} 的引用",referenceLine:"第 {line} 行"});
  // Keys are exported AST variants, not keywords inferred from source text.
  const statementTypes = {
    Fact:["Fact assertion","事实陈述","fact"],
    Definition:["Definition statement","定义语句"],Trust:["Explicit assumption","显式假设"],By:["Proof step","证明步骤"],ReleaseAndExpand:["Unpacking statement","展开语句"],Register:["Property registration","性质登记"],Witness:["Witness proof","构造见证"],ProofBlock:["Proof block","证明块"],Command:["Session command","会话命令"],
    DefPropStmt:["Proposition definition","命题定义","prop","propDefinitionHint"],DefAbstractPropStmt:["Abstract proposition declaration","抽象命题声明","abstract_prop","abstractDefinitionHint"],DefThmStmt:["Theorem","定理","thm","theoremDefinitionHint"],AxiomStmt:["Axiom declaration","公理声明","axiom"],DefStrategyStmt:["Proof strategy definition","证明策略定义","strategy"],DefTemplateStmt:["Template definition","模板定义","template"],DefStructStmt:["Structure definition","结构定义","struct"],
    LetObjStmt:["Object binding","对象绑定","let"],HaveObjInNonemptySetStmt:["Object declaration","对象声明","have"],HaveObjEqualStmt:["Object definition by equality","等式定义对象","have"],HaveObjByExistFactsStmt:["Objects from existence","由存在性引入对象","have"],ObtainObjFromExistFact:["Witness extraction","提取存在见证","obtain"],ObtainObjFromAtomicFact:["Witness extraction from a predicate","从命题提取见证","obtain"],HaveByPreimageStmt:["Preimage object declaration","引入原像对象","have by fn_preimage"],HaveByReplacementAxiomStmt:["Replacement construction","替换公理构造","have by replacement_axiom"],
    HaveFnEqualStmt:["Function definition","函数定义","have fn"],HaveFnEqualCaseByCaseStmt:["Function definition by cases","分情况定义函数","have fn"],HaveFnByInducStmt:["Function definition by induction","归纳定义函数","have fn"],HaveFnByForallExistUniqueStmt:["Function from unique existence","由唯一存在性定义函数","have fn"],DefAlgoByCasesStmt:["Algorithm by cases","分情况定义算法","algo"],DefAlgoByInducStmt:["Algorithm by induction","归纳定义算法","algo"],
    ByDefStmt:["Definition expansion","按定义展开","by def"],ByThmStmt:["Theorem application","应用定理","by thm"],ByCasesStmt:["Proof by cases","分类证明","by cases"],ByContraStmt:["Proof by contradiction","反证法","by contra"],ByEnumerateFiniteSetStmt:["Proof by finite enumeration","有限枚举证明","by enumerate"],ByInducStmt:["Induction proof","归纳证明","by induc"],ByStrongInducStmt:["Strong induction proof","强归纳证明","by strong_induc"],ByForStmt:["Range enumeration proof","范围枚举证明","by for"],ByExtensionStmt:["Set extensionality proof","集合外延证明","by extension"],ByFnExtensionStmt:["Function extensionality proof","函数外延证明","by fn_extension"],
    ReleaseThmStmt:["Theorem instantiation","实例化定理","release thm"],ReleaseStructDefStmt:["Structure definition release","展开结构定义","release"],ReleaseObjDefStmt:["Object definition release","展开对象定义","release"],ReleaseCartDefStmt:["Cartesian product definition release","展开笛卡尔积定义","release"],ReleaseTupleDefStmt:["Tuple definition release","展开元组定义","release"],ExpandRangeStmt:["Range membership expansion","展开范围归属","expand"],ReleaseZornLemmaStmt:["Zorn's lemma application","应用佐恩引理","release"],ReleaseAxiomOfChoiceStmt:["Axiom of choice application","应用选择公理","release"],ReleaseRegularityAxiomStmt:["Regularity axiom application","应用正则公理","release"],
    RegisterTransitivePropStmt:["Transitivity registration","登记传递性","register transitive"],RegisterSymmetricPropStmt:["Symmetry registration","登记对称性","register symmetric"],RegisterReflexivePropStmt:["Reflexivity registration","登记自反性","register reflexive"],WitnessExistFact:["Existence proof by witness","构造存在见证","witness"],WitnessAtomicFact:["Predicate proof by witness","构造命题见证","witness"],WitnessNonemptySet:["Nonemptiness proof by witness","构造非空集合见证","witness"],ClaimStmt:["Local claim","局部断言","claim"],SketchStmt:["Proof sketch","证明草稿","sketch"],TrustStmt:["Explicit assumption","显式假设","trust"],TrustHaveStmt:["Objects with explicit assumptions","带假设的对象声明","trust have"],EvalStmt:["Expression evaluation","表达式求值","eval"]
  };
  const roles = { base_in_real_proof:["Real base", "底数属于实数"], nonnegative_addend_proof:["Nonnegative addend", "加项非负"], well_defined_proof:["Well-defined expressions", "表达式有定义"], well_defined:["Well-defined expressions", "表达式有定义"], searched_proof:["Selected proof", "采用的证明"], verify_result:["Verification grounds", "验证依据"], store_and_infer_result:["Established knowledge", "建立的知识"], store_and_infer:["Established knowledge", "建立的知识"], local_env:["Local context", "局部上下文"], introduced_params:["Introduced parameters", "引入的参数"], assumed_dom_facts:["Local hypotheses", "局部假设"], proved_then_facts:["Conclusions", "结论"], cite_fact_id:["Cited fact", "引用的事实"], source_fact_id:["Source fact", "来源事实"], fact:["Statement", "数学陈述"], statement:["Source statement", "源码陈述"], value:["Evidence", "依据"] };
  const routeNames = { ByKnownAtomicFact:["Earlier fact", "更早的事实"], ByKnownForallFact:["Earlier universal fact", "更早的全称事实"], ByEquivalenceClass:["Stored equalities", "已建立的等式"], ByLocalIntroduction:["Local proof", "局部证明"], ByBuiltinRule:["Builtin rule", "内置规则"], ByBuiltinStrategy:["Structured derivation", "结构化推导"], ByBuiltinRewrite:["Checked rewrite", "经过检查的改写"], Success:["Established", "已建立"], Failed:["Not established", "尚未建立"] };
  function element(tag, className, content) { const node=document.createElement(tag); if(className)node.className=className; if(content!==undefined)node.textContent=String(content); return node; }
  function button(label, className, callback) { const node=element("button",className,label); node.type="button"; node.addEventListener("click",callback); return node; }
  function array(value) { return Array.isArray(value)?value:[]; }
  function humanize(value) { return String(value||"").replace(/([a-z])([A-Z])/g,"$1 $2").replace(/_/g," "); }
  function bytePositions(source) { const positions=new Map([[0,0]]); let bytes=0,units=0; for(const char of source){ const point=char.codePointAt(0); bytes+=point<128?1:point<2048?2:point<65536?3:4; units+=char.length; positions.set(bytes,units); } return positions; }

  Object.assign(copy.zh,{readingHelp:"阅读帮助",advancedHelp:"深入查看",records:"阅读记录",openFiles:"打开文件",openProject:"打开文件夹",recordExplanation:"阅读记录里保存了每句话怎样被检查、用到了哪些已知事实、又推出了什么。网页根据这些记录展示原文和说明。",recordFileExplanation:"这些记录保存成 JSON 文件，换一台电脑也能打开查看。JSON 是这种文件格式的名字。",book:"示例目录",hint:"悬浮对象、运算符或关键词查看说明，悬浮事实或行号查看依据；等式链中的每个等号可单独查看这一步的证明。灰色文字是本行推出的结果，悬浮或点击可查看全部结果。编辑时按住 Ctrl / ⌘ 点击，可跳转或固定说明。"});
  Object.assign(copy.en,{readingHelp:"Reading help",advancedHelp:"Explore further",records:"Reading records",openFiles:"Open a file",openProject:"Open a folder",recordExplanation:"Reading records save how each statement was checked, which known facts it used, and what it led to. This page uses those records to show the source and its explanations.",recordFileExplanation:"Records are saved as a JSON file, which you can open on another computer. JSON is the name of the file format.",book:"Examples",hint:"Hover an object, operation or keyword for help, or a fact or line number for proof. Each equals sign in a chain shows that step's own proof. Grey text shows inferred results; hover or click for all results. While editing, Ctrl / ⌘ + click follows a reference or keeps an explanation open."});

  // Authored language help. Token boundaries come from the real tokenizer;
  // builtin-set meanings are keyed by resolved identities, never source names.
  const syntaxHelp={
    prop:["定义命题：给出它的参数和成立条件。","Define a predicate with parameters and defining conditions."],
    abstract_prop:["声明抽象命题接口，不给出等价定义。","Declare a predicate interface without a defining equivalence."],
    have:["引入对象或函数，并检查声明要求。","Introduce an object or function and check its declaration requirements."],
    let:["引入当前上下文中的变量或绑定。","Introduce a variable or binding in the current context."],
    fn:["函数：描述参数和取值类型。","Function: describe parameter and result types."],
    forall:["全称量词：对于任意指定范围内的对象，所述条件均成立。","Universal quantifier: for every object in the specified domain, the stated conditions hold."],
    exist:["存在量词 ∃：存在满足条件的对象。","Existential quantifier ∃: an object satisfying the conditions exists."],
    "exist!":["唯一存在量词 ∃!：存在且仅存在一个满足条件的对象。","Unique existential quantifier ∃!: there exists exactly one object satisfying the conditions."],
    claim:["提出待证明的结论，并在块内给出证明。","State a goal and provide its proof in the block."],
    thm:["定义可供后文使用的定理。","Define a theorem for later use."],
    by:["指定证明或展开所采用的方法。","Specify a proof or expansion method."],
    def:["按定义检查或展开命题。","Check or unfold a predicate by its definition."],
    contra:["反证法：假设结论不成立并推出矛盾。","Proof by contradiction: negate the goal and derive a contradiction."],
    cases:["分情况证明。","Prove by cases."],
    case:["一个分支的条件与证明。","A case condition and its proof."],
    induc:["归纳证明。","Proof by induction."],
    strong_induc:["强归纳证明。","Proof by strong induction."],
    obtain:["从已知存在事实中取出见证对象。","Obtain witness objects from an existence fact."],
    witness:["提供满足存在性结论的具体见证。","Supply a concrete witness for an existence goal."],
    trust:["显式信任：此处内容作为假设接受。","Explicit trust: accept the content here as an assumption."],
    axiom:["声明公理，作为后续推理的前提。","Declare an axiom as a premise for subsequent reasoning."],
    struct:["定义带字段与约束的结构。","Define a structure with fields and constraints."],
    template:["定义可实例化的模板。","Define a template that can be instantiated."],
    set:["集合参数类型。","Set parameter type."],
    nonempty_set:["非空集合参数类型。","Nonempty-set parameter type."],
    finite_set:["有限集合参数类型。","Finite-set parameter type."],
    in:["属于 ∈：左边的对象属于右边的集合。","Membership ∈: the object on the left belongs to the set on the right."],
    and:["且 ∧：各条件同时成立。","Conjunction ∧: all conditions hold."],
    or:["或 ∨：至少一个条件成立。","Disjunction ∨: at least one condition holds."],
    not:["否定 ¬：后面的命题不成立。","Negation ¬: the following proposition does not hold."],
    "=>":["蕴含 ⇒：前面的条件推出后面的结论。","Implication ⇒: the preceding conditions imply the conclusion."],
    "<=>":["等价 ⇔：两边互相推出。","Equivalence ⇔: each side implies the other."],
    "?":["标出待证明的目标。","Mark a goal to be proved."],
    "$" :["命题应用的前缀。","Prefix for a predicate application."],
    "=":["相等。","Equality."],
    "!=":["不相等 ≠。","Inequality ≠."],
    "<=":["小于或等于 ≤。","Less than or equal to ≤."],
    ">=":["大于或等于 ≥。","Greater than or equal to ≥."],
    "<":["小于。","Less than."],
    ">":["大于。","Greater than."]
  };
  // Phrases are language help over adjacent lexer spans, not parsed mathematics.
  const syntaxPhrases={
    "by def":["用定义来证明。","Prove using a definition."],
    "by contra":["用反证法证明：假设结论不成立，再推出矛盾。","Prove by contradiction: negate the goal and derive a contradiction."],
    "by cases":["分情况证明，每一种情况都要成立。","Prove each case."],
    "by induc":["用数学归纳法证明。","Prove by mathematical induction."],
    "by strong_induc":["用强归纳法证明。","Prove by strong induction."],
    "by thm":["用已有定理证明。","Prove using a theorem."],
    "have fn":["定义函数，给出参数和函数值。","Define a function with its parameters and value."],
    "release thm":["使用已有定理，得到它给出的结论。","Apply a theorem and make its conclusions available."]
  };
  // BEGIN GENERATED LEXICAL KINDS
  const lexicalKinds=new Map([["keyword",["?","abstract_prop","algo","and","as","axiom","axiom_of_choice","by","case","cases","claim","contra","def","enumerate","eval","exist","exist!","expand","extension","fn","fn_extension","for","forall","from","have","import","impossible","induc","let","not","obtain","or","prop","reflexive","register","regularity_axiom","release","replacement_axiom","sketch","st","strategy","strong_induc","struct","symmetric","template","thm","transitive","trust","witness","zorn_lemma"]],["predicate",["$","bijective","coprime","dvd","fn_eq","fn_eq_in","has_curl_at","has_derivative_at","has_divergence_at","has_gradient_at","has_hessian_at","has_jacobian_at","has_laplacian_at","has_limit_at","has_limit_left","has_limit_neg_inf","has_limit_pos_inf","has_limit_right","has_multi_limit_at","has_partial_derivative_at","has_riemann_integral","has_scalar_differential_at","has_second_partial_derivative_at","has_seq_liminf","has_seq_limit","has_seq_limsup","has_total_derivative_at","has_vector_limit_at","in","injective","is_cart","is_choice_function_for","is_continuous","is_continuous_at","is_continuous_left","is_continuous_right","is_differentiable_at","is_finite_set","is_lipschitz","is_multi_continuous_at","is_multi_differentiable_at","is_nonempty_set","is_real_accumulation_at","is_real_accumulation_left","is_real_accumulation_right","is_real_bounded","is_real_bounded_above","is_real_bounded_below","is_real_lower_bound","is_real_upper_bound","is_riemann_integrable","is_seq_bounded","is_seq_bounded_above","is_seq_bounded_below","is_seq_cauchy","is_seq_convergent","is_seq_nondecreasing","is_seq_nonincreasing","is_seq_strictly_decreasing","is_seq_strictly_increasing","is_set","is_tuple","is_uniformly_continuous","is_vector_continuous_at","is_vector_differentiable_at","prime","proper_subset","proper_superset","subset","superset","surjective","∉"]],["function",["C_abs","abs","arccos","arccot","arcsin","arctan","cart","cart_dim","cart_n","ceil","closed_range","compose","conj","conjugate_transpose","cos","cosh","cot","coth","csc","csch","curl","derivative","det","diagonal_matrix","differential","divergence","euclidean_norm","exp","factorial","family_intersect","family_union","finite_seq","finite_set_max","finite_set_min","finite_set_product","finite_set_reduce","finite_set_size","finite_set_sum","floor","fn_lim","fn_preimage","fn_range","frobenius_norm","gcd","gradient_at","hessian","identity_matrix","img","index_cart","index_intersect","index_union","inf","inner_product","integral","intersect","jacobian","laplacian","lcm","lim","lim_left","lim_multi_at","lim_neg_inf","lim_pos_inf","lim_right","lim_vector_at","liminf","limsup","ln","log","matrix_add","matrix_adjugate","matrix_apply","matrix_cofactor","matrix_inverse","matrix_minor","matrix_mul","matrix_power","matrix_rank","matrix_scale","matrix_sub","max","min","outer_product","partial_derivative","power_set","preimage","preimage_set","product","proj","quot","range","re","reduce","scalar_differential","sec","sech","seq","set_diff","set_minus","sign","sin","sinh","sqrt","sum","sup","tan","tanh","trace","transpose","tuple","tuple_dim","union","zero_matrix"]],["type",["C","C*","N","N+","Q","Q*","Q+","Q-","R","R*","R+","R-","Z","Z*","Z+","Z-","finite_set","matrix","nonempty_set","obj","set","ℂ*","ℕ+","ℚ*","ℚ+","ℚ-","ℝ*","ℝ+","ℝ-","ℤ*","ℤ+","ℤ-"]],["constant",["e","i","pi"]],["operator",["!","!=","%","&","'*","'+","'-","'^","*","*'","+","-","->","/","<","<=","<=>","=","=>",">",">=","^","×","∘","∩","∪"]],["punctuation",["'","(",")",",",".","...",":","::",":::","[","\\","]","{","|","}"]]].flatMap(([kind,tokens])=>tokens.map(token=>[token,kind])));
  // END GENERATED LEXICAL KINDS
  const syntaxRoleHelp={
    keyword:["Litex 关键词。","Litex keyword."],
    predicate:["谓词：表达一个数学条件。","Predicate: express a mathematical condition."],
    function:["函数：把参数映射到一个值。","Function: map arguments to a value."],
    object:["对象","Object"],
    type:["类型或集合：描述对象的范围。","Type or set: describe a domain of objects."],
    theorem:["定理","Theorem"]
  };
  const standardSetHelp={
    N:["自然数集 ℕ（含 0）","Natural numbers ℕ (including 0)"],
    Z:["整数集 ℤ","Integers ℤ"], Q:["有理数集 ℚ","Rational numbers ℚ"],
    R:["实数集 ℝ","Real numbers ℝ"], C:["复数集 ℂ","Complex numbers ℂ"],
    "N+":["正自然数集","Positive natural numbers"],
    "Z+":["正整数集","Positive integers"], "Q+":["正有理数集","Positive rational numbers"], "R+":["正实数集","Positive real numbers"],
    "Z-":["负整数集","Negative integers"], "Q-":["负有理数集","Negative rational numbers"], "R-":["负实数集","Negative real numbers"],
    "Z*":["非零整数集","Nonzero integers"], "Q*":["非零有理数集","Nonzero rational numbers"], "R*":["非零实数集","Nonzero real numbers"], "C*":["非零复数集","Nonzero complex numbers"]
  };

  // Authored language-reference hints, not inferred expression types.
  // Domains follow verify_obj/scalar.rs and ast/obj.rs. Resolved user symbols
  // retain their own declaration help; token spelling never overrides identity.
  const builtinObjectHelp={
  "+": [
    "a + b",
    "a, b ∈ ℂ → ℂ",
    "加法。自然数、整数、有理数、实数也可以相加。",
    "Addition; also accepts natural, integer, rational and real operands.",
    "1 + 2 = 3"
  ],
  "-": [
    "a - b; -a",
    "a, b ∈ ℂ → ℂ",
    "减法；放在一个数前表示取相反数。结果未必仍是自然数。",
    "Subtraction; unary minus takes the additive inverse. The result need not be natural.",
    "2 - 5 = -3"
  ],
  "*": [
    "a * b",
    "a, b ∈ ℂ → ℂ",
    "乘法。",
    "Multiplication.",
    "3 * 4 = 12"
  ],
  "/": [
    "a / b",
    "a, b ∈ ℂ; b ≠ 0 → ℂ",
    "除法。除数必须不为零，结果不一定是整数。",
    "Division. The divisor must be nonzero; the result need not be an integer.",
    "3 / 2 = 1.5"
  ],
  "^": [
    "a ^ b",
    "(a ∈ ℂ, b ∈ ℕ) ∪ (a ∈ ℂ\\{0}, b ∈ ℤ)\n∪ (a > 0, a,b ∈ ℝ) ∪ (a ≥ 0, b > 0, a,b ∈ ℝ) → ℂ",
    "乘方。Litex 中 0^0 = 1；不支持一般的复数指数或负底数的非整数指数。",
    "Exponentiation. Litex sets 0^0 = 1; general complex exponents and noninteger powers of negative bases are unsupported.",
    "2 ^ 3 = 8"
  ],
  "%": [
    "a % b",
    "a, b ∈ ℤ; b ≠ 0 → ℕ",
    "欧几里得余数，满足 0 ≤ r < |b|。",
    "Euclidean remainder r, with 0 ≤ r < |b|.",
    "7 % 3 = 1"
  ],
  "sqrt": [
    "sqrt(x)",
    "x ∈ ℝ; x ≥ 0 → ℝ≥0",
    "非负平方根：结果的平方等于 x，且结果不小于零。",
    "The nonnegative square root: its square is x.",
    "sqrt(4) = 2"
  ],
  "abs": [
    "abs(x)",
    "x ∈ ℝ → ℝ≥0",
    "实数的绝对值，即它到零的距离。复数的模使用 C_abs。",
    "Real absolute value, the distance to zero. Use C_abs for complex modulus.",
    "abs(-3) = 3"
  ],
  "min": [
    "min(a, b)",
    "a, b ∈ ℝ → ℝ",
    "取两个实数中较小的一个。",
    "The smaller of two real numbers.",
    "min(2, 5) = 2"
  ],
  "max": [
    "max(a, b)",
    "a, b ∈ ℝ → ℝ",
    "取两个实数中较大的一个。",
    "The larger of two real numbers.",
    "max(2, 5) = 5"
  ],
  "floor": [
    "floor(x)",
    "x ∈ ℝ → ℤ",
    "向下取整：不大于 x 的最大整数。",
    "The greatest integer at most x.",
    "floor(2.5) = 2"
  ],
  "ceil": [
    "ceil(x)",
    "x ∈ ℝ → ℤ",
    "向上取整：不小于 x 的最小整数。",
    "The least integer at least x.",
    "ceil(2.5) = 3"
  ],
  "sign": [
    "sign(x)",
    "x ∈ ℝ → {-1, 0, 1}",
    "负数取 -1，零取 0，正数取 1。",
    "Returns -1 for negative x, 0 for zero, and 1 for positive x.",
    "sign(-3) = -1"
  ],
  "exp": [
    "exp(x)",
    "x ∈ ℝ → ℝ>0",
    "以自然常数 e 为底的指数函数 e^x。",
    "The real exponential e^x.",
    "exp(0) = 1"
  ],
  "ln": [
    "ln(x)",
    "x ∈ ℝ; x > 0 → ℝ",
    "自然对数，以 e 为底。",
    "The natural logarithm, with base e.",
    "ln(1) = 0"
  ],
  "log": [
    "log(b, x)",
    "b, x ∈ ℝ; b > 0, b ≠ 1, x > 0 → ℝ",
    "以 b 为底、x 的对数；第一个参数是底数。",
    "The logarithm of x to base b; the base is the first argument.",
    "log(2, 8) = 3"
  ],
  "factorial": [
    "factorial(n)",
    "n ∈ ℕ → ℕ>0",
    "阶乘：从 1 乘到 n，约定 0! = 1；也可写 n!。",
    "Factorial: the product from 1 to n, with 0! = 1. Also written n!.",
    "factorial(3) = 6"
  ],
  "gcd": [
    "gcd(a, b)",
    "a, b ∈ ℤ; (a ≠ 0 ∨ b ≠ 0) → ℕ>0",
    "最大公约数，取正值；不接受两个参数都为零。",
    "The positive greatest common divisor; the all-zero pair is excluded.",
    "gcd(12, 18) = 6"
  ],
  "lcm": [
    "lcm(a, b)",
    "a, b ∈ ℤ → ℕ",
    "最小非负公倍数；任一参数为零时结果为零。",
    "The least nonnegative common multiple, zero when either argument is zero.",
    "lcm(4, 6) = 12"
  ],
  "quot": [
    "quot(a, d)",
    "a ∈ ℤ, d ∈ ℕ>0 → ℤ",
    "欧几里得整商，满足 a = d * quot(a,d) + a % d。",
    "Euclidean integer quotient: a = d * quot(a,d) + a % d.",
    "quot(7, 3) = 2"
  ],
  "sin": [
    "sin(x)",
    "x ∈ ℝ → [-1, 1]",
    "正弦函数，角度使用弧度。",
    "Sine, with angles in radians.",
    "sin(0) = 0"
  ],
  "cos": [
    "cos(x)",
    "x ∈ ℝ → [-1, 1]",
    "余弦函数，角度使用弧度。",
    "Cosine, with angles in radians.",
    "cos(0) = 1"
  ],
  "tan": [
    "tan(x)",
    "x ∈ ℝ; cos(x) ≠ 0 → ℝ",
    "正切函数 sin(x)/cos(x)，角度使用弧度。",
    "Tangent sin(x)/cos(x), with angles in radians.",
    "tan(0) = 0"
  ],
  "cot": [
    "cot(x)",
    "x ∈ ℝ; sin(x) ≠ 0 → ℝ",
    "余切函数 cos(x)/sin(x)，角度使用弧度。",
    "Cotangent cos(x)/sin(x), with angles in radians.",
    "cot(pi / 4) = 1"
  ],
  "arcsin": [
    "arcsin(x)",
    "x ∈ [-1, 1] → [-π/2, π/2]",
    "反正弦，结果是主值区间中的弧度。",
    "Principal inverse sine, returned in radians.",
    "arcsin(0) = 0"
  ],
  "arccos": [
    "arccos(x)",
    "x ∈ [-1, 1] → [0, π]",
    "反余弦，结果是主值区间中的弧度。",
    "Principal inverse cosine, returned in radians.",
    "arccos(1) = 0"
  ],
  "arctan": [
    "arctan(x)",
    "x ∈ ℝ → (-π/2, π/2)",
    "反正切，结果是主值区间中的弧度。",
    "Principal inverse tangent, returned in radians.",
    "arctan(0) = 0"
  ],
  "re": [
    "re(z)",
    "z ∈ ℂ → ℝ",
    "复数的实部。",
    "The real part of a complex number.",
    "re(i) = 0"
  ],
  "img": [
    "img(z)",
    "z ∈ ℂ → ℝ",
    "复数的虚部，结果是实数。",
    "The imaginary part of a complex number, returned as a real number.",
    "img(i) = 1"
  ],
  "conj": [
    "conj(z)",
    "z ∈ ℂ → ℂ",
    "复共轭：a + b*i 变成 a - b*i。",
    "Complex conjugate: a + b*i becomes a - b*i.",
    "conj(i) = -i"
  ],
  "C_abs": [
    "C_abs(z)",
    "z ∈ ℂ → ℝ≥0",
    "复数的模，即复平面上到原点的距离。",
    "Complex modulus, the distance to the origin in the complex plane.",
    "C_abs(i) = 1"
  ]
};

  // Authored reference cards describe builtin contracts, not the inferred type
  // of a hovered expression. Set-kind inputs are never a universal set domain.
  const setOperatorHelp={
    union:["union(A, B)","A、B 是集合；结果是集合 A ∪ B。","A and B are sets; the result is the set A ∪ B.","并集：包含属于 A 或属于 B 的元素。","Union: elements belonging to A or B.","1 $in union({1}, {2})"],
    intersect:["intersect(A, B)","A、B 是集合；结果是集合 A ∩ B。","A and B are sets; the result is the set A ∩ B.","交集：只包含同时属于 A 和 B 的元素。","Intersection: elements belonging to both A and B.","2 $in intersect({1, 2}, {2, 3})"],
    set_minus:["set_minus(A, B)","A、B 是集合；结果是 A 的子集。","A and B are sets; the result is a subset of A.","差集：包含属于 A 但不属于 B 的元素。","Relative complement: elements in A but not in B.","1 $in set_minus({1, 2}, {2})"],
    power_set:["power_set(A)","A 是集合；结果是由 A 的所有子集组成的集合。","A is a set; the result is the set of all subsets of A.","幂集：它的每个元素都是 A 的一个子集。","Power set: each of its elements is a subset of A.","power_set({1}) = {{}, {1}}"],
    family_union:["family_union(F)","F 是集合族（每个元素都是集合）；结果是集合。","F is a set of sets; the result is a set.","集合族的并：包含至少属于 F 中一个集合的元素。","Union of a family: elements in at least one member of F.","family_union({{1, 2}}) = {1, 2}"],
    family_intersect:["family_intersect(F)","F 是非空集合族（每个元素都是集合）；结果是集合。","F is a nonempty set of sets; the result is a set.","集合族的交：包含属于 F 中每一个集合的元素。","Intersection of a family: elements in every member of F.","$is_set(family_intersect({{1}}))"],
    index_union:["index_union(I, X, A)","I 是非空集合，X 是集合；A ∈ fn(k I) power_set(X)；结果是 X 的子集。","I is a nonempty set and X is a set; A ∈ fn(k I) power_set(X); the result is a subset of X.","指标并集：把每个 k ∈ I 对应的集合 A(k) 合并。","Indexed union: combine A(k) for every k ∈ I.","let U = index_union({1}, N, fn(k {1}) power_set(N) {{2}})"],
    index_intersect:["index_intersect(I, X, A)","I 是非空集合，X 是集合；A ∈ fn(k I) power_set(X)；结果是 X 的子集。","I is a nonempty set and X is a set; A ∈ fn(k I) power_set(X); the result is a subset of X.","指标交集：取 X 中属于每个 A(k) 的元素；Litex 要求 I 非空。","Indexed intersection: elements of X in every A(k); Litex requires nonempty I.","let J = index_intersect({1}, N, fn(k {1}) power_set(N) {{2}})"]
  };
  // Alternate builtin spellings share documentation only, never public APIs.
  setOperatorHelp.set_diff=setOperatorHelp.set_minus;
  setOperatorHelp["∪"]=setOperatorHelp.union;setOperatorHelp["∩"]=setOperatorHelp.intersect;
  Object.assign(builtinObjectHelp,{
    arccot:["arccot(x)","x ∈ ℝ → (0, π)","反余切，取 (0, π) 中的主值，单位为弧度。","Principal inverse cotangent in (0, π), in radians.","arccot(0) = pi / 2"],
    sec:["sec(x)","x ∈ ℝ; cos(x) ≠ 0 → ℝ","正割，等于 1 / cos(x)。","Secant, equal to 1 / cos(x).","sec(0) = 1"],
    csc:["csc(x)","x ∈ ℝ; sin(x) ≠ 0 → ℝ","余割，等于 1 / sin(x)。","Cosecant, equal to 1 / sin(x).","csc(pi / 2) = 1"],
    sinh:["sinh(x)","x ∈ ℝ → ℝ","双曲正弦，等于 (exp(x) - exp(-x)) / 2。","Hyperbolic sine: (exp(x) - exp(-x)) / 2.","sinh(0) = 0"],
    cosh:["cosh(x)","x ∈ ℝ → [1, ∞)","双曲余弦，等于 (exp(x) + exp(-x)) / 2。","Hyperbolic cosine: (exp(x) + exp(-x)) / 2.","cosh(0) = 1"],
    tanh:["tanh(x)","x ∈ ℝ → (-1, 1)","双曲正切，等于 sinh(x) / cosh(x)。","Hyperbolic tangent: sinh(x) / cosh(x).","tanh(0) = 0"],
    coth:["coth(x)","x ∈ ℝ; x ≠ 0 → ℝ","双曲余切，等于 cosh(x) / sinh(x)；零处无定义。","Hyperbolic cotangent: cosh(x) / sinh(x); undefined at zero.","coth(1) = cosh(1) / sinh(1)"],
    sech:["sech(x)","x ∈ ℝ → (0, 1]","双曲正割，等于 1 / cosh(x)。","Hyperbolic secant: 1 / cosh(x).","sech(0) = 1"],
    csch:["csch(x)","x ∈ ℝ; x ≠ 0 → ℝ","双曲余割，等于 1 / sinh(x)；零处无定义。","Hyperbolic cosecant: 1 / sinh(x); undefined at zero.","csch(1) = 1 / sinh(1)"]
  });
  const keywordReference={
    prop:{
      syntax:"prop name(x A):\n    condition",
      zh:["谓词定义","定义带类型参数的谓词。","对声明域内的参数，谓词成立等价于定义体中的全部条件同时成立。定义本身不证明任何具体实例。"],
      en:["Predicate definition","Define a predicate with typed parameters.","For arguments in the declared domains, the predicate holds exactly when all conditions in its definition hold. The definition proves no particular instance."],
      example:"prop nonnegative(x R):\n    x >= 0\n\nby def $nonnegative(3)",
      walkthrough:{
        zh:[
          ["参数类型","x 是形式参数，R 将它的取值范围限定为实数集。实例中的实参必须属于该集合。"],
          ["谓词","nonnegative(x) 是关于实数 x 的命题，表示 x 非负；它不是返回一个数值的函数。"],
          ["定义条件","本例的定义体只有 x >= 0 一个条件。因此，对每个实数 x，有以下等价关系；若定义体有多个条件，则要求它们同时成立。","\\forall x\\in\\mathbb{R},\\quad \\operatorname{nonnegative}(x)\\iff x\\ge 0","∀ x ∈ ℝ: nonnegative(x) ⇔ x ≥ 0"],
          ["定义与实例","这条定义没有断言所有实数都非负，也没有证明某个具体实数非负。例如，nonnegative(-2) 不成立，因为 -2 < 0。"],
          ["按定义证明","最后一行 by def $nonnegative(3) 将实参 3 代入 x。验证 3 ∈ ℝ 和 3 ≥ 0 后，建立事实 $nonnegative(3)，后续证明可以引用这一事实。"]
        ],
        en:[
          ["Typed parameter","x is a formal parameter whose domain R is the set of real numbers. An actual argument must belong to this set."],
          ["Predicate","nonnegative(x) is a proposition about a real number x: x is nonnegative. It is not a function returning a numerical value."],
          ["Defining condition","The definition has one condition, x >= 0. Thus the following equivalence holds for every real x. With several defining conditions, all must hold.","\\forall x\\in\\mathbb{R},\\quad \\operatorname{nonnegative}(x)\\iff x\\ge 0","∀ x ∈ ℝ: nonnegative(x) ⇔ x ≥ 0"],
          ["Definition and instance","This declaration neither asserts that every real number is nonnegative nor proves a particular real number nonnegative. For example, nonnegative(-2) does not hold because -2 < 0."],
          ["Proof by definition","The last line, by def $nonnegative(3), substitutes the actual argument 3 for x. Verifying 3 ∈ ℝ and 3 ≥ 0 establishes $nonnegative(3), which later proofs may cite."]
        ]
      }
    },
    "by def":{
      syntax:"by def $name(arguments)",
      zh:["按定义证明","按谓词定义证明一个实例。","将实参代入定义，在参数类型要求满足的前提下证明全部定义条件；成功后得到对应的谓词事实。"],
      en:["Proof by definition","Prove an instance using its predicate definition.","Substitute the actual arguments, establish their declared types and prove every defining condition. Success establishes the corresponding predicate fact."],
      example:"prop nonnegative(x R):\n    x >= 0\n\nby def $nonnegative(3)",
      walkthrough:{
        zh:[
          ["代入实参","nonnegative 的形式参数是 x，本次实参是 3。代入后，定义体的 x >= 0 成为 3 >= 0。"],
          ["验证类型与条件","声明要求 x ∈ ℝ，因此先验证 3 ∈ ℝ；随后验证唯一的定义条件 3 ≥ 0。若定义有多个条件，每个条件都需要成立。"],
          ["得到实例事实","这些要求均得到验证后，by def 建立 $nonnegative(3)，供后续证明引用。它证明的是这个实例，不是所有实数都非负。"]
        ],
        en:[
          ["Substitute the argument","The formal parameter of nonnegative is x; the actual argument is 3. Substitution turns the defining condition x >= 0 into 3 >= 0."],
          ["Verify the type and condition","The declaration requires x ∈ ℝ, so verify 3 ∈ ℝ and then the single defining condition 3 ≥ 0. If the definition contains several conditions, every condition must hold."],
          ["Establish the instance","Once these requirements are established, by def establishes $nonnegative(3) for later citation. It proves this instance, not that every real number is nonnegative."]
        ]
      }
    },
    forall:{syntax:"forall x A:\n    condition",zh:["全称量词","对于任意指定范围内的对象，所述条件均成立。","在块内 x 是任意一个 A 中的对象。证明不能依赖 x 的某个特殊取值；x 的这个绑定只在本量词范围内有效。"],en:["Universal quantifier","For every object in the specified domain, the stated conditions hold.","Inside the block, x is an arbitrary member of A, not a chosen special value. Its binding is scoped to this quantifier."],example:"forall x R:\n    x = x"},
    claim:{syntax:"claim:\n    ? goal\n    proof",zh:["声明并证明","把要证明的目标和它的证明放在同一个块里。","? 标出目标。块内可以补充中间步骤；只有目标被证明后，承诺的结论才交给后文使用。"],en:["State and prove","Place a goal and its proof in one block.","? marks the goal. Intermediate steps can be added inside; the promised conclusion becomes available after it is established."],example:"claim:\n    ? 1 = 1\n    1 = 1"},
    "release thm":{
      syntax:"release thm name(arguments)",
      zh:["定理实例化","应用定理，将其实例化结论引入当前证明上下文。","将实参代入定理的形式参数，验证参数域与实例化后的全部前提，再建立定理给出的全部结论。该指令应用已有定理，不定义新定理，也不将其前提作为假设直接接受。"],
      en:["Theorem instantiation","Apply a theorem and introduce its instantiated conclusions into the current proof context.","Substitute actual arguments for formal parameters, verify their domains and every instantiated premise, then establish all conclusions of the theorem. This applies an existing theorem; it neither defines a theorem nor assumes its premises."],
      example:"$prime(2)\n$dvd(6 ^ 2, 2)\nrelease thm prime_divides_power(6, 2, 2)\n$dvd(6, 2)",
      walkthrough:{
        zh:[
          ["定理内容","prime_divides_power(a, k, p) 表示：p 是素数、k 是正自然数且 p 整除 aᵏ 时，p 整除 a。"],
          ["参数与前提","本例代入 a = 6、k = 2、p = 2。相应参数域为 a ∈ ℤ、p ∈ ℕ+、k ∈ ℕ+；两条事实给出 2 为素数，以及 2 整除 6²。"],
          ["实例化结论","release thm 在验证这些要求后建立 $dvd(6, 2)，即 2 整除 6。最后一行引用这个结论。结论来自定理及已验证的前提，而不是从定理名称猜测得到。"]
        ],
        en:[
          ["The theorem","prime_divides_power(a, k, p) states that if p is prime, k is a positive natural number and p divides aᵏ, then p divides a."],
          ["Arguments and premises","Here a = 6, k = 2 and p = 2, with a ∈ ℤ, p ∈ ℕ+ and k ∈ ℕ+. The first two facts establish that 2 is prime and divides 6²."],
          ["Instantiated conclusion","After checking these requirements, release thm establishes $dvd(6, 2): 2 divides 6. The last line cites this conclusion. The result follows from the theorem and verified premises, not from interpreting its name."]
        ]
      }
    },
    "have fn":{syntax:"have fn f(x A) B = expression",zh:["定义函数","给出参数的范围，以及每个参数对应的函数值。","输入 x 属于 A；表达式的值必须属于 B。以后可以用 f(x) 引用这个值。"],en:["Function definition","Specify an input domain and the value assigned to each argument.","Input x belongs to A and the expression must belong to B. Later expressions may refer to this value as f(x)."],example:"have fn double(x R) R = 2 * x"},
    "by contra":{syntax:"by contra:\n    ? goal\n    proof",zh:["反证法","假设目标不成立，再推出矛盾，从而证明目标。","否定目标得到的假设只供当前证明使用。必须真正推出矛盾，不能只重复目标。"],en:["Proof by contradiction","Assume the negation of the goal and derive a contradiction.","The negated goal is local to this proof. A contradiction must be established, rather than merely repeating the goal."],example:"by contra:\n    ? not 1 = 2\n    impossible 1 = 2"}
  };

  // BEGIN GENERATED LANGUAGE REFERENCE
  const languageReference={"entries":{"let":{"kind":{"zh":"语句","en":"Statement"},"syntax":"let a = expression","summary":{"zh":"将名称绑定到给定的数学对象。","en":"Bind a name to a specified mathematical object."},"notes":{"zh":"先检查右侧表达式有定义；名称随后表示这个对象。绑定与引入任意参数不同。","en":"The right-hand expression must be well-defined. The name denotes that object, rather than an arbitrary parameter."}},"prop":{"kind":{"zh":"谓词定义","en":"Predicate definition"},"syntax":"prop P(x A):\n    condition","summary":{"zh":"定义带类型参数的谓词及其等价条件。","en":"Define a predicate with typed parameters and equivalent defining conditions."},"notes":{"zh":"对声明域内的参数，P 成立等价于定义体中的全部条件同时成立。定义本身不证明某个具体实例。","en":"For arguments in the declared domains, P holds exactly when all defining conditions hold. A definition does not prove a particular instance."}},"abstract_prop":{"kind":{"zh":"抽象谓词","en":"Abstract predicate"},"syntax":"abstract_prop P(x A)","summary":{"zh":"声明谓词的参数接口，不给出等价定义。","en":"Declare a predicate’s parameter interface without a defining equivalence."},"notes":{"zh":"后续事实或定理可使用 P；这个声明不使任何 P 的实例自动成立。","en":"Later facts and theorems may use P, but the declaration establishes no instance of P."}},"thm":{"kind":{"zh":"定理","en":"Theorem"},"syntax":"thm name:\n    ? fact\n    proof","summary":{"zh":"证明并命名一个可复用的数学结论。","en":"Prove and name a reusable mathematical result."},"notes":{"zh":"? 标出定理目标；证明使用声明的参数与前提。后续应用时须验证实例化后的要求。","en":"The ? marker identifies the goal. The proof uses its declared parameters and premises; later applications must establish the instantiated requirements."}},"axiom":{"kind":{"zh":"公理声明","en":"Axiom declaration"},"syntax":"axiom name:\n    ? forall ...","summary":{"zh":"命名一个作为基础假设接受的全称命题。","en":"Name a universal proposition accepted as a foundational assumption."},"notes":{"zh":"检查接口和表达式合法性，不提供该公理的证明；依赖它的结论仍依赖该假设。","en":"Its interface and formation are checked, but no proof of the axiom is supplied. Conclusions using it retain that assumption dependency."}},"strategy":{"kind":{"zh":"证明策略","en":"Proof strategy"},"syntax":"strategy name:\n    ? forall ...\n    proof","summary":{"zh":"定义一个可复用的证明策略。","en":"Define a reusable proof strategy."},"notes":{"zh":"策略根据目标匹配参数，并验证实例化前提；匹配成功不能替代前提证明。","en":"A strategy matches parameters against a goal and verifies the instantiated premises. A successful match does not replace the premise proofs."}},"struct":{"kind":{"zh":"结构定义","en":"Structure definition"},"syntax":"struct Name:\n    field A","summary":{"zh":"用带类型的字段及约束定义结构。","en":"Define a structure through typed fields and constraints."},"notes":{"zh":"字段可以依赖此前字段；结构对象须满足相应字段域及结构约束。访问字段不会凭空建立额外性质。","en":"Fields may depend on earlier fields. A structure value must satisfy the field domains and constraints; field access establishes no additional property by itself."}},"template":{"kind":{"zh":"模板定义","en":"Template definition"},"syntax":"template<S set>:\n    definition","summary":{"zh":"以类型化参数定义一族可实例化的数学接口。","en":"Define a family of mathematical interfaces parameterized by typed arguments."},"notes":{"zh":"实例化时检查参数条件，再使用相应定义；模板参数与实例定义内部的局部参数具有不同作用域。","en":"Instantiation checks the template arguments before using the resulting definition. Template parameters and local binders have distinct scopes."}},"by thm":{"kind":{"zh":"应用定理","en":"Theorem application"},"syntax":"by thm theorem(arguments) => fact","summary":{"zh":"应用已有定理，选择并建立其中一个原子结论。","en":"Apply an existing theorem and establish one selected atomic conclusion."},"notes":{"zh":"须检查实参、实例化前提和结论的对应关系。所选结论必须由该次定理应用提供；不能将任意目标附在定理名称之后。","en":"Check the arguments, instantiated premises and correspondence with the selected conclusion. The conclusion must be supplied by that application; an arbitrary goal cannot be appended to a theorem name."}},"by def":{"kind":{"zh":"按定义证明","en":"Proof by definition"},"syntax":"by def $P(arguments)","summary":{"zh":"按谓词的定义证明一个具体实例。","en":"Prove a concrete predicate instance by its definition."},"notes":{"zh":"将实参代入定义，验证参数要求及全部定义条件，再建立实例事实。实例的证明与谓词声明是不同步骤。","en":"Substitute the arguments, verify their requirements and all defining conditions, then establish the instance. This is distinct from declaring the predicate."}},"by contra":{"kind":{"zh":"反证法","en":"Proof by contradiction"},"syntax":"by contra:\n    ? fact\n    proof","summary":{"zh":"假设目标的否定，并由矛盾证明原目标。","en":"Prove a goal by deriving a contradiction under its negation."},"notes":{"zh":"须实际建立互相矛盾的事实。反证假设不会作为无条件结论交给后文。","en":"Incompatible facts must actually be established. The temporary negation is not exported as an unconditional conclusion."}},"by cases":{"kind":{"zh":"分类证明","en":"Proof by cases"},"syntax":"by cases:\n    ? fact\n    case condition:\n        proof","summary":{"zh":"通过穷尽可能性的分类讨论证明结论。","en":"Prove conclusions by an exhaustive case split."},"notes":{"zh":"每种情况中都须证明所需结论，或证明该情况不可能发生；分支假设只在对应分支有效。","en":"Each case must establish the requested conclusions or be shown impossible. A branch assumption is local to its branch."}},"by enumerate":{"kind":{"zh":"有限枚举证明","en":"Finite enumeration proof"},"syntax":"by enumerate finite_set:\n    ? forall x S => condition\n    proof","summary":{"zh":"逐个验证有限集合中的对象，证明一个全称命题。","en":"Prove a universal statement by checking each element of a finite set."},"notes":{"zh":"集合必须可按该指令支持的方式枚举；验证一个例子不能替代检查全部元素。","en":"The carrier must be enumerable by this command. Checking one example does not establish every case."}},"by for":{"kind":{"zh":"范围枚举证明","en":"Range enumeration proof"},"syntax":"by for:\n    ? forall i range(a, b) => condition\n    proof","summary":{"zh":"通过有限范围的逐项检查证明全称结论。","en":"Prove a universal conclusion by checking a finite range."},"notes":{"zh":"按指令支持的范围或笛卡尔积枚举所有参数组合，并对每组检查结论。","en":"Enumerate all parameter combinations in the supported ranges or Cartesian products and verify the conclusion in each case."}},"by induc":{"kind":{"zh":"数学归纳法","en":"Mathematical induction"},"syntax":"by induc n from k:\n    ? fact\n    proof","summary":{"zh":"用基础情形与归纳步骤证明整数指标上的结论。","en":"Prove an integer-indexed conclusion using a base case and induction step."},"notes":{"zh":"基础情形验证起点；归纳步骤在相应归纳假设下证明下一指标的结论。起点和参数域也须满足要求。","en":"The base case establishes the starting point. The step proves the next case under the corresponding induction hypothesis. The start and parameter domain must also satisfy their requirements."}},"by strong_induc":{"kind":{"zh":"强归纳法","en":"Strong induction"},"syntax":"by strong_induc n from k:\n    ? fact\n    proof","summary":{"zh":"用所有较小指标的结论作归纳假设。","en":"Use conclusions at all smaller admissible indices as the induction hypothesis."},"notes":{"zh":"仍须验证基础情形；强归纳允许在归纳步骤中使用起点之后且小于当前指标的已假定结论。","en":"A base case is still required. The induction step may use assumed conclusions from the starting point up to, but not including, the current index."}},"by extension":{"kind":{"zh":"集合外延证明","en":"Set extensionality"},"syntax":"by extension A = B","summary":{"zh":"用集合的相互包含证明集合相等。","en":"Prove equality of sets by mutual inclusion."},"notes":{"zh":"分别验证 A ⊆ B 和 B ⊆ A。仅证明其中一个方向，通常只能得到包含关系。","en":"Establish A ⊆ B and B ⊆ A separately. A single direction generally establishes only inclusion."}},"by fn_extension":{"kind":{"zh":"函数外延证明","en":"Function extensionality"},"syntax":"by fn_extension f = g","summary":{"zh":"在共同的函数接口上用逐点相等证明函数相等。","en":"Prove equality of functions by pointwise equality on a common interface."},"notes":{"zh":"须满足函数域与接口匹配要求，再证明每个合法输入上的值相同；有限个样本相等通常不够。","en":"The function domains and interfaces must match, and values must agree at every admissible input. Agreement at finitely many sample inputs generally does not suffice."}},"release thm":{"kind":{"zh":"定理实例化","en":"Theorem instantiation"},"syntax":"release thm theorem(arguments)","summary":{"zh":"应用定理，并引入该次实例化的全部结论。","en":"Apply a theorem and introduce all conclusions of that instantiation."},"notes":{"zh":"先验证参数域、函数参数要求和实例化前提。定理前提不是由这条语句直接假定的。","en":"First verify parameter domains, function-argument requirements and instantiated premises. This command does not assume the theorem’s premises."}},"register transitive":{"kind":{"zh":"性质登记","en":"Property registration"},"syntax":"register transitive: ...","summary":{"zh":"登记一个二元谓词的传递性规则。","en":"Register the transitivity law of a binary predicate."},"notes":{"zh":"规则形状为 P(a,b) ∧ P(b,c) ⇒ P(a,c)，变量须满足所登记接口的类型和适用条件。 登记前须验证相应的全称规律。","en":"The law has shape P(a,b) ∧ P(b,c) ⇒ P(a,c), subject to the registered interface’s types and applicability conditions. The corresponding universal law must be verified before registration."}},"register symmetric":{"kind":{"zh":"性质登记","en":"Property registration"},"syntax":"register symmetric: ...","summary":{"zh":"登记一个二元谓词的对称性规则。","en":"Register the symmetry law of a binary predicate."},"notes":{"zh":"规则形状为 P(a,b) ⇒ P(b,a)，变量须满足所登记接口的类型和适用条件。 登记前须验证相应的全称规律。","en":"The law has shape P(a,b) ⇒ P(b,a), subject to the registered interface’s types and applicability conditions. The corresponding universal law must be verified before registration."}},"register reflexive":{"kind":{"zh":"性质登记","en":"Property registration"},"syntax":"register reflexive: ...","summary":{"zh":"登记一个二元谓词的自反性规则。","en":"Register the reflexivity law of a binary predicate."},"notes":{"zh":"规则形状为 P(a,a)，变量须满足所登记接口的类型和适用条件。 登记前须验证相应的全称规律。","en":"The law has shape P(a,a), subject to the registered interface’s types and applicability conditions. The corresponding universal law must be verified before registration."}},"claim":{"kind":{"zh":"局部断言","en":"Local claim"},"syntax":"claim:\n    ? fact\n    proof","summary":{"zh":"在局部证明中建立一个指定结论。","en":"Establish a specified conclusion in a local proof."},"notes":{"zh":"块内可引入辅助步骤；只有被证明的目标交给外层使用，局部辅助声明不会全部逸出。","en":"The block may introduce auxiliary steps. The established target is exported, not every local helper declaration."}},"sketch":{"kind":{"zh":"证明草稿","en":"Proof sketch"},"syntax":"sketch:\n    proof","summary":{"zh":"检查一个局部证明草稿，其结果不向外发布。","en":"Check a local proof sketch without exporting its results."},"notes":{"zh":"草稿中的数学语句仍须通过相应检查；它不等于 trust。","en":"Mathematical statements in the sketch remain subject to checking; a sketch is not a trust boundary."}},"trust":{"kind":{"zh":"显式信任","en":"Explicit trust"},"syntax":"trust:\n    fact","summary":{"zh":"将列出的事实作为显式假设接受。","en":"Accept the listed facts as explicit assumptions."},"notes":{"zh":"仍检查表达式有定义，但跳过事实的真值证明。严格模式拒绝此类边界；依赖关系应标明信任来源。","en":"Formation is still checked, but truth proofs are skipped. Strict mode rejects this boundary; dependent results retain its trust provenance."}},"trust have":{"kind":{"zh":"带信任的对象声明","en":"Object declaration with trust"},"syntax":"trust have x A:\n    condition","summary":{"zh":"引入对象，并显式信任列出的性质。","en":"Introduce objects and explicitly trust the listed properties."},"notes":{"zh":"这不是由已有存在性证明得到的构造。仍须检查表达式有定义，严格模式拒绝此类边界。","en":"This is not a construction justified by established existence. Formation remains checked and strict mode rejects this boundary."}},"eval":{"kind":{"zh":"精确求值","en":"Exact evaluation"},"syntax":"eval expression","summary":{"zh":"精确求值，并保留原表达式与结果的等式。","en":"Evaluate an expression exactly and retain its equality with the result."},"notes":{"zh":"表达式必须有定义且受当前求值器支持；这不等于对任意函数执行数值近似。","en":"The expression must be well-defined and supported by the evaluator. This is not unrestricted numerical approximation of an arbitrary function."}},"have fn":{"kind":{"zh":"函数定义","en":"Function definition"},"syntax":"have fn f(x A: condition) B = expression","summary":{"zh":"以一个表达式定义函数值。","en":"Define function values by an expression."},"notes":{"zh":"参数须满足声明域和条件；函数体在这些条件下须有定义且属于 B。应用函数时按绑定变量的身份代入实参。","en":"Arguments must satisfy the declared domains and guards. Under those conditions, the body must be well-defined and belong to B. Application substitutes arguments by bound-variable identity."}},"have":{"kind":{"zh":"对象声明","en":"Object declaration"},"syntax":"have x A; have x A = expression","summary":{"zh":"引入具有指定类型的对象，或通过等式及存在性定义对象。","en":"Introduce typed objects, or define objects by equality or established existence."},"notes":{"zh":"具体要求由声明形式决定：任意元素、指定值、满足条件的见证和函数定义各有不同的验证义务。","en":"The declaration form determines the obligations: an arbitrary element, a specified value, a constrained witness and a function definition are distinct constructions."}},"obtain":{"kind":{"zh":"提取见证","en":"Witness extraction"},"syntax":"obtain x from exist x A st {condition}","summary":{"zh":"从已有存在性结论中引入见证对象。","en":"Introduce witnesses from an established existence conclusion."},"notes":{"zh":"对象的域和性质来自所引用的存在命题，而非新增的无条件假设。","en":"The object’s domain and properties come from the cited existential statement, not from a new unconditional assumption."}},"not":{"kind":{"zh":"逻辑否定","en":"Logical negation"},"syntax":"not P","summary":{"zh":"断言命题 P 不成立。","en":"Assert that proposition P does not hold."},"notes":{"zh":"未能证明 P 不等于证明 not P；否定也需要自己的数学依据。","en":"Failure to prove P is not a proof of not P. Negation requires mathematical evidence of its own."}},"in":{"kind":{"zh":"数学关系","en":"Mathematical relation"},"syntax":"x $in A","summary":{"zh":"x 是集合 A 的元素。","en":"x is an element of A."},"notes":{"zh":"数学记号为 x ∈ A。x 是一个对象，A 是一个集合。归属关系与集合包含关系不同。","en":"Mathematical notation: x ∈ A. x is an object and A is a set. Membership differs from set inclusion."}},"subset":{"kind":{"zh":"数学关系","en":"Mathematical relation"},"syntax":"A $subset B","summary":{"zh":"A 的每个元素都属于 B。","en":"Every element of A belongs to B."},"notes":{"zh":"∀ x ∈ A, x ∈ B。允许 A = B。","en":"∀ x ∈ A, x ∈ B. Equality A = B is allowed."}},"superset":{"kind":{"zh":"数学关系","en":"Mathematical relation"},"syntax":"A $superset B","summary":{"zh":"B 的每个元素都属于 A。","en":"Every element of B belongs to A."},"notes":{"zh":"A ⊇ B 等价于 B ⊆ A。","en":"A ⊇ B is equivalent to B ⊆ A."}},"proper_subset":{"kind":{"zh":"数学关系","en":"Mathematical relation"},"syntax":"A $proper_subset B","summary":{"zh":"A 包含于 B，且 A 与 B 不相等。","en":"A is included in B and A differs from B."},"notes":{"zh":"A ⊊ B ⇔ A ⊆ B ∧ A ≠ B。","en":"A ⊊ B ⇔ A ⊆ B ∧ A ≠ B."}},"proper_superset":{"kind":{"zh":"数学关系","en":"Mathematical relation"},"syntax":"A $proper_superset B","summary":{"zh":"A 包含 B，且 A 与 B 不相等。","en":"A includes B and A differs from B."},"notes":{"zh":"A ⊋ B ⇔ B ⊆ A ∧ A ≠ B。","en":"A ⊋ B ⇔ B ⊆ A ∧ A ≠ B."}},"is_set":{"kind":{"zh":"数学关系","en":"Mathematical relation"},"syntax":"$is_set(A)","summary":{"zh":"A 是集合。","en":"A is a set."},"notes":{"zh":"这是对象的种类性质，不是 A 属于一个“所有集合的集合”的声明。","en":"This is a kind property, not membership in a supposed set of all sets."}},"is_nonempty_set":{"kind":{"zh":"数学关系","en":"Mathematical relation"},"syntax":"$is_nonempty_set(A)","summary":{"zh":"集合 A 至少有一个元素。","en":"The set A has at least one element."},"notes":{"zh":"∃ x ∈ A。证明非空可以给出一个经过验证的元素见证。","en":"∃ x ∈ A. Nonemptiness can be established by a verified element witness."}},"is_finite_set":{"kind":{"zh":"数学关系","en":"Mathematical relation"},"syntax":"$is_finite_set(A)","summary":{"zh":"A 是有限集合。","en":"A is a finite set."},"notes":{"zh":"有限性与非空性不同；空集也是有限集合。","en":"Finiteness differs from nonemptiness; the empty set is finite."}},"dvd":{"kind":{"zh":"数学关系","en":"Mathematical relation"},"syntax":"$dvd(a, d)","summary":{"zh":"整数 d 整除整数 a。","en":"The integer d divides the integer a."},"notes":{"zh":"参数域为 a ∈ ℤ、d ∈ ℤ 且 d ≠ 0；参数顺序是被整除数 a 在前、除数 d 在后。整除条件为 ∃ k ∈ ℤ, a = k·d。","en":"The domains are a ∈ ℤ and nonzero d ∈ ℤ. The dividend a comes first and divisor d second. Divisibility means ∃ k ∈ ℤ, a = k·d."}},"prime":{"kind":{"zh":"数学关系","en":"Mathematical relation"},"syntax":"$prime(p)","summary":{"zh":"自然数 p 是素数。","en":"The natural number p is prime."},"notes":{"zh":"参数域为 p ∈ ℕ。素数满足 p > 1，且正因子只有 1 与 p。","en":"The argument domain is p ∈ ℕ. A prime satisfies p > 1 and has only the positive divisors 1 and p."}},"coprime":{"kind":{"zh":"数学关系","en":"Mathematical relation"},"syntax":"$coprime(a, b)","summary":{"zh":"自然数 a 与 b 互素。","en":"The natural numbers a and b are coprime."},"notes":{"zh":"当前接口的参数域为 a,b ∈ ℕ；互素条件为 gcd(a,b) = 1。这不要求两数都是素数。","en":"The current interface has domain a,b ∈ ℕ. Coprimality means gcd(a,b) = 1; neither number is required to be prime."}},"injective":{"kind":{"zh":"数学关系","en":"Mathematical relation"},"syntax":"$injective(A, B, f)","summary":{"zh":"f 是从 A 到 B 的单射：不同输入具有不同输出。","en":"f is injective from A to B: distinct inputs have distinct outputs."},"notes":{"zh":"参数依次为定义域 A、陪域 B、函数 f。对 x,y ∈ A，f(x) = f(y) ⇒ x = y。","en":"The arguments are domain A, codomain B, and function f. For x,y ∈ A, f(x) = f(y) implies x = y."}},"surjective":{"kind":{"zh":"数学关系","en":"Mathematical relation"},"syntax":"$surjective(A, B, f)","summary":{"zh":"f 是从 A 到 B 的满射：B 中每个元素都有原像。","en":"f is surjective from A to B: every element of B has a preimage."},"notes":{"zh":"参数依次为定义域 A、陪域 B、函数 f。对每个 y ∈ B，存在 x ∈ A 使 f(x) = y。函数值属于 B 本身不保证满射。","en":"The arguments are domain A, codomain B, and function f. For every y ∈ B there is x ∈ A with f(x) = y. Output membership in B alone does not establish surjectivity."}},"bijective":{"kind":{"zh":"数学关系","en":"Mathematical relation"},"syntax":"$bijective(A, B, f)","summary":{"zh":"f 是从 A 到 B 的双射：同时满足单射和满射。","en":"f is bijective from A to B: both injectivity and surjectivity hold."},"notes":{"zh":"以显式给定的 A 为定义域、B 为陪域、f 为函数。相对于声明接口，每个陪域元素恰有一个原像。","en":"The explicit arguments are domain A, codomain B, and function f. Relative to the declared interface, each codomain element has exactly one preimage."}},"=":{"kind":{"zh":"相等关系","en":"Equality"},"syntax":"a = b","summary":{"zh":"两边表示同一个数学对象。","en":"Both sides denote the same mathematical object."},"notes":{"zh":"在 a = b = c 中，每个相邻等式分别需要依据；悬浮各个等号可查看对应步骤。","en":"In a = b = c, each adjacent equality needs evidence; hover each equals sign to inspect its own step."}},"!=":{"kind":{"zh":"不等关系","en":"Disequality"},"syntax":"a != b","summary":{"zh":"两边表示不同的数学对象。","en":"The two sides denote different mathematical objects."},"notes":{"zh":"这是相等关系的否定，不是不能证明相等时自动得到的结论。","en":"This negates equality; it does not follow merely from failure to prove equality."}},"<":{"kind":{"zh":"实数序关系","en":"Real order relation"},"syntax":"a < b","summary":{"zh":"实数 a 严格小于实数 b。","en":"Real a is strictly less than real b."},"notes":{"zh":"两边须满足该序关系的实数域要求；复数没有这里使用的通常大小序。","en":"Both operands must satisfy the real-domain requirements; this usual order is not defined on arbitrary complex numbers."}},">":{"kind":{"zh":"实数序关系","en":"Real order relation"},"syntax":"a > b","summary":{"zh":"实数 a 严格大于实数 b。","en":"Real a is strictly greater than real b."},"notes":{"zh":"两边须满足该序关系的实数域要求；复数没有这里使用的通常大小序。","en":"Both operands must satisfy the real-domain requirements; this usual order is not defined on arbitrary complex numbers."}},"<=":{"kind":{"zh":"实数序关系","en":"Real order relation"},"syntax":"a <= b","summary":{"zh":"实数 a 小于或等于实数 b。","en":"Real a is less than or equal to real b."},"notes":{"zh":"两边须满足该序关系的实数域要求；复数没有这里使用的通常大小序。","en":"Both operands must satisfy the real-domain requirements; this usual order is not defined on arbitrary complex numbers."}},">=":{"kind":{"zh":"实数序关系","en":"Real order relation"},"syntax":"a >= b","summary":{"zh":"实数 a 大于或等于实数 b。","en":"Real a is greater than or equal to real b."},"notes":{"zh":"两边须满足该序关系的实数域要求；复数没有这里使用的通常大小序。","en":"Both operands must satisfy the real-domain requirements; this usual order is not defined on arbitrary complex numbers."}},"forall":{"kind":{"zh":"逻辑结构","en":"Logical form"},"syntax":"forall x A:\n    P(x)","summary":{"zh":"对于指定类型或范围内的任意对象，所述条件均成立。","en":"The stated conditions hold for every object of the specified type or domain."},"notes":{"zh":"若有前提，只要求在前提成立时推出结论。set、nonempty_set、finite_set 限定集合的种类，不表示属于一个“所有集合的集合”。绑定变量只在量词范围内有效。","en":"With premises, the conclusions are required when those premises hold. set, nonempty_set and finite_set constrain the kind of set, not membership in a set of all sets. The variable is bound within the quantifier."}},"exist":{"kind":{"zh":"逻辑结构","en":"Logical form"},"syntax":"exist x A st {P(x)}","summary":{"zh":"至少存在一个满足所列类型要求及条件的对象。","en":"At least one object satisfies the stated type requirements and conditions."},"notes":{"zh":"需要存在性依据；不指定见证的唯一性。","en":"Existence needs evidence; uniqueness is not asserted."}},"exist!":{"kind":{"zh":"逻辑结构","en":"Logical form"},"syntax":"exist! x A st {P(x)}","summary":{"zh":"存在且仅存在一个满足所列类型要求及条件的对象。","en":"Exactly one object satisfies the stated type requirements and conditions."},"notes":{"zh":"须同时建立存在性与唯一性；给出一个例子只证明前者。","en":"Both existence and uniqueness are required; a single example establishes only existence."}},"and":{"kind":{"zh":"逻辑结构","en":"Logical form"},"syntax":"P and Q","summary":{"zh":"P 和 Q 同时成立。","en":"P and Q both hold."},"notes":{"zh":"证明合取需要建立每一项；已知合取时可以使用其中各项。","en":"Proving a conjunction requires every component; each component can be used once the conjunction is known."}},"or":{"kind":{"zh":"逻辑结构","en":"Logical form"},"syntax":"P or Q","summary":{"zh":"P 与 Q 中至少有一个成立。","en":"At least one of P and Q holds."},"notes":{"zh":"不要求两者互斥；单凭析取不能指定其中某一项成立。","en":"The alternatives need not be exclusive. The disjunction alone does not establish a chosen alternative."}},"=>":{"kind":{"zh":"逻辑结构","en":"Logical form"},"syntax":"premises => conclusions","summary":{"zh":"当前提成立时，结论成立。","en":"The conclusions hold whenever the premises hold."},"notes":{"zh":"前提作为局部假设用于证明结论；蕴含本身不使前提无条件成立。","en":"Premises are local assumptions when proving the conclusions. The implication does not establish its premises unconditionally."}},"<=>":{"kind":{"zh":"逻辑结构","en":"Logical form"},"syntax":"P <=> Q","summary":{"zh":"P 与 Q 互相蕴含。","en":"P and Q imply one another."},"notes":{"zh":"需区分等价定义与单向推论；一般推导结果不自动构成双向等价。","en":"A defining equivalence differs from a one-way implication; a derived consequence is not automatically an equivalence."}},"fn":{"kind":{"zh":"函数接口或函数值","en":"Function interface or value"},"syntax":"fn(x A: condition) B; fn(x A) B {expression}","summary":{"zh":"描述函数的参数域、适用条件与返回集合；带函数体时给出具体函数。","en":"Specify argument domains, guards and the return set; a body supplies a concrete function."},"notes":{"zh":"函数应用须验证输入满足定义域条件。声明陪域 B 不意味着函数满射到 B。","en":"Application checks that inputs meet the domain conditions. Declaring codomain B does not imply surjectivity onto B."}},"set":{"kind":{"zh":"集合种类","en":"Set kind"},"syntax":"X set","summary":{"zh":"参数 X 是一个集合。","en":"The parameter X is a set."},"notes":{"zh":"set 是参数种类，不表示所有集合组成的一个内部集合。","en":"set is a parameter kind, not an internal universal set of all sets."}},"nonempty_set":{"kind":{"zh":"非空集合种类","en":"Nonempty-set kind"},"syntax":"X nonempty_set","summary":{"zh":"参数 X 是至少含一个元素的集合。","en":"The parameter X is a set with at least one element."},"notes":{"zh":"这是对集合参数的非空要求，不会自动选择一个具体元素。","en":"This constrains the set parameter to be nonempty; it does not select an element."}},"finite_set":{"kind":{"zh":"有限集合种类","en":"Finite-set kind"},"syntax":"X finite_set","summary":{"zh":"参数 X 是有限集合。","en":"The parameter X is a finite set."},"notes":{"zh":"有限集合可以为空；非空性需要另行给出。","en":"A finite set may be empty; nonemptiness is a separate condition."}},"release struct def":{"kind":{"zh":"展开结构定义","en":"Unpack a structure definition"},"syntax":"release struct def object","summary":{"zh":"展开一个结构对象的定义性质。","en":"Unpack the defining properties of a structure object."},"notes":{"zh":"按该结构的实际定义引入字段约束及相应关系；不会自动证明定义中未给出的性质。","en":"Introduce the field constraints and relations supplied by the actual structure definition; no unstated properties are established."}},"release obj def":{"kind":{"zh":"展开对象定义","en":"Unpack an object definition"},"syntax":"release obj def object","summary":{"zh":"显式引入对象定义所给出的事实。","en":"Explicitly introduce the facts provided by an object definition."},"notes":{"zh":"使用当前可见的实际定义；这与任意改写一个数学对象不同。","en":"Use the actual visible definition; this does not permit arbitrary replacement of the object."}},"release cart def":{"kind":{"zh":"展开笛卡尔积","en":"Unpack a Cartesian product"},"syntax":"release cart def cart(A, B)","summary":{"zh":"展开笛卡尔积对各坐标的约束。","en":"Unpack Cartesian-product coordinate constraints."},"notes":{"zh":"乘积中的对象由指定数量和类型的坐标刻画；每一坐标必须满足对应因子集合的要求。","en":"A product element is characterized by the specified coordinate count and domains. Each coordinate must meet its factor’s requirements."}},"release tuple def":{"kind":{"zh":"展开元组","en":"Unpack a tuple"},"syntax":"release tuple def tuple","summary":{"zh":"展开元组的坐标及维数性质。","en":"Unpack a tuple’s coordinates and dimension properties."},"notes":{"zh":"坐标编号从 1 开始；仅引入该元组实际给出的坐标关系。","en":"Coordinates are numbered from 1; only the actual tuple’s coordinate relations are introduced."}},"release zorn_lemma":{"kind":{"zh":"佐恩引理","en":"Zorn’s lemma"},"syntax":"release zorn_lemma: ...","summary":{"zh":"在满足条件的偏序结构上应用佐恩引理。","en":"Apply Zorn’s lemma to a partially ordered structure satisfying its hypotheses."},"notes":{"zh":"须建立所用偏序、非空性和链的上界等规定前提，才能引入相应极大元素结论。","en":"The required partial order, nonemptiness and chain-upper-bound premises must be established before the maximal-element conclusion is introduced."}},"release axiom_of_choice":{"kind":{"zh":"选择公理","en":"Axiom of choice"},"syntax":"release axiom_of_choice: ...","summary":{"zh":"对非空集合族应用选择公理。","en":"Apply the axiom of choice to a family of nonempty sets."},"notes":{"zh":"选择函数为族中的每个集合选取一个属于该集合的元素；必须满足该指令实际要求的集合族条件。","en":"A choice function selects an element from each member of the family. The command’s family hypotheses must be established."}},"release regularity_axiom":{"kind":{"zh":"正则公理","en":"Axiom of regularity"},"syntax":"release regularity_axiom(S)","summary":{"zh":"对集合 S 应用正则公理。","en":"Apply the axiom of regularity to S."},"notes":{"zh":"非空集合存在一个与它不交的元素；具体结论及前提以本次指令保留的记录为准。","en":"A nonempty set has an element disjoint from it. The precise premises and conclusions are those retained for this application."}},"have by fn_preimage":{"kind":{"zh":"语句","en":"Statement"},"syntax":"have by fn_preimage: x from y $in fn_range(f)","summary":{"zh":"利用原像的存在性选取具有指定函数值的对象。","en":"Select an input with a specified function value using a preimage existence result."},"notes":{"zh":"须验证所用函数、目标值及相应原像非空等要求；声明不把任意函数当作满射。","en":"The function, target value and required nonempty fiber must be justified; this declaration does not assume that an arbitrary function is surjective."}},"have by replacement_axiom":{"kind":{"zh":"语句","en":"Statement"},"syntax":"have by replacement_axiom: Image from prop relation, set A","summary":{"zh":"按替换公理构造由已给定集合逐点产生的像集。","en":"Construct an image set by replacement from an existing set."},"notes":{"zh":"构造使用给定的定义关系及其唯一性要求，不形成所有对象的无界集合。","en":"The construction uses its specified relation and required uniqueness; it does not form an unrestricted set of all objects."}},"is_real_upper_bound":{"kind":{"zh":"分析命题","en":"Analysis predicate"},"syntax":"$is_real_upper_bound(S, b)","summary":{"zh":"实数 b 是实数集合 S 的上界。","en":"The real b is a upper bound of the real set S."},"notes":{"zh":"∀ x ∈ S, x ≤ b。界不必属于 S，也不必是最优的界。","en":"∀ x ∈ S, x ≤ b. A bound need not belong to S or be the best possible bound."}},"is_real_lower_bound":{"kind":{"zh":"分析命题","en":"Analysis predicate"},"syntax":"$is_real_lower_bound(S, b)","summary":{"zh":"实数 b 是实数集合 S 的下界。","en":"The real b is a lower bound of the real set S."},"notes":{"zh":"∀ x ∈ S, x ≥ b。界不必属于 S，也不必是最优的界。","en":"∀ x ∈ S, x ≥ b. A bound need not belong to S or be the best possible bound."}},"is_real_bounded_above":{"kind":{"zh":"分析命题","en":"Analysis predicate"},"syntax":"$is_real_bounded_above(S)","summary":{"zh":"实数集合 S 有上界。","en":"The real set S is bounded above."},"notes":{"zh":"∃ b ∈ ℝ: ∀ x ∈ S, x ≤ b。这是界的存在性，不指定上确界或下确界。","en":"∃ b ∈ ℝ: ∀ x ∈ S, x ≤ b. This asserts existence of bounds, not a particular supremum or infimum."}},"is_real_bounded_below":{"kind":{"zh":"分析命题","en":"Analysis predicate"},"syntax":"$is_real_bounded_below(S)","summary":{"zh":"实数集合 S 有下界。","en":"The real set S is bounded below."},"notes":{"zh":"∃ b ∈ ℝ: ∀ x ∈ S, b ≤ x。这是界的存在性，不指定上确界或下确界。","en":"∃ b ∈ ℝ: ∀ x ∈ S, b ≤ x. This asserts existence of bounds, not a particular supremum or infimum."}},"is_real_bounded":{"kind":{"zh":"分析命题","en":"Analysis predicate"},"syntax":"$is_real_bounded(S)","summary":{"zh":"实数集合 S 有界。","en":"The real set S is bounded."},"notes":{"zh":"∃ a,b ∈ ℝ: ∀ x ∈ S, a ≤ x ≤ b。这是界的存在性，不指定上确界或下确界。","en":"∃ a,b ∈ ℝ: ∀ x ∈ S, a ≤ x ≤ b. This asserts existence of bounds, not a particular supremum or infimum."}},"is_seq_nondecreasing":{"kind":{"zh":"分析命题","en":"Analysis predicate"},"syntax":"$is_seq_nondecreasing(a)","summary":{"zh":"实数序列 a 单调不减。","en":"The real sequence a is nondecreasing."},"notes":{"zh":"对正整数指标 i < j，a(i) ≤ a(j)。指标域从 1 开始。","en":"For positive integer indices i < j, a(i) ≤ a(j). Sequence indices start at 1."}},"is_seq_nonincreasing":{"kind":{"zh":"分析命题","en":"Analysis predicate"},"syntax":"$is_seq_nonincreasing(a)","summary":{"zh":"实数序列 a 单调不增。","en":"The real sequence a is nonincreasing."},"notes":{"zh":"对正整数指标 i < j，a(i) ≥ a(j)。指标域从 1 开始。","en":"For positive integer indices i < j, a(i) ≥ a(j). Sequence indices start at 1."}},"is_seq_strictly_increasing":{"kind":{"zh":"分析命题","en":"Analysis predicate"},"syntax":"$is_seq_strictly_increasing(a)","summary":{"zh":"实数序列 a 严格递增。","en":"The real sequence a is strictly increasing."},"notes":{"zh":"对正整数指标 i < j，a(i) < a(j)。指标域从 1 开始。","en":"For positive integer indices i < j, a(i) < a(j). Sequence indices start at 1."}},"is_seq_strictly_decreasing":{"kind":{"zh":"分析命题","en":"Analysis predicate"},"syntax":"$is_seq_strictly_decreasing(a)","summary":{"zh":"实数序列 a 严格递减。","en":"The real sequence a is strictly decreasing."},"notes":{"zh":"对正整数指标 i < j，a(i) > a(j)。指标域从 1 开始。","en":"For positive integer indices i < j, a(i) > a(j). Sequence indices start at 1."}},"is_seq_bounded_above":{"kind":{"zh":"分析命题","en":"Analysis predicate"},"syntax":"$is_seq_bounded_above(a)","summary":{"zh":"实数序列 a 有上界。","en":"The real sequence a is bounded above."},"notes":{"zh":"∃ M ∈ ℝ: ∀ n ∈ ℕ+, a(n) ≤ M。有界性约束所有项，不仅是有限个样本。","en":"∃ M ∈ ℝ: ∀ n ∈ ℕ+, a(n) ≤ M. The bound applies to every term, not merely finitely many samples."}},"is_seq_bounded_below":{"kind":{"zh":"分析命题","en":"Analysis predicate"},"syntax":"$is_seq_bounded_below(a)","summary":{"zh":"实数序列 a 有下界。","en":"The real sequence a is bounded below."},"notes":{"zh":"∃ m ∈ ℝ: ∀ n ∈ ℕ+, m ≤ a(n)。有界性约束所有项，不仅是有限个样本。","en":"∃ m ∈ ℝ: ∀ n ∈ ℕ+, m ≤ a(n). The bound applies to every term, not merely finitely many samples."}},"is_seq_bounded":{"kind":{"zh":"分析命题","en":"Analysis predicate"},"syntax":"$is_seq_bounded(a)","summary":{"zh":"实数序列 a 有界。","en":"The real sequence a is bounded."},"notes":{"zh":"∃ m,M ∈ ℝ: ∀ n ∈ ℕ+, m ≤ a(n) ≤ M。有界性约束所有项，不仅是有限个样本。","en":"∃ m,M ∈ ℝ: ∀ n ∈ ℕ+, m ≤ a(n) ≤ M. The bound applies to every term, not merely finitely many samples."}},"is_seq_cauchy":{"kind":{"zh":"分析命题","en":"Analysis predicate"},"syntax":"$is_seq_cauchy(a)","summary":{"zh":"实数序列 a 是柯西序列。","en":"The real sequence a is Cauchy."},"notes":{"zh":"∀ ε > 0，存在 N ∈ ℕ+，使所有 m,n ≥ N 都满足 |a(m) − a(n)| < ε。定义比较尾部项，不指定极限值。","en":"For every ε > 0 there is N ∈ ℕ+ such that |a(m) − a(n)| < ε for all m,n ≥ N. The definition compares tail terms without naming a limit."}},"is_seq_convergent":{"kind":{"zh":"分析命题","en":"Analysis predicate"},"syntax":"$is_seq_convergent(a)","summary":{"zh":"实数序列 a 收敛到某个实数。","en":"The real sequence a converges to some real number."},"notes":{"zh":"存在 L ∈ ℝ，使 a 收敛到 L；这条命题不单独指定 L 的值。","en":"There exists L ∈ ℝ to which a converges; this proposition does not itself specify that value."}},"has_seq_limit":{"kind":{"zh":"分析命题","en":"Analysis predicate"},"syntax":"$has_seq_limit(a, L)","summary":{"zh":"实数序列 a 的极限为实数 L。","en":"The real sequence a has real limit L."},"notes":{"zh":"∀ ε > 0，存在 N ∈ ℕ+，使 n ≥ N ⇒ |a(n) − L| < ε。a 的指标为正整数。","en":"For every ε > 0 there exists N ∈ ℕ+ such that n ≥ N implies |a(n) − L| < ε. The sequence is indexed by positive integers."}},"has_seq_limsup":{"kind":{"zh":"分析命题","en":"Analysis predicate"},"syntax":"$has_seq_limsup(a, L)","summary":{"zh":"实数序列 a 的有限上极限为 L。","en":"The real sequence a has finite limit superior L."},"notes":{"zh":"对每个 ε > 0，最终所有项满足 a(n) < L + ε，且任意靠后的尾部都仍有一项满足 L − ε < a(n)。不表示序列一定收敛。","en":"For every ε > 0, eventually every term satisfies a(n) < L + ε, and every tail contains a term satisfying L − ε < a(n). This does not assert convergence of the sequence."}},"has_seq_liminf":{"kind":{"zh":"分析命题","en":"Analysis predicate"},"syntax":"$has_seq_liminf(a, L)","summary":{"zh":"实数序列 a 的有限下极限为 L。","en":"The real sequence a has finite limit inferior L."},"notes":{"zh":"对每个 ε > 0，最终所有项满足 L − ε < a(n)，且任意靠后的尾部都仍有一项满足 a(n) < L + ε。不表示序列一定收敛。","en":"For every ε > 0, eventually every term satisfies L − ε < a(n), and every tail contains a term satisfying a(n) < L + ε. This does not assert convergence of the sequence."}},"is_real_accumulation_at":{"kind":{"zh":"分析命题","en":"Analysis predicate"},"syntax":"$is_real_accumulation_at(D, x₀)","summary":{"zh":"x₀ 是实数集合 D 的聚点。","en":"x₀ is a accumulation point of the real set D."},"notes":{"zh":"对每个 δ > 0，都存在 x ∈ D 满足 0 < |x − x₀| < δ。x₀ 本身不必属于 D。","en":"For every δ > 0 there is x ∈ D with 0 < |x − x₀| < δ. The point x₀ need not itself belong to D."}},"is_real_accumulation_left":{"kind":{"zh":"分析命题","en":"Analysis predicate"},"syntax":"$is_real_accumulation_left(D, x₀)","summary":{"zh":"x₀ 是实数集合 D 的左聚点。","en":"x₀ is a left accumulation point of the real set D."},"notes":{"zh":"对每个 δ > 0，都存在 x ∈ D 满足 x₀ − δ < x < x₀。x₀ 本身不必属于 D。","en":"For every δ > 0 there is x ∈ D with x₀ − δ < x < x₀. The point x₀ need not itself belong to D."}},"is_real_accumulation_right":{"kind":{"zh":"分析命题","en":"Analysis predicate"},"syntax":"$is_real_accumulation_right(D, x₀)","summary":{"zh":"x₀ 是实数集合 D 的右聚点。","en":"x₀ is a right accumulation point of the real set D."},"notes":{"zh":"对每个 δ > 0，都存在 x ∈ D 满足 x₀ < x < x₀ + δ。x₀ 本身不必属于 D。","en":"For every δ > 0 there is x ∈ D with x₀ < x < x₀ + δ. The point x₀ need not itself belong to D."}},"has_limit_at":{"kind":{"zh":"分析命题","en":"Analysis predicate"},"syntax":"$has_limit_at(f, x₀, L)","summary":{"zh":"函数 f 在 x 趋于 x₀ 时的极限为 L。","en":"The limit of f as x approaches x₀ is L."},"notes":{"zh":"在 f 的实际定义域内，∀ ε > 0，存在 δ > 0，使 0 < |x − x₀| < δ ⇒ |f(x) − L| < ε。相应聚点要求排除空洞的极限。","en":"Relative to f’s actual domain, for every ε > 0 there is δ > 0 such that 0 < |x − x₀| < δ implies |f(x) − L| < ε. The required accumulation condition rules out vacuous limits."}},"has_limit_left":{"kind":{"zh":"分析命题","en":"Analysis predicate"},"syntax":"$has_limit_left(f, x₀, L)","summary":{"zh":"函数 f 在 x 趋于 x₀ 时的左极限为 L。","en":"The left-hand limit of f as x approaches x₀ is L."},"notes":{"zh":"在 f 的实际定义域内，∀ ε > 0，存在 δ > 0，使 x₀ − δ < x < x₀ ⇒ |f(x) − L| < ε。相应聚点要求排除空洞的极限。","en":"Relative to f’s actual domain, for every ε > 0 there is δ > 0 such that x₀ − δ < x < x₀ implies |f(x) − L| < ε. The required accumulation condition rules out vacuous limits."}},"has_limit_right":{"kind":{"zh":"分析命题","en":"Analysis predicate"},"syntax":"$has_limit_right(f, x₀, L)","summary":{"zh":"函数 f 在 x 趋于 x₀ 时的右极限为 L。","en":"The right-hand limit of f as x approaches x₀ is L."},"notes":{"zh":"在 f 的实际定义域内，∀ ε > 0，存在 δ > 0，使 x₀ < x < x₀ + δ ⇒ |f(x) − L| < ε。相应聚点要求排除空洞的极限。","en":"Relative to f’s actual domain, for every ε > 0 there is δ > 0 such that x₀ < x < x₀ + δ implies |f(x) − L| < ε. The required accumulation condition rules out vacuous limits."}},"has_limit_pos_inf":{"kind":{"zh":"分析命题","en":"Analysis predicate"},"syntax":"$has_limit_pos_inf(f, L)","summary":{"zh":"函数 f 在 x 趋于正无穷时的有限极限为 L。","en":"The finite limit of f as x tends to positive infinity is L."},"notes":{"zh":"∀ ε > 0，存在 M ∈ ℝ，使定义域内满足 x > M 的 x 都有 |f(x) − L| < ε；定义域还须满足对应无界趋近要求。","en":"For every ε > 0 there is M ∈ ℝ such that domain points with x > M satisfy |f(x) − L| < ε; the domain must also support the corresponding unbounded approach."}},"has_limit_neg_inf":{"kind":{"zh":"分析命题","en":"Analysis predicate"},"syntax":"$has_limit_neg_inf(f, L)","summary":{"zh":"函数 f 在 x 趋于负无穷时的有限极限为 L。","en":"The finite limit of f as x tends to negative infinity is L."},"notes":{"zh":"∀ ε > 0，存在 M ∈ ℝ，使定义域内满足 x < M 的 x 都有 |f(x) − L| < ε；定义域还须满足对应无界趋近要求。","en":"For every ε > 0 there is M ∈ ℝ such that domain points with x < M satisfy |f(x) − L| < ε; the domain must also support the corresponding unbounded approach."}},"is_continuous_at":{"kind":{"zh":"分析命题","en":"Analysis predicate"},"syntax":"$is_continuous_at(f, x₀)","summary":{"zh":"函数 f 在定义域中的点 x₀ 处连续。","en":"The function f is continuous at domain point x₀."},"notes":{"zh":"在相应的定义域方向上，∀ ε > 0，存在 δ > 0，使 |x − x₀| < δ ⇒ |f(x) − f(x₀)| < ε。这里须有定义 f(x₀)。","en":"Relative to the corresponding side of the domain, for every ε > 0 there is δ > 0 such that |x − x₀| < δ implies |f(x) − f(x₀)| < ε. The value f(x₀) must be defined."}},"is_continuous_left":{"kind":{"zh":"分析命题","en":"Analysis predicate"},"syntax":"$is_continuous_left(f, x₀)","summary":{"zh":"函数 f 在定义域中的点 x₀ 处左连续。","en":"The function f is left-continuous at domain point x₀."},"notes":{"zh":"在相应的定义域方向上，∀ ε > 0，存在 δ > 0，使 x₀ − δ < x ≤ x₀ ⇒ |f(x) − f(x₀)| < ε。这里须有定义 f(x₀)。","en":"Relative to the corresponding side of the domain, for every ε > 0 there is δ > 0 such that x₀ − δ < x ≤ x₀ implies |f(x) − f(x₀)| < ε. The value f(x₀) must be defined."}},"is_continuous_right":{"kind":{"zh":"分析命题","en":"Analysis predicate"},"syntax":"$is_continuous_right(f, x₀)","summary":{"zh":"函数 f 在定义域中的点 x₀ 处右连续。","en":"The function f is right-continuous at domain point x₀."},"notes":{"zh":"在相应的定义域方向上，∀ ε > 0，存在 δ > 0，使 x₀ ≤ x < x₀ + δ ⇒ |f(x) − f(x₀)| < ε。这里须有定义 f(x₀)。","en":"Relative to the corresponding side of the domain, for every ε > 0 there is δ > 0 such that x₀ ≤ x < x₀ + δ implies |f(x) − f(x₀)| < ε. The value f(x₀) must be defined."}},"is_continuous":{"kind":{"zh":"分析命题","en":"Analysis predicate"},"syntax":"$is_continuous(f)","summary":{"zh":"函数 f 在其实际定义域的每一点连续。","en":"The function f is continuous at every point of its actual domain."},"notes":{"zh":"每一点可以使用不同的 δ；这与一致连续性的统一量词要求不同。","en":"Different points may use different δ. Uniform continuity imposes a different, uniform quantifier requirement."}},"is_uniformly_continuous":{"kind":{"zh":"分析命题","en":"Analysis predicate"},"syntax":"$is_uniformly_continuous(f)","summary":{"zh":"函数 f 在其实际定义域上一致连续。","en":"The function f is uniformly continuous on its actual domain."},"notes":{"zh":"∀ ε > 0，存在同一个 δ > 0，使所有定义域内的 x,y 都满足 |x − y| < δ ⇒ |f(x) − f(y)| < ε。δ 不依赖所选的点。","en":"For every ε > 0 one δ > 0 works for all domain points x,y: |x − y| < δ implies |f(x) − f(y)| < ε. The choice of δ does not depend on the points."}},"is_lipschitz":{"kind":{"zh":"分析命题","en":"Analysis predicate"},"syntax":"$is_lipschitz(f, K)","summary":{"zh":"函数 f 满足给定常数 K 的 Lipschitz 估计。","en":"The function f satisfies a Lipschitz estimate with constant K."},"notes":{"zh":"K 为非负实数，且对定义域内所有 x,y，有 |f(x) − f(y)| ≤ K|x − y|。这不表示 K 是最小常数。","en":"K is a nonnegative real and |f(x) − f(y)| ≤ K|x − y| for all domain points x,y. K need not be the smallest possible constant."}},"has_derivative_at":{"kind":{"zh":"分析命题","en":"Analysis predicate"},"syntax":"$has_derivative_at(f, x₀, L)","summary":{"zh":"函数 f 在 x₀ 处可导，导数为 L。","en":"The function f is differentiable at x₀ with derivative L."},"notes":{"zh":"差商 (f(x) − f(x₀))/(x − x₀) 在 x 趋于 x₀ 时趋于 L；须满足接口规定的定义域与内点条件。","en":"The difference quotient (f(x) − f(x₀))/(x − x₀) tends to L as x approaches x₀, subject to the interface’s domain and interior-point conditions."}},"is_differentiable_at":{"kind":{"zh":"分析命题","en":"Analysis predicate"},"syntax":"$is_differentiable_at(f, x₀)","summary":{"zh":"函数 f 在 x₀ 处存在有限实导数。","en":"The function f has a finite real derivative at x₀."},"notes":{"zh":"这是某个导数值的存在性，不指定导数的具体数值。","en":"This asserts existence of a derivative value without specifying its numerical value."}},"has_riemann_integral":{"kind":{"zh":"分析命题","en":"Analysis predicate"},"syntax":"$has_riemann_integral(f, a, b, I)","summary":{"zh":"函数 f 在区间 [a,b] 上的黎曼积分为 I。","en":"The Riemann integral of f over [a,b] is I."},"notes":{"zh":"满足积分接口的端点与函数域要求后，足够细的带标记分割，其黎曼和一致地接近 I；不是只检查某一种分割。","en":"Subject to the integral interface’s endpoint and function-domain requirements, all sufficiently fine tagged partitions have Riemann sums close to I; a single chosen partition does not suffice."}},"is_riemann_integrable":{"kind":{"zh":"分析命题","en":"Analysis predicate"},"syntax":"$is_riemann_integrable(f, a, b)","summary":{"zh":"函数 f 在区间 [a,b] 上存在有限黎曼积分。","en":"The function f has a finite Riemann integral over [a,b]."},"notes":{"zh":"这是积分值的存在性；指定积分等于 I 是更具体的命题。","en":"This asserts existence of an integral value; asserting that it equals a specified I is more specific."}},"is_choice_function_for":{"kind":{"zh":"选择函数关系","en":"Choice-function relation"},"syntax":"$is_choice_function_for(I, S, F, c)","summary":{"zh":"c 为以 I 为指标、取值于 S 的集合族 F 逐点选择元素。","en":"c selects an element from each member of the family F indexed by I with ambient set S."},"notes":{"zh":"I、S 为集合，F : I → S，c : I → family_union(S)。对每个 i ∈ I，要求 c(i) ∈ F(i)。","en":"I and S are sets, F : I → S, and c : I → family_union(S). For every i ∈ I, c(i) ∈ F(i)."}},"∉":{"kind":{"zh":"非归属关系","en":"Non-membership"},"syntax":"x ∉ A","summary":{"zh":"对象 x 不属于集合 A。","en":"The object x is not an element of A."},"notes":{"zh":"这是归属关系的否定，与不能证明 x ∈ A 不同。","en":"This negates membership; it does not follow merely from failure to prove x ∈ A."}},"is_cart":{"kind":{"zh":"已移除的语法","en":"Removed syntax"},"syntax":"$is_cart(...)","summary":{"zh":"该谓词已从当前 Litex 语法中移除。","en":"This predicate has been removed from current Litex syntax."},"notes":{"zh":"请使用当前支持的集合归属、相等关系或逐点相等证明；不能再用该名字建立内置事实。","en":"Use ordinary set equality or cart membership instead. This spelling no longer establishes a builtin fact."},"status":"removed"},"is_tuple":{"kind":{"zh":"已移除的语法","en":"Removed syntax"},"syntax":"$is_tuple(...)","summary":{"zh":"该谓词已从当前 Litex 语法中移除。","en":"This predicate has been removed from current Litex syntax."},"notes":{"zh":"请使用当前支持的集合归属、相等关系或逐点相等证明；不能再用该名字建立内置事实。","en":"Use exact finite_seq membership instead. This spelling no longer establishes a builtin fact."},"status":"removed"},"fn_eq":{"kind":{"zh":"已移除的语法","en":"Removed syntax"},"syntax":"$fn_eq(...)","summary":{"zh":"该谓词已从当前 Litex 语法中移除。","en":"This predicate has been removed from current Litex syntax."},"notes":{"zh":"请使用当前支持的集合归属、相等关系或逐点相等证明；不能再用该名字建立内置事实。","en":"Use ordinary equality f = g instead. This spelling no longer establishes a builtin fact."},"status":"removed"},"fn_eq_in":{"kind":{"zh":"已移除的语法","en":"Removed syntax"},"syntax":"$fn_eq_in(...)","summary":{"zh":"该谓词已从当前 Litex 语法中移除。","en":"This predicate has been removed from current Litex syntax."},"notes":{"zh":"请使用当前支持的集合归属、相等关系或逐点相等证明；不能再用该名字建立内置事实。","en":"Use by fn_extension or forall for pointwise agreement instead. This spelling no longer establishes a builtin fact."},"status":"removed"},"contra":{"kind":{"zh":"反证法","en":"Proof by contradiction"},"syntax":"by contra:\n    ? fact\n    proof","summary":{"zh":"假设目标的否定，并由矛盾证明原目标。","en":"Prove a goal by deriving a contradiction under its negation."},"notes":{"zh":"须实际建立互相矛盾的事实。反证假设不会作为无条件结论交给后文。","en":"Incompatible facts must actually be established. The temporary negation is not exported as an unconditional conclusion."}},"cases":{"kind":{"zh":"分类证明","en":"Proof by cases"},"syntax":"by cases:\n    ? fact\n    case condition:\n        proof","summary":{"zh":"通过穷尽可能性的分类讨论证明结论。","en":"Prove conclusions by an exhaustive case split."},"notes":{"zh":"每种情况中都须证明所需结论，或证明该情况不可能发生；分支假设只在对应分支有效。","en":"Each case must establish the requested conclusions or be shown impossible. A branch assumption is local to its branch."}},"induc":{"kind":{"zh":"数学归纳法","en":"Mathematical induction"},"syntax":"by induc n from k:\n    ? fact\n    proof","summary":{"zh":"用基础情形与归纳步骤证明整数指标上的结论。","en":"Prove an integer-indexed conclusion using a base case and induction step."},"notes":{"zh":"基础情形验证起点；归纳步骤在相应归纳假设下证明下一指标的结论。起点和参数域也须满足要求。","en":"The base case establishes the starting point. The step proves the next case under the corresponding induction hypothesis. The start and parameter domain must also satisfy their requirements."}},"strong_induc":{"kind":{"zh":"强归纳法","en":"Strong induction"},"syntax":"by strong_induc n from k:\n    ? fact\n    proof","summary":{"zh":"用所有较小指标的结论作归纳假设。","en":"Use conclusions at all smaller admissible indices as the induction hypothesis."},"notes":{"zh":"仍须验证基础情形；强归纳允许在归纳步骤中使用起点之后且小于当前指标的已假定结论。","en":"A base case is still required. The induction step may use assumed conclusions from the starting point up to, but not including, the current index."}},"enumerate":{"kind":{"zh":"有限枚举证明","en":"Finite enumeration proof"},"syntax":"by enumerate:\n    ? forall x S => condition\n    proof","summary":{"zh":"逐个验证有限集合中的对象，证明一个全称命题。","en":"Prove a universal statement by checking each element of a finite set."},"notes":{"zh":"集合必须可按该指令支持的方式枚举；验证一个例子不能替代检查全部元素。","en":"The carrier must be enumerable by this command. Checking one example does not establish every case."}},"extension":{"kind":{"zh":"集合外延证明","en":"Set extensionality"},"syntax":"by extension A = B","summary":{"zh":"用集合的相互包含证明集合相等。","en":"Prove equality of sets by mutual inclusion."},"notes":{"zh":"分别验证 A ⊆ B 和 B ⊆ A。仅证明其中一个方向，通常只能得到包含关系。","en":"Establish A ⊆ B and B ⊆ A separately. A single direction generally establishes only inclusion."}},"fn_extension":{"kind":{"zh":"函数外延证明","en":"Function extensionality"},"syntax":"by fn_extension f = g","summary":{"zh":"在共同的函数接口上用逐点相等证明函数相等。","en":"Prove equality of functions by pointwise equality on a common interface."},"notes":{"zh":"须满足函数域与接口匹配要求，再证明每个合法输入上的值相同；有限个样本相等通常不够。","en":"The function domains and interfaces must match, and values must agree at every admissible input. Agreement at finitely many sample inputs generally does not suffice."}},"for":{"kind":{"zh":"范围枚举证明","en":"Range enumeration proof"},"syntax":"by for:\n    ? forall i range(a, b) => condition\n    proof","summary":{"zh":"通过有限范围的逐项检查证明全称结论。","en":"Prove a universal conclusion by checking a finite range."},"notes":{"zh":"按指令支持的范围或笛卡尔积枚举所有参数组合，并对每组检查结论。","en":"Enumerate all parameter combinations in the supported ranges or Cartesian products and verify the conclusion in each case."}},"transitive":{"kind":{"zh":"性质登记","en":"Property registration"},"syntax":"register transitive: ...","summary":{"zh":"登记一个二元谓词的传递性规则。","en":"Register the transitivity law of a binary predicate."},"notes":{"zh":"规则形状为 P(a,b) ∧ P(b,c) ⇒ P(a,c)，变量须满足所登记接口的类型和适用条件。 登记前须验证相应的全称规律。","en":"The law has shape P(a,b) ∧ P(b,c) ⇒ P(a,c), subject to the registered interface’s types and applicability conditions. The corresponding universal law must be verified before registration."}},"symmetric":{"kind":{"zh":"性质登记","en":"Property registration"},"syntax":"register symmetric: ...","summary":{"zh":"登记一个二元谓词的对称性规则。","en":"Register the symmetry law of a binary predicate."},"notes":{"zh":"规则形状为 P(a,b) ⇒ P(b,a)，变量须满足所登记接口的类型和适用条件。 登记前须验证相应的全称规律。","en":"The law has shape P(a,b) ⇒ P(b,a), subject to the registered interface’s types and applicability conditions. The corresponding universal law must be verified before registration."}},"reflexive":{"kind":{"zh":"性质登记","en":"Property registration"},"syntax":"register reflexive: ...","summary":{"zh":"登记一个二元谓词的自反性规则。","en":"Register the reflexivity law of a binary predicate."},"notes":{"zh":"规则形状为 P(a,a)，变量须满足所登记接口的类型和适用条件。 登记前须验证相应的全称规律。","en":"The law has shape P(a,a), subject to the registered interface’s types and applicability conditions. The corresponding universal law must be verified before registration."}},"zorn_lemma":{"kind":{"zh":"佐恩引理","en":"Zorn’s lemma"},"syntax":"release zorn_lemma: ...","summary":{"zh":"在满足条件的偏序结构上应用佐恩引理。","en":"Apply Zorn’s lemma to a partially ordered structure satisfying its hypotheses."},"notes":{"zh":"须建立所用偏序、非空性和链的上界等规定前提，才能引入相应极大元素结论。","en":"The required partial order, nonemptiness and chain-upper-bound premises must be established before the maximal-element conclusion is introduced."}},"axiom_of_choice":{"kind":{"zh":"选择公理","en":"Axiom of choice"},"syntax":"release axiom_of_choice: ...","summary":{"zh":"对非空集合族应用选择公理。","en":"Apply the axiom of choice to a family of nonempty sets."},"notes":{"zh":"选择函数为族中的每个集合选取一个属于该集合的元素；必须满足该指令实际要求的集合族条件。","en":"A choice function selects an element from each member of the family. The command’s family hypotheses must be established."}},"regularity_axiom":{"kind":{"zh":"正则公理","en":"Axiom of regularity"},"syntax":"release regularity_axiom(S)","summary":{"zh":"对集合 S 应用正则公理。","en":"Apply the axiom of regularity to S."},"notes":{"zh":"非空集合存在一个与它不交的元素；具体结论及前提以本次指令保留的记录为准。","en":"A nonempty set has an element disjoint from it. The precise premises and conclusions are those retained for this application."}},"replacement_axiom":{"kind":{"zh":"语句","en":"Statement"},"syntax":"have by replacement_axiom: Image from prop relation, set A","summary":{"zh":"按替换公理构造由已给定集合逐点产生的像集。","en":"Construct an image set by replacement from an existing set."},"notes":{"zh":"构造使用给定的定义关系及其唯一性要求，不形成所有对象的无界集合。","en":"The construction uses its specified relation and required uniqueness; it does not form an unrestricted set of all objects."}},"def":{"kind":{"zh":"定义展开指令的一部分","en":"Definition-expansion keyword"},"syntax":"by def $P(arguments)","summary":{"zh":"在 by def 中表示使用谓词定义证明一个实例。","en":"Within by def, select a predicate definition to prove an instance."},"notes":{"zh":"def 在这里不是另起一个定义；完整作用由复合指令确定。","en":"Here def does not introduce a new definition; its role is determined by the complete command."}},"case":{"kind":{"zh":"条件分支","en":"Conditional branch"},"syntax":"case condition: ...","summary":{"zh":"引入一个由条件限定的证明或函数定义分支。","en":"Introduce a branch of a proof or function definition under a condition."},"notes":{"zh":"分支条件只在对应分支内使用；能否选择该分支、分支是否穷尽，取决于外层的实际指令。","en":"The condition is local to its branch. Branch selection and exhaustiveness are obligations of the actual enclosing command."}},"by":{"kind":{"zh":"证明方法引导词","en":"Proof-method introducer"},"syntax":"by def; by thm; by contra; by cases","summary":{"zh":"指定采用的证明方法。","en":"Select a proof method."},"notes":{"zh":"by 与后面的词共同决定方法；它本身不提供任何结论的依据。","en":"The following word completes the method. The word by alone supplies no proof of a conclusion."}},"release":{"kind":{"zh":"引入已有结论","en":"Release packaged conclusions"},"syntax":"release thm ...; release tuple def ...","summary":{"zh":"显式引入已有定理或定义所提供的结论。","en":"Explicitly introduce conclusions supplied by an existing theorem or definition."},"notes":{"zh":"具体要检查的前提和能得到的结论由完整的 release 指令决定；不是任意增加假设。","en":"The complete release command determines the requirements and conclusions; it does not add arbitrary assumptions."}},"register":{"kind":{"zh":"登记已验证的规律","en":"Register a verified law"},"syntax":"register transitive; register symmetric; register reflexive","summary":{"zh":"将已验证且形状匹配的谓词规律登记为可复用规则。","en":"Register a verified predicate law of the required shape for reuse."},"notes":{"zh":"须验证所列规律并匹配相应接口；登记不是跳过证明的公理声明。","en":"The law must be verified and match its required interface; registration is not an unproved axiom declaration."}},"witness":{"kind":{"zh":"构造见证","en":"Witness construction"},"syntax":"witness exist x A st {P(x)} from a","summary":{"zh":"提供具体对象以建立存在性或非空性。","en":"Supply concrete objects to establish existence or nonemptiness."},"notes":{"zh":"见证须满足目标所要求的域与条件；对象的存在不能代替对其性质的验证。","en":"The witnesses must meet the goal’s domains and conditions; existence of an object does not establish its required properties."}},"algo":{"kind":{"zh":"算法定义","en":"Algorithm definition"},"syntax":"algo f(...) ... by cases; algo f(...) ... by induc","summary":{"zh":"为带数学接口的函数给出可执行分支或递归规则。","en":"Provide executable cases or recursion rules for a function with a mathematical interface."},"notes":{"zh":"函数域、返回域和递归度量等要求由所用定义形式决定。","en":"The definition form determines the domain, return-domain and recursion-measure requirements."}},"expand":{"kind":{"zh":"展开整数范围归属","en":"Expand integer-range membership"},"syntax":"expand: x $in range(a, b)","summary":{"zh":"将已知整数范围归属展开为对应的有限种取值。","en":"Expand known integer-range membership into the corresponding finite alternatives."},"notes":{"zh":"range(a,b) 包含 a 而不包含 b；展开不改变这些边界。","en":"range(a,b) includes a and excludes b; expansion preserves these bounds."}},"impossible":{"kind":{"zh":"指出矛盾","en":"Contradiction closing"},"syntax":"impossible fact","summary":{"zh":"指出一个与当前已建立事实相矛盾的陈述，以结束相应证明分支。","en":"Identify a statement incompatible with established facts to close the corresponding proof branch."},"notes":{"zh":"须由实际证明记录建立矛盾；仅写出 impossible 不会使任意命题成立。","en":"The contradiction must be established by actual proof evidence; writing impossible alone proves nothing."}},"?":{"kind":{"zh":"目标标记","en":"Goal marker"},"syntax":"? fact","summary":{"zh":"标出当前块承诺证明的数学结论。","en":"Mark the mathematical conclusion promised by the current block."},"notes":{"zh":"目标需要后续证明；标记本身不把目标作为已知事实。","en":"The goal still requires a proof; the marker does not make it an established fact."}},"st":{"kind":{"zh":"存在量词的条件引导词","en":"Such-that clause"},"syntax":"exist x A st {P(x)}","summary":{"zh":"引出存在对象必须满足的条件。","en":"Introduce the conditions an existential witness must satisfy."},"notes":{"zh":"st 对应 such that；条件位于存在量词的绑定范围内，可能包含多个需要同时成立的事实。","en":"st means such that. The conditions are within the existential binder and may require several facts simultaneously."}},"from":{"kind":{"zh":"指定对象或起点","en":"Source or starting-point keyword"},"syntax":"witness ... from a; obtain ... from fact; by induc n from k","summary":{"zh":"依所在指令指定见证来源、存在命题或归纳起点。","en":"Specify witnesses, an existential source or an induction start according to the enclosing command."},"notes":{"zh":"该词不单独表达一个数学推理规则；应结合完整指令阅读。","en":"This word is not itself an inference rule; read it as part of the complete command."}},"as":{"kind":{"zh":"保留拼写","en":"Reserved spelling"},"status":"reserved","syntax":"as","summary":{"zh":"当前词表中的保留拼写，没有独立的数学含义。","en":"A reserved vocabulary spelling with no standalone mathematical meaning."},"notes":{"zh":"当前解析器没有实现独立的 as 语句。它不表示相等、集合归属或蕴含，也不提供推理依据。","en":"The current parser implements no standalone as statement. This token does not denote equality, membership or implication and supplies no proof evidence."}},"import":{"kind":{"zh":"配置中的依赖声明","en":"Configuration dependency declaration"},"status":"not_statement","syntax":"litex.config","summary":{"zh":"import 不能作为 Litex 源码语句；依赖在 litex.config 中声明。","en":"import is not a Litex source statement; declare dependencies in litex.config."},"notes":{"zh":"词表保留 import 的拼写，但在源码中使用它会得到明确的语法错误。导入配置不能替代所用数学结论的证明。","en":"The spelling is recognized, but using it as source produces an explicit parse error. Dependency configuration does not replace proofs of mathematical conclusions."}},"N":{"kind":{"zh":"数集","en":"Number set"},"syntax":"N","summary":{"zh":"自然数集。","en":"Natural numbers."},"notes":{"zh":"{0, 1, 2, …}。写 x $in N 表示 x 属于该数集。","en":"{0, 1, 2, …}. Writing x $in N asserts membership in this set."}},"N+":{"kind":{"zh":"数集","en":"Number set"},"syntax":"N+","summary":{"zh":"正自然数集。","en":"Positive natural numbers."},"notes":{"zh":"{1, 2, 3, …}。写 x $in N+ 表示 x 属于该数集。","en":"{1, 2, 3, …}. Writing x $in N+ asserts membership in this set."}},"Z":{"kind":{"zh":"数集","en":"Number set"},"syntax":"Z","summary":{"zh":"整数集。","en":"Integers."},"notes":{"zh":"{…, −2, −1, 0, 1, 2, …}。写 x $in Z 表示 x 属于该数集。","en":"{…, −2, −1, 0, 1, 2, …}. Writing x $in Z asserts membership in this set."}},"Q":{"kind":{"zh":"数集","en":"Number set"},"syntax":"Q","summary":{"zh":"有理数集。","en":"Rational numbers."},"notes":{"zh":"{p/q : p ∈ ℤ, q ∈ ℤ, q ≠ 0}。写 x $in Q 表示 x 属于该数集。","en":"{p/q : p ∈ ℤ, q ∈ ℤ, q ≠ 0}. Writing x $in Q asserts membership in this set."}},"R":{"kind":{"zh":"数集","en":"Number set"},"syntax":"R","summary":{"zh":"实数集。","en":"Real numbers."},"notes":{"zh":"ℝ。写 x $in R 表示 x 属于该数集。","en":"ℝ. Writing x $in R asserts membership in this set."}},"C":{"kind":{"zh":"数集","en":"Number set"},"syntax":"C","summary":{"zh":"复数集。","en":"Complex numbers."},"notes":{"zh":"{a + bi : a,b ∈ ℝ}。写 x $in C 表示 x 属于该数集。","en":"{a + bi : a,b ∈ ℝ}. Writing x $in C asserts membership in this set."}},"Z+":{"kind":{"zh":"受限数集","en":"Restricted number set"},"syntax":"Z+","summary":{"zh":"正整数集。","en":"Positive integers."},"notes":{"zh":"x ∈ Z+ ⇔ x ∈ Z 且 x > 0。","en":"x ∈ Z+ iff x ∈ Z and x > 0."}},"Q+":{"kind":{"zh":"受限数集","en":"Restricted number set"},"syntax":"Q+","summary":{"zh":"正有理数集。","en":"Positive rationals."},"notes":{"zh":"x ∈ Q+ ⇔ x ∈ Q 且 x > 0。","en":"x ∈ Q+ iff x ∈ Q and x > 0."}},"R+":{"kind":{"zh":"受限数集","en":"Restricted number set"},"syntax":"R+","summary":{"zh":"正实数集。","en":"Positive reals."},"notes":{"zh":"x ∈ R+ ⇔ x ∈ R 且 x > 0。","en":"x ∈ R+ iff x ∈ R and x > 0."}},"Z-":{"kind":{"zh":"受限数集","en":"Restricted number set"},"syntax":"Z-","summary":{"zh":"负整数集。","en":"Negative integers."},"notes":{"zh":"x ∈ Z- ⇔ x ∈ Z 且 x < 0。","en":"x ∈ Z- iff x ∈ Z and x < 0."}},"Q-":{"kind":{"zh":"受限数集","en":"Restricted number set"},"syntax":"Q-","summary":{"zh":"负有理数集。","en":"Negative rationals."},"notes":{"zh":"x ∈ Q- ⇔ x ∈ Q 且 x < 0。","en":"x ∈ Q- iff x ∈ Q and x < 0."}},"R-":{"kind":{"zh":"受限数集","en":"Restricted number set"},"syntax":"R-","summary":{"zh":"负实数集。","en":"Negative reals."},"notes":{"zh":"x ∈ R- ⇔ x ∈ R 且 x < 0。","en":"x ∈ R- iff x ∈ R and x < 0."}},"Z*":{"kind":{"zh":"受限数集","en":"Restricted number set"},"syntax":"Z*","summary":{"zh":"非零整数集。","en":"Nonzero integers."},"notes":{"zh":"x ∈ Z* ⇔ x ∈ Z 且 x ≠ 0。","en":"x ∈ Z* iff x ∈ Z and x ≠ 0."}},"Q*":{"kind":{"zh":"受限数集","en":"Restricted number set"},"syntax":"Q*","summary":{"zh":"非零有理数集。","en":"Nonzero rationals."},"notes":{"zh":"x ∈ Q* ⇔ x ∈ Q 且 x ≠ 0。","en":"x ∈ Q* iff x ∈ Q and x ≠ 0."}},"R*":{"kind":{"zh":"受限数集","en":"Restricted number set"},"syntax":"R*","summary":{"zh":"非零实数集。","en":"Nonzero reals."},"notes":{"zh":"x ∈ R* ⇔ x ∈ R 且 x ≠ 0。","en":"x ∈ R* iff x ∈ R and x ≠ 0."}},"C*":{"kind":{"zh":"受限数集","en":"Restricted number set"},"syntax":"C*","summary":{"zh":"非零复数集。","en":"Nonzero complex numbers."},"notes":{"zh":"x ∈ C* ⇔ x ∈ C 且 x ≠ 0。","en":"x ∈ C* iff x ∈ C and x ≠ 0."}},"i":{"kind":{"zh":"数学常数","en":"Mathematical constant"},"syntax":"i","summary":{"zh":"虚数单位。","en":"The imaginary unit."},"notes":{"zh":"i ∈ ℂ，且 i² = −1。","en":"i ∈ ℂ and i² = −1."}},"e":{"kind":{"zh":"数学常数","en":"Mathematical constant"},"syntax":"e","summary":{"zh":"自然指数函数的底数。","en":"The base of the natural exponential function."},"notes":{"zh":"e 是一个确定的正实数；此处表示精确数学常数，而非小数近似。","en":"e is a fixed positive real; this denotes the exact mathematical constant, not a decimal approximation."}},"pi":{"kind":{"zh":"数学常数","en":"Mathematical constant"},"syntax":"pi","summary":{"zh":"圆周率 π。","en":"The constant π."},"notes":{"zh":"π 是一个确定的正实数；例如 sin(pi) = 0。","en":"π is a fixed positive real; for example, sin(pi) = 0."}},"literal:number":{"kind":{"zh":"精确数值","en":"Exact numeral"},"syntax":"2; 2.5","summary":{"zh":"数值字面量表示一个确定的精确数。","en":"A numeral denotes a specific exact number."},"notes":{"zh":"整数和有限小数按精确值读取；例如 2.5 = 5/2，而不是浮点近似。","en":"Integers and finite decimals are read exactly; for example, 2.5 = 5/2 rather than a floating-point approximation."}},"obj":{"kind":{"zh":"对象类别","en":"Object category"},"syntax":"obj","summary":{"zh":"数学对象的通用类别名。","en":"A general category name for mathematical objects."},"notes":{"zh":"obj 不表示“所有数学对象组成的集合”；使用集合归属时仍须给出一个实际集合。","en":"obj does not denote a set of all mathematical objects; membership still requires an actual set."}},"$":{"kind":{"zh":"谓词应用标记","en":"Predicate-application marker"},"syntax":"$P(arguments); x $in A","summary":{"zh":"标明一个谓词应用或内置数学关系。","en":"Mark a predicate application or builtin mathematical relation."},"notes":{"zh":"$P(...) 表达关于实参的命题，而不是返回数值的函数调用；是否成立仍需要证明。","en":"$P(...) is a proposition about its arguments, not a function call returning a numerical value. Its truth still requires evidence."}},"by enumerate finite_set":{"kind":{"zh":"有限枚举证明","en":"Finite enumeration proof"},"syntax":"by enumerate finite_set:\n    ? forall x S => condition\n    proof","summary":{"zh":"逐个验证有限集合中的对象，证明一个全称命题。","en":"Prove a universal statement by checking each element of a finite set."},"notes":{"zh":"集合必须可按该指令支持的方式枚举；验证一个例子不能替代检查全部元素。","en":"The carrier must be enumerable by this command. Checking one example does not establish every case."}},"set_diff":{"kind":{"zh":"集合运算符","en":"Set operator"},"role":"operator","syntax":"set_diff(A, B)","summary":{"zh":"集合 A 与 B 的对称差：只属于其中一个集合的元素组成的集合。","en":"The symmetric difference of A and B: elements belonging to exactly one of the two sets."},"notes":{"zh":"x ∈ set_diff(A,B) ⇔ (x ∈ A ∧ x ∉ B) ∨ (x ∈ B ∧ x ∉ A)。这不同于只取 A 中不属于 B 的元素的 set_minus(A,B)。","en":"x ∈ set_diff(A,B) iff (x ∈ A and x ∉ B) or (x ∈ B and x ∉ A). This differs from set_minus(A,B), which keeps only the elements of A outside B."}},"cart_dim":{"kind":{"zh":"已移除的语法","en":"Removed syntax"},"status":"removed","syntax":"cart_dim(...)","summary":{"zh":"该运算已从当前 Litex 语法中移除。","en":"This operation has been removed from current Litex syntax."},"notes":{"zh":"笛卡尔积作为集合本身没有唯一的构造维数。要描述坐标数和坐标域，应使用具体 cart 或 finite_seq 接口；读取分量须具备相应的完整定义域依据。","en":"A Cartesian set has no unique construction dimension. Use explicit cart or finite_seq interfaces for coordinate counts and domains; coordinate access needs the corresponding complete-domain evidence."}},"tuple_dim":{"kind":{"zh":"已移除的语法","en":"Removed syntax"},"status":"removed","syntax":"tuple_dim(...)","summary":{"zh":"该运算已从当前 Litex 语法中移除。","en":"This operation has been removed from current Litex syntax."},"notes":{"zh":"该访问器已移除；使用精确的 finite_seq 归属和完整定义域依据描述元组的坐标数。","en":"This accessor is removed; use exact finite_seq membership and complete-domain evidence to specify a tuple’s coordinate count."}},"proj":{"kind":{"zh":"已移除的语法","en":"Removed syntax"},"status":"removed","syntax":"proj(...)","summary":{"zh":"该运算已从当前 Litex 语法中移除。","en":"This operation has been removed from current Litex syntax."},"notes":{"zh":"该投影访问器已移除；笛卡尔积作为集合不保存其构造时的投影。应基于实际对象的函数或元组接口读取分量。","en":"This projection accessor is removed; a Cartesian set does not retain its construction projections. Access coordinates through the actual object’s function or tuple interface."}},"matrix":{"kind":{"zh":"矩阵空间","en":"Matrix space"},"syntax":"matrix(S, m, n)","summary":{"zh":"元素属于 S 的 m 行 n 列矩阵组成的集合。","en":"The set of m-by-n matrices with entries in S."},"notes":{"zh":"S 为集合，m,n ∈ ℕ，允许零维。矩阵按 (i,j) 取值，行、列指标分别为 1…m、1…n。","en":"S is a set and m,n ∈ ℕ; zero dimensions are allowed. A matrix is evaluated at (i,j), with row and column indices 1…m and 1…n."},"role":"operator"},"det":{"kind":{"zh":"行列式","en":"Determinant"},"syntax":"det(A, n)","summary":{"zh":"方阵 A 的行列式。","en":"The determinant of the square matrix A."},"notes":{"zh":"n ∈ ℕ，A ∈ matrix(C,n,n)，结果属于 ℂ。仅对方阵使用；实矩阵的行列式为实数。","en":"n ∈ ℕ and A ∈ matrix(C,n,n); the result lies in ℂ. The matrix must be square; a real matrix has a real determinant."}},"trace":{"kind":{"zh":"迹","en":"Trace"},"syntax":"trace(A, n)","summary":{"zh":"方阵 A 的对角元素之和。","en":"The sum of the diagonal entries of the square matrix A."},"notes":{"zh":"n ∈ ℕ，A ∈ matrix(C,n,n)。trace(A,n) = Σᵢ₌₁ⁿ A(i,i) ∈ ℂ。","en":"n ∈ ℕ and A ∈ matrix(C,n,n). trace(A,n) = Σᵢ₌₁ⁿ A(i,i) ∈ ℂ."}},"zero_matrix":{"kind":{"zh":"零矩阵","en":"Zero matrix"},"syntax":"zero_matrix(m, n)","summary":{"zh":"每个条目均为 0 的 m 行 n 列矩阵。","en":"The m-by-n matrix whose entries are all zero."},"notes":{"zh":"m,n ∈ ℕ，允许零维；结果属于 matrix(C,m,n)，在每个合法指标 (i,j) 上取值为 0。","en":"m,n ∈ ℕ; zero dimensions are allowed. The result lies in matrix(C,m,n) and takes value 0 at every admissible (i,j)."}},"identity_matrix":{"kind":{"zh":"单位矩阵","en":"Identity matrix"},"syntax":"identity_matrix(n)","summary":{"zh":"n 阶单位矩阵。","en":"The identity matrix of order n."},"notes":{"zh":"n ∈ ℕ；结果属于 matrix(C,n,n)。第 (i,j) 项在 i=j 时为 1，其余为 0。","en":"n ∈ ℕ; the result lies in matrix(C,n,n). Its (i,j) entry is 1 if i=j and 0 otherwise."}},"transpose":{"kind":{"zh":"转置","en":"Transpose"},"syntax":"transpose(A, m, n)","summary":{"zh":"交换矩阵的行指标和列指标。","en":"Interchange the row and column indices of a matrix."},"notes":{"zh":"m,n ∈ ℕ，A ∈ matrix(C,m,n)；结果属于 matrix(C,n,m)，其第 (i,j) 项为 A(j,i)，不取复共轭。","en":"m,n ∈ ℕ and A ∈ matrix(C,m,n). The result lies in matrix(C,n,m), with (i,j) entry A(j,i); no complex conjugation is taken."}},"conjugate_transpose":{"kind":{"zh":"共轭转置","en":"Conjugate transpose"},"syntax":"conjugate_transpose(A, m, n)","summary":{"zh":"先取复共轭，再交换行、列指标。","en":"Conjugate the entries and interchange row and column indices."},"notes":{"zh":"m,n ∈ ℕ，A ∈ matrix(C,m,n)；结果属于 matrix(C,n,m)，其第 (i,j) 项为 conj(A(j,i))。","en":"m,n ∈ ℕ and A ∈ matrix(C,m,n). The result lies in matrix(C,n,m), with (i,j) entry conj(A(j,i))."}},"matrix_add":{"kind":{"zh":"矩阵加法","en":"Matrix addition"},"syntax":"matrix_add(A, B, m, n)","summary":{"zh":"两个同型矩阵逐项相加。","en":"Add two matrices entry by entry."},"notes":{"zh":"m,n ∈ ℕ，A,B ∈ matrix(C,m,n)；结果仍在 matrix(C,m,n)，第 (i,j) 项为 A(i,j)+B(i,j)。","en":"m,n ∈ ℕ and A,B ∈ matrix(C,m,n). The result lies in matrix(C,m,n), with (i,j) entry A(i,j)+B(i,j)."}},"matrix_sub":{"kind":{"zh":"矩阵减法","en":"Matrix subtraction"},"syntax":"matrix_sub(A, B, m, n)","summary":{"zh":"两个同型矩阵逐项相减。","en":"Subtract two matrices entry by entry."},"notes":{"zh":"m,n ∈ ℕ，A,B ∈ matrix(C,m,n)；结果仍在 matrix(C,m,n)，第 (i,j) 项为 A(i,j)−B(i,j)。","en":"m,n ∈ ℕ and A,B ∈ matrix(C,m,n). The result lies in matrix(C,m,n), with (i,j) entry A(i,j)−B(i,j)."}},"matrix_scale":{"kind":{"zh":"矩阵数乘","en":"Scalar multiplication of a matrix"},"syntax":"matrix_scale(c, A, m, n)","summary":{"zh":"用复数 c 乘矩阵 A 的每个条目。","en":"Multiply every entry of A by the complex scalar c."},"notes":{"zh":"c ∈ ℂ，m,n ∈ ℕ，A ∈ matrix(C,m,n)；结果属于 matrix(C,m,n)，第 (i,j) 项为 c*A(i,j)。","en":"c ∈ ℂ, m,n ∈ ℕ and A ∈ matrix(C,m,n). The result lies in matrix(C,m,n), with (i,j) entry c*A(i,j)."}},"matrix_mul":{"kind":{"zh":"矩阵乘法","en":"Matrix multiplication"},"syntax":"matrix_mul(A, B, m, k, n)","summary":{"zh":"按行与列配对求和，构成矩阵乘积 AB。","en":"Form AB by pairing rows of A with columns of B."},"notes":{"zh":"m,k,n ∈ ℕ，A ∈ matrix(C,m,k)，B ∈ matrix(C,k,n)。结果属于 matrix(C,m,n)，第 (i,j) 项为 Σᵣ₌₁ᵏ A(i,r)*B(r,j)。","en":"m,k,n ∈ ℕ, A ∈ matrix(C,m,k) and B ∈ matrix(C,k,n). The result lies in matrix(C,m,n), with (i,j) entry Σᵣ₌₁ᵏ A(i,r)*B(r,j)."}},"matrix_apply":{"kind":{"zh":"矩阵作用于向量","en":"Matrix action on a vector"},"syntax":"matrix_apply(A, v, m, n)","summary":{"zh":"矩阵 A 与列向量 v 的乘积。","en":"The product of A with the column vector v."},"notes":{"zh":"m,n ∈ ℕ，A ∈ matrix(C,m,n)，v ∈ finite_seq(C,n)。结果属于 finite_seq(C,m)，第 i 项为 Σⱼ₌₁ⁿ A(i,j)*v(j)。","en":"m,n ∈ ℕ, A ∈ matrix(C,m,n) and v ∈ finite_seq(C,n). The result lies in finite_seq(C,m), with i-th entry Σⱼ₌₁ⁿ A(i,j)*v(j)."}},"matrix_power":{"kind":{"zh":"矩阵幂","en":"Matrix power"},"syntax":"matrix_power(A, n, p)","summary":{"zh":"方阵 A 的非负整数次幂。","en":"A nonnegative integer power of the square matrix A."},"notes":{"zh":"n,p ∈ ℕ，A ∈ matrix(C,n,n)。结果属于 matrix(C,n,n)；p=0 时为 identity_matrix(n)，p>0 时为 p 个 A 的矩阵乘积。","en":"n,p ∈ ℕ and A ∈ matrix(C,n,n). The result lies in matrix(C,n,n); exponent 0 gives identity_matrix(n), and a positive exponent gives the product of p copies of A."}},"matrix_inverse":{"kind":{"zh":"逆矩阵","en":"Inverse matrix"},"syntax":"matrix_inverse(A, n)","summary":{"zh":"可逆方阵 A 的逆。","en":"The inverse of an invertible square matrix A."},"notes":{"zh":"n ∈ ℕ，A ∈ matrix(C,n,n)，须已证明 det(A,n) ≠ 0。结果属于 matrix(C,n,n)，与 A 左乘、右乘均得 identity_matrix(n)。","en":"n ∈ ℕ, A ∈ matrix(C,n,n), and det(A,n) ≠ 0 must be established. The result lies in matrix(C,n,n); multiplying it by A on either side gives identity_matrix(n)."}},"matrix_rank":{"kind":{"zh":"矩阵的秩","en":"Matrix rank"},"syntax":"matrix_rank(A, m, n)","summary":{"zh":"矩阵 A 的秩。","en":"The rank of the matrix A."},"notes":{"zh":"m,n ∈ ℕ，A ∈ matrix(C,m,n)。秩属于 ℕ，数学上等于线性无关列的最大数量，亦等于线性无关行的最大数量。","en":"m,n ∈ ℕ and A ∈ matrix(C,m,n). The rank lies in ℕ; mathematically it is the maximum number of linearly independent columns, equivalently rows."}},"matrix_minor":{"kind":{"zh":"删行删列矩阵","en":"Deleted-row-and-column matrix"},"syntax":"matrix_minor(A, n, i, j)","summary":{"zh":"从方阵 A 删除第 i 行、第 j 列所得的矩阵。","en":"The matrix obtained by deleting row i and column j from A."},"notes":{"zh":"n ∈ ℕ+，A ∈ matrix(C,n,n)，i,j ∈ closed_range(1,n)。结果属于 matrix(C,n−1,n−1)。它是矩阵；对它取 det 才得到相应余子式的值。","en":"n ∈ ℕ+, A ∈ matrix(C,n,n) and i,j ∈ closed_range(1,n). The result lies in matrix(C,n−1,n−1). It is a matrix; its determinant is the corresponding minor value."}},"matrix_cofactor":{"kind":{"zh":"代数余子式","en":"Cofactor"},"syntax":"matrix_cofactor(A, n, i, j)","summary":{"zh":"方阵 A 的第 (i,j) 个代数余子式。","en":"The (i,j) cofactor of the square matrix A."},"notes":{"zh":"n ∈ ℕ+，A ∈ matrix(C,n,n)，i,j ∈ closed_range(1,n)。结果为 (−1)^(i+j)*det(matrix_minor(A,n,i,j),n−1)，属于 ℂ。","en":"n ∈ ℕ+, A ∈ matrix(C,n,n) and i,j ∈ closed_range(1,n). The value is (−1)^(i+j)*det(matrix_minor(A,n,i,j),n−1) ∈ ℂ."}},"matrix_adjugate":{"kind":{"zh":"伴随矩阵","en":"Adjugate matrix"},"syntax":"matrix_adjugate(A, n)","summary":{"zh":"方阵 A 的代数余子式矩阵的转置。","en":"The transpose of the cofactor matrix of A."},"notes":{"zh":"n ∈ ℕ，A ∈ matrix(C,n,n)。结果属于 matrix(C,n,n)；第 (i,j) 项为 A 的第 (j,i) 个代数余子式，不要求 A 可逆。","en":"n ∈ ℕ and A ∈ matrix(C,n,n). The result lies in matrix(C,n,n); its (i,j) entry is the (j,i) cofactor of A. Invertibility is not required."}},"diagonal_matrix":{"kind":{"zh":"对角矩阵","en":"Diagonal matrix"},"syntax":"diagonal_matrix(v, n)","summary":{"zh":"以向量 v 的各项为对角元素的方阵。","en":"The square matrix with the entries of v on its diagonal."},"notes":{"zh":"n ∈ ℕ，v ∈ finite_seq(C,n)；结果属于 matrix(C,n,n)。第 (i,i) 项为 v(i)，其余条目为 0。","en":"n ∈ ℕ and v ∈ finite_seq(C,n). The result lies in matrix(C,n,n); its (i,i) entry is v(i), and off-diagonal entries are 0."}},"outer_product":{"kind":{"zh":"向量外积矩阵","en":"Outer-product matrix"},"syntax":"outer_product(u, v, m, n)","summary":{"zh":"由两个向量的分量两两相乘构成矩阵。","en":"Form a matrix from all pairwise products of vector entries."},"notes":{"zh":"m,n ∈ ℕ，u ∈ finite_seq(C,m)，v ∈ finite_seq(C,n)。结果属于 matrix(C,m,n)，第 (i,j) 项为 u(i)*v(j)，这里不对 v 取共轭。","en":"m,n ∈ ℕ, u ∈ finite_seq(C,m) and v ∈ finite_seq(C,n). The result lies in matrix(C,m,n), with (i,j) entry u(i)*v(j). No conjugation of v is taken."}},"inner_product":{"kind":{"zh":"厄米内积","en":"Hermitian inner product"},"syntax":"inner_product(u, v, n)","summary":{"zh":"两个复向量的厄米内积，对第一个参数共轭线性。","en":"The Hermitian inner product of two complex vectors, conjugate-linear in the first argument."},"notes":{"zh":"n ∈ ℕ，u,v ∈ finite_seq(C,n)。inner_product(u,v,n) = Σⱼ₌₁ⁿ conj(u(j))*v(j) ∈ ℂ；实向量时退化为通常的点积。","en":"n ∈ ℕ and u,v ∈ finite_seq(C,n). inner_product(u,v,n) = Σⱼ₌₁ⁿ conj(u(j))*v(j) ∈ ℂ; for real vectors this is the usual dot product."}},"euclidean_norm":{"kind":{"zh":"欧几里得范数","en":"Euclidean norm"},"syntax":"euclidean_norm(v, n)","summary":{"zh":"向量各分量的模平方之和的非负平方根。","en":"The nonnegative square root of the sum of squared entry moduli."},"notes":{"zh":"n ∈ ℕ，v ∈ finite_seq(C,n)。结果为 sqrt(Σⱼ₌₁ⁿ C_abs(v(j))^2)，属于 ℝ 且非负。","en":"n ∈ ℕ and v ∈ finite_seq(C,n). The result is sqrt(Σⱼ₌₁ⁿ C_abs(v(j))^2), a nonnegative real number."}},"frobenius_norm":{"kind":{"zh":"弗罗贝尼乌斯范数","en":"Frobenius norm"},"syntax":"frobenius_norm(A, m, n)","summary":{"zh":"矩阵全部条目的模平方之和的非负平方根。","en":"The nonnegative square root of the sum of squared moduli of all entries."},"notes":{"zh":"m,n ∈ ℕ，A ∈ matrix(C,m,n)。结果为 sqrt(Σᵢ₌₁ᵐ Σⱼ₌₁ⁿ C_abs(A(i,j))^2)，属于 ℝ 且非负。","en":"m,n ∈ ℕ and A ∈ matrix(C,m,n). The result is sqrt(Σᵢ₌₁ᵐ Σⱼ₌₁ⁿ C_abs(A(i,j))^2), a nonnegative real number."}},"range":{"kind":{"zh":"整数范围","en":"Integer range"},"syntax":"range(a, b)","summary":{"zh":"半开整数范围：包含 a，不包含 b。","en":"The half-open integer range: include a and exclude b."},"notes":{"zh":"a,b ∈ ℤ。k ∈ range(a,b) ⇔ k ∈ ℤ 且 a ≤ k < b；a ≥ b 时为空集。例如 range(1,3) = {1,2}。","en":"a,b ∈ ℤ. k ∈ range(a,b) iff k ∈ ℤ and a ≤ k < b. The set is empty when a ≥ b; for example range(1,3) = {1,2}."},"role":"operator"},"closed_range":{"kind":{"zh":"闭整数范围","en":"Closed integer range"},"syntax":"closed_range(a, b)","summary":{"zh":"包含左右端点的整数范围。","en":"The integer range including both endpoints."},"notes":{"zh":"a,b ∈ ℤ。k ∈ closed_range(a,b) ⇔ k ∈ ℤ 且 a ≤ k ≤ b；a > b 时为空集。例如 closed_range(1,3) = {1,2,3}。","en":"a,b ∈ ℤ. k ∈ closed_range(a,b) iff k ∈ ℤ and a ≤ k ≤ b. The set is empty when a > b; for example closed_range(1,3) = {1,2,3}."},"role":"operator"},"finite_seq":{"kind":{"zh":"有限序列空间","en":"Finite sequence space"},"syntax":"finite_seq(S, n)","summary":{"zh":"取值于 S、长度为 n 的序列组成的集合。","en":"The set of length-n sequences with values in S."},"notes":{"zh":"S 为集合，n ∈ ℕ。序列是定义在 closed_range(1,n) 上的函数，指标从 1 开始；n=0 时定义域为空。cart_n(S,n) 是同一构造的另一种拼写。","en":"S is a set and n ∈ ℕ. A sequence is a function on closed_range(1,n), indexed from 1; length 0 has empty domain. cart_n(S,n) is another spelling of the same construction."},"role":"operator"},"cart_n":{"kind":{"zh":"有限序列空间","en":"Finite sequence space"},"syntax":"cart_n(S, n)","summary":{"zh":"与 finite_seq(S,n) 表示同一集合。","en":"The same set as finite_seq(S,n)."},"notes":{"zh":"S 为集合，n ∈ ℕ；元素是从 closed_range(1,n) 到 S 的函数，指标从 1 开始。n=0 允许空定义域。","en":"S is a set and n ∈ ℕ. Members are functions from closed_range(1,n) to S, indexed from 1. Length 0 is allowed."},"role":"operator"},"seq":{"kind":{"zh":"无限序列空间","en":"Infinite sequence space"},"syntax":"seq(S)","summary":{"zh":"以正整数为指标、取值于 S 的序列组成的集合。","en":"The set of sequences indexed by positive integers with values in S."},"notes":{"zh":"S 为集合。a ∈ seq(S) 表示 a 的定义域为 ℕ+，且对每个 n ∈ ℕ+ 都有 a(n) ∈ S；它不同于只有有限项的 finite_seq(S,n)。","en":"S is a set. a ∈ seq(S) means a has domain ℕ+ and a(n) ∈ S for every positive integer n. This differs from the finite space finite_seq(S,n)."},"role":"operator"},"cart":{"kind":{"zh":"笛卡尔积","en":"Cartesian product"},"syntax":"cart(A, B, ...)","summary":{"zh":"各因子集合的元素按顺序组成的元组集合。","en":"The set of ordered tuples whose coordinates lie in the respective factors."},"notes":{"zh":"例如 p ∈ cart(A,B) 要求 p(1) ∈ A、p(2) ∈ B，并具有该二元组的完整坐标域。各因子可以不同；它不同于单个元组 (a,b)。","en":"For example, p ∈ cart(A,B) requires p(1) ∈ A and p(2) ∈ B, together with the complete coordinate domain of a pair. Factors may differ. This is a set, distinct from the individual tuple (a,b)."},"role":"operator"},"tuple":{"kind":{"zh":"元组","en":"Tuple"},"syntax":"tuple(a, b, ...)","summary":{"zh":"按给定顺序记录对象的有限元组。","en":"A finite ordered tuple of the given objects."},"notes":{"zh":"也可写 (a,b)。坐标从 1 开始：若 p=(a,b)，则 p(1)=a、p(2)=b。元组保留顺序和重复项；它不同于集合 {a,b}。","en":"A pair may also be written (a,b). Coordinates start at 1: p=(a,b) has p(1)=a and p(2)=b. Tuples preserve order and repetition, unlike sets {a,b}."},"role":"operator"},"index_cart":{"kind":{"zh":"指标笛卡尔积","en":"Indexed Cartesian product"},"syntax":"index_cart(I, S, g)","summary":{"zh":"从每个指标 i 对应的集合 g(i) 中选取一个元素所构成的函数集合。","en":"The set of functions choosing an element of g(i) for each index i."},"notes":{"zh":"当前接口要求 I、S 均为非空集合，g ∈ fn(i I) S，且各 g(i) 为集合。其元素 f 的定义域为 I，并满足对每个 i ∈ I 有 f(i) ∈ g(i)。S 是集合族的载体；乘积本身未必非空。","en":"The current interface requires nonempty sets I and S, with g ∈ fn(i I) S and each g(i) a set. A member f has domain I and satisfies f(i) ∈ g(i) for every i ∈ I. S carries the family; the product itself need not be nonempty."},"role":"operator"},"obj:list_set":{"kind":{"zh":"列举集合","en":"Set by enumeration"},"syntax":"{a, b, ...}","summary":{"zh":"由列出的对象组成的有限集合。","en":"The finite set consisting of the listed objects."},"notes":{"zh":"x 属于此集合当且仅当 x 等于其中某一项；{} 为空集。当前列举语法要求各项有定义且两两不相等，重复项或尚不能排除相等的项不会自动合并。","en":"An object belongs exactly when it equals a listed entry; {} is the empty set. The current syntax requires well-defined, pairwise distinct entries; duplicates or entries not established distinct are not silently merged."},"role":"operator"},"obj:set_builder":{"kind":{"zh":"限定集合","en":"Set comprehension"},"syntax":"{x S: condition, ...}","summary":{"zh":"从集合 S 中取出满足全部所列条件的元素。","en":"The subset of S satisfying all listed conditions."},"notes":{"zh":"x 只在花括号内绑定。y ∈ {x S: P(x)} ⇔ y ∈ S 且 P(y)；多个条件同时成立。它只能从指定的 S 中筛选，不能构造无范围的“所有对象”。","en":"The binder x is local to the braces. y ∈ {x S: P(x)} iff y ∈ S and P(y); multiple conditions are conjunctive. Comprehension selects from a specified carrier S, not an unrestricted collection of all objects."},"role":"operator"},"fn_range":{"kind":{"zh":"函数的像集","en":"Image of a function"},"syntax":"fn_range(f)","summary":{"zh":"函数 f 在其完整定义域上取得的全部值组成的集合。","en":"The set of all values attained by f on its complete domain."},"notes":{"zh":"须有 f 的完整函数接口，包括参数域与附加条件。y ∈ fn_range(f) 表示存在合法输入使 f 的值等于 y；像集可以严格小于声明的陪域。","en":"A complete function interface for f is required, including parameter domains and guards. y ∈ fn_range(f) means some admissible input is mapped to y; the image can be smaller than the declared codomain."},"role":"operator"},"preimage":{"kind":{"zh":"单点原像","en":"Fiber over a value"},"syntax":"preimage(f, y)","summary":{"zh":"f 取值为 y 的全部合法输入组成的集合。","en":"The set of all admissible inputs mapped to y by f."},"notes":{"zh":"须有 f 的完整函数接口。若 f 有一个参数，元素为输入对象 x；若有多个参数，元素为相应输入元组。原像保留各参数域及函数附加条件，并要求 f(x)=y；不要求 f 单射，集合可以为空。","en":"A complete function interface for f is required. Inputs are individual objects for a unary function and input tuples for a multi-argument function. Parameter domains and guards are retained, together with f(x)=y. Injectivity is not required; the fiber may be empty."},"role":"operator"},"preimage_set":{"kind":{"zh":"集合的原像","en":"Inverse image of a set"},"syntax":"preimage_set(f, Y)","summary":{"zh":"f 的值属于 Y 的全部合法输入组成的集合。","en":"The set of all admissible inputs whose images under f lie in Y."},"notes":{"zh":"Y 为集合，须有 f 的完整函数接口。x ∈ preimage_set(f,Y) ⇔ x 满足 f 的参数域与附加条件，且 f(x) ∈ Y。多参数输入用元组表示；不要求 f 可逆。","en":"Y is a set and f must have a complete function interface. x ∈ preimage_set(f,Y) iff x satisfies f’s parameter domains and guards, and f(x) ∈ Y. Multiple inputs are represented by tuples; invertibility is not required."},"role":"operator"},"compose":{"kind":{"zh":"函数复合","en":"Function composition"},"syntax":"compose(g, f)","summary":{"zh":"先应用 f，再应用 g 的复合函数。","en":"The composite function applying f first, then g."},"notes":{"zh":"一元 f 时，compose(g,f)(x)=g(f(x))；多参数时保留 f 的全部输入参数。须有两个函数的完整接口；外层 g 为一元函数，内层 f 至少有一个参数。对 f 的合法输入，f 的值还须满足 g 的参数域与附加条件。","en":"For unary f, compose(g,f)(x)=g(f(x)); for multiple arguments, all input parameters of f are retained. Both functions need complete interfaces. The outer function g is unary; the inner f has at least one argument. For each admissible input of f, its output must satisfy g’s domain and guards."}},"sum":{"kind":{"zh":"求和","en":"Finite sum"},"syntax":"sum(a, b, f)","summary":{"zh":"对闭整数范围 a…b 上的 f(k) 求和。","en":"The sum of f(k) over the closed integer range a…b."},"notes":{"zh":"a,b ∈ ℤ，须有 a ≤ b。f 为一元函数，在每个所用整数上有定义，取值属于 ℂ；两端均包含。例如 sum(1,3,f) = f(1) + f(2) + f(3)。","en":"a,b ∈ ℤ and a ≤ b is required. The unary f must be defined at every used integer and have values in ℂ. Both endpoints are included; sum(1,3,f) = f(1) + f(2) + f(3)."}},"product":{"kind":{"zh":"求积","en":"Finite product"},"syntax":"product(a, b, f)","summary":{"zh":"对闭整数范围 a…b 上的 f(k) 求积。","en":"The product of f(k) over the closed integer range a…b."},"notes":{"zh":"a,b ∈ ℤ，须有 a ≤ b。f 为一元函数，在每个所用整数上有定义，取值属于 ℂ；两端均包含。例如 product(1,3,f) = f(1) * f(2) * f(3)。","en":"a,b ∈ ℤ and a ≤ b is required. The unary f must be defined at every used integer and have values in ℂ. Both endpoints are included; product(1,3,f) = f(1) * f(2) * f(3)."}},"finite_set_sum":{"kind":{"zh":"有限集合上的求和","en":"Sum over a finite set"},"syntax":"finite_set_sum(S, f)","summary":{"zh":"对有限集合 S 中每个元素的函数值求和。","en":"The sum of f(x) over all elements x of the finite set S."},"notes":{"zh":"须证明 S 有限；f 为一元函数，在 S 上有定义且取值属于 ℂ。每个集合元素只计一次；结果不依赖枚举顺序。","en":"Finiteness of S must be established. The unary f must be defined on S and have values in ℂ. Each set element is counted once; the result is independent of enumeration order."}},"finite_set_product":{"kind":{"zh":"有限集合上的求积","en":"Product over a finite set"},"syntax":"finite_set_product(S, f)","summary":{"zh":"对有限集合 S 中每个元素的函数值求积。","en":"The product of f(x) over all elements x of the finite set S."},"notes":{"zh":"须证明 S 有限；f 为一元函数，在 S 上有定义且取值属于 ℂ。每个集合元素只计一次；结果不依赖枚举顺序。","en":"Finiteness of S must be established. The unary f must be defined on S and have values in ℂ. Each set element is counted once; the result is independent of enumeration order."}},"reduce":{"kind":{"zh":"有序折叠","en":"Ordered fold"},"syntax":"reduce(a, b, f, op, seed)","summary":{"zh":"从初值 seed 出发，按递增整数指标依次用 op 累积 f 的值。","en":"Starting from seed, accumulate the values of f using op in increasing integer order."},"notes":{"zh":"a,b ∈ ℤ。op 具有同一载体上的接口 fn(u,v T) T，seed ∈ T，f 的返回集合为 T，且 f 在所有所用指标上有定义。依次计算 op(seed,f(a))、op(上一步,f(a+1))，直到 b；a>b 时返回 seed。不要求 op 交换。","en":"a,b ∈ ℤ. The operation has homogeneous signature fn(u,v T) T; seed ∈ T; f returns T and is defined at every used index. Compute op(seed,f(a)), then op(the previous value,f(a+1)), through b. If a>b the result is seed. Commutativity is not required."}},"finite_set_reduce":{"kind":{"zh":"有限集合折叠","en":"Fold over a finite set"},"syntax":"finite_set_reduce(S, f, op, seed)","summary":{"zh":"用运算 op 从初值 seed 累积有限集合 S 上的函数值。","en":"Accumulate f(x) over the finite set S using op, starting from seed."},"notes":{"zh":"须证明 S 有限。op 的接口为 fn(u,v T) T，并须满足结合律与交换律；seed ∈ T，f 返回 T 且在 S 上有定义。这些条件保证结果不依赖枚举顺序；不另要求 seed 为单位元。","en":"S must be finite. The homogeneous operation fn(u,v T) T must be associative and commutative; seed ∈ T; f returns T and is defined on S. These conditions make the result independent of enumeration order. The seed need not be an identity element."}},"finite_set_size":{"kind":{"zh":"有限集合的基数","en":"Cardinality of a finite set"},"syntax":"finite_set_size(S)","summary":{"zh":"有限集合 S 的元素个数。","en":"The number of elements of the finite set S."},"notes":{"zh":"须证明 S 有限；结果属于 ℕ。空集的基数为 0，集合中每个不同元素只计一次。","en":"Finiteness of S must be established; the result lies in ℕ. The empty set has cardinality 0, and each distinct element is counted once."}},"finite_set_max":{"kind":{"zh":"有限集合的最大值","en":"Maximum of a finite set"},"syntax":"finite_set_max(S)","summary":{"zh":"非空有限实数集合 S 的最大元素。","en":"The greatest element of the nonempty finite real set S."},"notes":{"zh":"须证明 S 有限、非空且 S ⊆ ℝ。结果 m 属于 S，并满足对任意 x ∈ S，x ≤ m。空集不在此运算的定义域内。","en":"S must be finite, nonempty and a subset of ℝ. The result m belongs to S and satisfies x ≤ m for every x ∈ S. The operation is not defined on the empty set."}},"finite_set_min":{"kind":{"zh":"有限集合的最小值","en":"Minimum of a finite set"},"syntax":"finite_set_min(S)","summary":{"zh":"非空有限实数集合 S 的最小元素。","en":"The least element of the nonempty finite real set S."},"notes":{"zh":"须证明 S 有限、非空且 S ⊆ ℝ。结果 m 属于 S，并满足对任意 x ∈ S，x ≥ m。空集不在此运算的定义域内。","en":"S must be finite, nonempty and a subset of ℝ. The result m belongs to S and satisfies x ≥ m for every x ∈ S. The operation is not defined on the empty set."}},"lim":{"kind":{"zh":"实数列的极限","en":"Limit of a real sequence"},"syntax":"lim(a)","summary":{"zh":"已证明收敛的实数列 a 的唯一有限极限。","en":"The unique finite limit of a real sequence a whose convergence is established."},"notes":{"zh":"a 的完整指标域为 ℕ+，各项属于 ℝ。使用前须已有 has_seq_limit(a,L) 的证明，或证明存在这样的实数 L。写出 lim(a) 本身不会证明收敛；函数在点处的极限另用 fn_lim(f,x0)。","en":"The complete index domain is ℕ+ and all values are real. A proved has_seq_limit(a,L) candidate or existence of such a real L is required before selection. Writing lim(a) does not prove convergence; use fn_lim(f,x0) for a function limit at a point."}},"limsup":{"kind":{"zh":"实数列的有限上极限","en":"Finite upper limit of a real sequence"},"syntax":"limsup(a)","summary":{"zh":"实数列 a 的有限上极限。","en":"The finite upper limit of the real sequence a."},"notes":{"zh":"a 的完整指标域为 ℕ+，各项属于 ℝ；须先证明 has_seq_limsup(a,L) 或相应实数 L 的存在性。其条件包括：对每个 ε>0，充分靠后的项满足 a(n) < L+ε；并且任意尾部都有一项满足 L−ε < a(n)。此选择器不取 ±∞。","en":"The complete index domain is ℕ+ and values are real. A proved has_seq_limsup(a,L) candidate or existence of such a real L is required. For every ε>0, sufficiently late terms satisfy a(n) < L+ε, and every tail contains a term satisfying L−ε < a(n). This selector does not take values ±∞."}},"liminf":{"kind":{"zh":"实数列的有限下极限","en":"Finite lower limit of a real sequence"},"syntax":"liminf(a)","summary":{"zh":"实数列 a 的有限下极限。","en":"The finite lower limit of the real sequence a."},"notes":{"zh":"a 的完整指标域为 ℕ+，各项属于 ℝ；须先证明 has_seq_liminf(a,L) 或相应实数 L 的存在性。其条件包括：对每个 ε>0，充分靠后的项满足 L−ε < a(n)；并且任意尾部都有一项满足 a(n) < L+ε。此选择器不取 ±∞。","en":"The complete index domain is ℕ+ and values are real. A proved has_seq_liminf(a,L) candidate or existence of such a real L is required. For every ε>0, sufficiently late terms satisfy L−ε < a(n), and every tail contains a term satisfying a(n) < L+ε. This selector does not take values ±∞."}},"fn_lim":{"kind":{"zh":"函数极限","en":"Function limit"},"syntax":"fn_lim(f, x0)","summary":{"zh":"一元实函数 f 沿其定义域在 x → x0 时的唯一有限极限。","en":"The unique finite limit of the unary real function f along its domain as x → x0."},"notes":{"zh":"须有完整实函数接口及此方向的极限候选证明，或相应极限存在性证明；趋近方向须满足对应的聚点或无界性条件。有限点 x0 ∈ ℝ。取去心极限，不要求 f(x0) 有定义。","en":"A complete real-function interface and a proved limit candidate or existence in this direction are required. The approach must satisfy the corresponding accumulation or unboundedness conditions. The finite point x0 lies in ℝ. This is a punctured limit; f(x0) need not be defined."}},"lim_left":{"kind":{"zh":"左极限","en":"Left-hand limit"},"syntax":"lim_left(f, x0)","summary":{"zh":"一元实函数 f 沿其定义域在 x → x0− 时的唯一有限极限。","en":"The unique finite limit of the unary real function f along its domain as x → x0−."},"notes":{"zh":"须有完整实函数接口及此方向的极限候选证明，或相应极限存在性证明；趋近方向须满足对应的聚点或无界性条件。有限点 x0 ∈ ℝ。取去心极限，不要求 f(x0) 有定义。","en":"A complete real-function interface and a proved limit candidate or existence in this direction are required. The approach must satisfy the corresponding accumulation or unboundedness conditions. The finite point x0 lies in ℝ. This is a punctured limit; f(x0) need not be defined."}},"lim_right":{"kind":{"zh":"右极限","en":"Right-hand limit"},"syntax":"lim_right(f, x0)","summary":{"zh":"一元实函数 f 沿其定义域在 x → x0+ 时的唯一有限极限。","en":"The unique finite limit of the unary real function f along its domain as x → x0+."},"notes":{"zh":"须有完整实函数接口及此方向的极限候选证明，或相应极限存在性证明；趋近方向须满足对应的聚点或无界性条件。有限点 x0 ∈ ℝ。取去心极限，不要求 f(x0) 有定义。","en":"A complete real-function interface and a proved limit candidate or existence in this direction are required. The approach must satisfy the corresponding accumulation or unboundedness conditions. The finite point x0 lies in ℝ. This is a punctured limit; f(x0) need not be defined."}},"lim_pos_inf":{"kind":{"zh":"正无穷处的极限","en":"Limit at positive infinity"},"syntax":"lim_pos_inf(f)","summary":{"zh":"一元实函数 f 沿其定义域在 x → +∞ 时的唯一有限极限。","en":"The unique finite limit of the unary real function f along its domain as x → +∞."},"notes":{"zh":"须有完整实函数接口及此方向的极限候选证明，或相应极限存在性证明；趋近方向须满足对应的聚点或无界性条件。沿定义域向对应无穷方向趋近，结果仍是有限实数。","en":"A complete real-function interface and a proved limit candidate or existence in this direction are required. The approach must satisfy the corresponding accumulation or unboundedness conditions. Approach through the domain in the indicated infinite direction; the result is still a finite real number."}},"lim_neg_inf":{"kind":{"zh":"负无穷处的极限","en":"Limit at negative infinity"},"syntax":"lim_neg_inf(f)","summary":{"zh":"一元实函数 f 沿其定义域在 x → −∞ 时的唯一有限极限。","en":"The unique finite limit of the unary real function f along its domain as x → −∞."},"notes":{"zh":"须有完整实函数接口及此方向的极限候选证明，或相应极限存在性证明；趋近方向须满足对应的聚点或无界性条件。沿定义域向对应无穷方向趋近，结果仍是有限实数。","en":"A complete real-function interface and a proved limit candidate or existence in this direction are required. The approach must satisfy the corresponding accumulation or unboundedness conditions. Approach through the domain in the indicated infinite direction; the result is still a finite real number."}},"derivative":{"kind":{"zh":"实函数在点处的导数","en":"Derivative of a real function at a point"},"syntax":"derivative(f, x0)","summary":{"zh":"一元实函数 f 在 x0 处的有限导数。","en":"The finite derivative of a unary real function f at x0."},"notes":{"zh":"须有完整实函数接口，x0 ∈ ℝ 且 f(x0) 有定义，并先证明 has_derivative_at(f,x0,d) 或相应导数存在性。导数由 (f(x)−f(x0))/(x−x0) 的极限刻画；只写 derivative 不会建立可导性。 该导数定义还要求 x0 为函数定义域的内点。","en":"A complete real-function interface is required; x0 ∈ ℝ and f(x0) must be defined. A proved has_derivative_at(f,x0,d) candidate or existence is required. The derivative is characterized by the limit of (f(x)−f(x0))/(x−x0); writing derivative does not establish differentiability. The derivative definition also requires x0 to be an interior point of the function domain."}},"integral":{"kind":{"zh":"定向黎曼积分","en":"Oriented Riemann integral"},"syntax":"integral(f, a, b)","summary":{"zh":"实函数 f 从 a 到 b 的有限黎曼积分。","en":"The finite Riemann integral of the real function f from a to b."},"notes":{"zh":"a,b ∈ ℝ，须有完整实函数接口，且 [min(a,b),max(a,b)] 包含在其定义域内。使用前须证明对应积分值或积分存在性。交换端点使积分变号；a=b 时积分为 0，仍须满足该点的定义域条件。","en":"a,b ∈ ℝ. A complete real-function interface is required, with [min(a,b),max(a,b)] contained in its domain. The integral value or its existence must be proved before selection. Reversing endpoints changes the sign; equal endpoints give 0, while domain conditions at that point still apply."}},"sup":{"kind":{"zh":"有限实上确界","en":"Finite real supremum"},"syntax":"sup(S)","summary":{"zh":"非空实数集合 S 的上确界。","en":"The supremum of the nonempty real set S."},"notes":{"zh":"须证明 S ⊆ ℝ，并已有 is_real_least_upper_bound(S,L) 的证书，或相应实数 L 的存在性；这要求集合非空且在对应方向有界。结果是最紧的上界，不要求它属于 S；不取 ±∞。","en":"S ⊆ ℝ and a proved is_real_least_upper_bound(S,L) certificate, or existence of such a real L, are required. The certificate entails nonemptiness and boundedness in the corresponding direction. The result is the tightest upper bound; it need not belong to S and is not ±∞."}},"inf":{"kind":{"zh":"有限实下确界","en":"Finite real infimum"},"syntax":"inf(S)","summary":{"zh":"非空实数集合 S 的下确界。","en":"The infimum of the nonempty real set S."},"notes":{"zh":"须证明 S ⊆ ℝ，并已有 is_real_greatest_lower_bound(S,L) 的证书，或相应实数 L 的存在性；这要求集合非空且在对应方向有界。结果是最紧的下界，不要求它属于 S；不取 ±∞。","en":"S ⊆ ℝ and a proved is_real_greatest_lower_bound(S,L) certificate, or existence of such a real L, are required. The certificate entails nonemptiness and boundedness in the corresponding direction. The result is the tightest lower bound; it need not belong to S and is not ±∞."}},"fn_preimage":{"kind":{"zh":"原像见证指令的一部分","en":"Part of a preimage-witness command"},"syntax":"have by fn_preimage: x from y $in fn_range(f)","summary":{"zh":"从已知的函数像集归属中引入原像见证。","en":"Introduce a preimage witness from established membership in a function image."},"notes":{"zh":"先证明 y ∈ fn_range(f)，再引入满足函数参数域与附加条件、且 f(x)=y 的输入 x。fn_preimage 不是可单独调用的对象函数；完整指令是 have by fn_preimage。","en":"First establish y ∈ fn_range(f), then introduce an input x satisfying the function’s domain and guards with f(x)=y. fn_preimage is not a standalone object function; it is part of have by fn_preimage."},"role":"keyword"},"obj:interval:open_open":{"kind":{"zh":"实数区间","en":"Real interval"},"syntax":"'(a, b)","summary":{"zh":"满足两端不等式的实数组成的集合。","en":"The set of real numbers satisfying the two endpoint inequalities."},"notes":{"zh":"a,b ∈ ℝ。x 属于该区间 ⇔ x ∈ ℝ 且 a < x < b。方括号包含相应端点，圆括号不包含；这是连续实数区间，不是整数范围 range(a,b)。","en":"a,b ∈ ℝ. Membership is equivalent to x ∈ ℝ and a < x < b. A square bracket includes its endpoint; a round bracket excludes it. This is a real interval, distinct from the integer range range(a,b)."}},"obj:interval:open_closed":{"kind":{"zh":"实数区间","en":"Real interval"},"syntax":"'(a, b]","summary":{"zh":"满足两端不等式的实数组成的集合。","en":"The set of real numbers satisfying the two endpoint inequalities."},"notes":{"zh":"a,b ∈ ℝ。x 属于该区间 ⇔ x ∈ ℝ 且 a < x ≤ b。方括号包含相应端点，圆括号不包含；这是连续实数区间，不是整数范围 range(a,b)。","en":"a,b ∈ ℝ. Membership is equivalent to x ∈ ℝ and a < x ≤ b. A square bracket includes its endpoint; a round bracket excludes it. This is a real interval, distinct from the integer range range(a,b)."}},"obj:interval:closed_open":{"kind":{"zh":"实数区间","en":"Real interval"},"syntax":"'[a, b)","summary":{"zh":"满足两端不等式的实数组成的集合。","en":"The set of real numbers satisfying the two endpoint inequalities."},"notes":{"zh":"a,b ∈ ℝ。x 属于该区间 ⇔ x ∈ ℝ 且 a ≤ x < b。方括号包含相应端点，圆括号不包含；这是连续实数区间，不是整数范围 range(a,b)。","en":"a,b ∈ ℝ. Membership is equivalent to x ∈ ℝ and a ≤ x < b. A square bracket includes its endpoint; a round bracket excludes it. This is a real interval, distinct from the integer range range(a,b)."}},"obj:interval:closed_closed":{"kind":{"zh":"实数区间","en":"Real interval"},"syntax":"'[a, b]","summary":{"zh":"满足两端不等式的实数组成的集合。","en":"The set of real numbers satisfying the two endpoint inequalities."},"notes":{"zh":"a,b ∈ ℝ。x 属于该区间 ⇔ x ∈ ℝ 且 a ≤ x ≤ b。方括号包含相应端点，圆括号不包含；这是连续实数区间，不是整数范围 range(a,b)。","en":"a,b ∈ ℝ. Membership is equivalent to x ∈ ℝ and a ≤ x ≤ b. A square bracket includes its endpoint; a round bracket excludes it. This is a real interval, distinct from the integer range range(a,b)."}},"obj:ray:lower_open":{"kind":{"zh":"实数射线","en":"Real ray"},"syntax":"'(a,)","summary":{"zh":"只在一侧有有限端点的实数集合。","en":"A real interval with one finite endpoint and one unbounded side."},"notes":{"zh":"a ∈ ℝ。x 属于该射线 ⇔ x ∈ ℝ 且 a < x。省略端点的一侧无界，不表示集合包含无穷这个元素。","en":"a ∈ ℝ. Membership is equivalent to x ∈ ℝ and a < x. The omitted endpoint indicates an unbounded side, not an infinite element of the set."}},"obj:ray:lower_closed":{"kind":{"zh":"实数射线","en":"Real ray"},"syntax":"'[a,)","summary":{"zh":"只在一侧有有限端点的实数集合。","en":"A real interval with one finite endpoint and one unbounded side."},"notes":{"zh":"a ∈ ℝ。x 属于该射线 ⇔ x ∈ ℝ 且 a ≤ x。省略端点的一侧无界，不表示集合包含无穷这个元素。","en":"a ∈ ℝ. Membership is equivalent to x ∈ ℝ and a ≤ x. The omitted endpoint indicates an unbounded side, not an infinite element of the set."}},"obj:ray:upper_open":{"kind":{"zh":"实数射线","en":"Real ray"},"syntax":"'(,a)","summary":{"zh":"只在一侧有有限端点的实数集合。","en":"A real interval with one finite endpoint and one unbounded side."},"notes":{"zh":"a ∈ ℝ。x 属于该射线 ⇔ x ∈ ℝ 且 x < a。省略端点的一侧无界，不表示集合包含无穷这个元素。","en":"a ∈ ℝ. Membership is equivalent to x ∈ ℝ and x < a. The omitted endpoint indicates an unbounded side, not an infinite element of the set."}},"obj:ray:upper_closed":{"kind":{"zh":"实数射线","en":"Real ray"},"syntax":"'(,a]","summary":{"zh":"只在一侧有有限端点的实数集合。","en":"A real interval with one finite endpoint and one unbounded side."},"notes":{"zh":"a ∈ ℝ。x 属于该射线 ⇔ x ∈ ℝ 且 x ≤ a。省略端点的一侧无界，不表示集合包含无穷这个元素。","en":"a ∈ ℝ. Membership is equivalent to x ∈ ℝ and x ≤ a. The omitted endpoint indicates an unbounded side, not an infinite element of the set."}},"obj:call":{"kind":{"zh":"应用","en":"Application"},"syntax":"f(arguments)","summary":{"zh":"将实参交给可调用的对象，取得对应的值。","en":"Apply a callable object to arguments to obtain its value."},"notes":{"zh":"函数实参须满足该函数的参数域及附加条件；元组和有限序列用从 1 开始的指标取分量。连续的调用 f(a)(b) 依次使用前一次调用的结果；应用本身不表示某个关于结果的事实已获证明。","en":"Function arguments must satisfy the declared domains and guards. Tuples and finite sequences use indices starting at 1 to select entries. In f(a)(b), the second call applies the value returned by the first. An application alone does not prove a proposition about its result."}},"obj:field":{"kind":{"zh":"结构字段访问","en":"Structure field access"},"syntax":"object.field","summary":{"zh":"取出结构对象中由字段名指定的分量。","en":"Select the component named by a field of a structure object."},"notes":{"zh":"对象须属于相应的结构类型；字段的类型与约束由该结构定义确定。p.x 访问字段 x；这不同于使用点号作乘法，也不是引入一个新的独立对象。","en":"The object must have the corresponding structure type. The structure definition determines the field’s type and constraints. p.x selects its x field; the dot is not multiplication, and the access introduces no new independent object."}},"obj:struct_type":{"kind":{"zh":"结构类型","en":"Structure type"},"syntax":"&Structure; &Structure<arguments>","summary":{"zh":"满足指定结构的字段域与约束的对象组成的类型。","en":"The type of objects satisfying the fields and constraints of the specified structure."},"notes":{"zh":"& 引用一个已定义的结构类型；带参数的结构先代入类型参数，再使用各字段的要求。声明 p &Point 规定 p 的结构接口，p.x 则访问其字段。","en":"The & prefix refers to a defined structure type. A parameterized structure substitutes its type arguments before using the field requirements. A declaration p &Point specifies p’s structure interface; p.x selects a field."}},"obj:template":{"kind":{"zh":"模板实例","en":"Template instance"},"syntax":"\\Template<arguments>","summary":{"zh":"将实参代入模板，取得对应的实例对象。","en":"Substitute arguments into a template to obtain its instance object."},"notes":{"zh":"须满足模板参数的类型及附加条件，再使用实例中定义的字段或接口。反斜杠引入模板实例，尖括号中的对象是实参；不同实参的实例不会仅因使用同一模板而被视为相等。","en":"The template arguments must satisfy the declared types and guards before the instance fields or interfaces are used. A backslash introduces the instance and angle brackets contain its arguments. Instances with different arguments are not identified merely because they use the same template."}},"obj:anonymous_fn":{"kind":{"zh":"函数值","en":"Function value"},"syntax":"fn(x A: conditions) B {expression}","summary":{"zh":"用参数接口与取值表达式给出一个具体函数。","en":"Specify a function by its parameter interface and value expression."},"notes":{"zh":"参数在函数体内绑定。对满足参数域 A 和附加条件的输入 x，函数取给定表达式的值，该值须属于 B。省略花括号中的表达式时，fn(x A) B 表示函数空间，而不是一个指定的函数值。","en":"Parameters are bound inside the function body. For inputs x satisfying A and the guards, the value is the given expression and must belong to B. Without a body, fn(x A) B denotes a function space rather than a specified function value."}},"lim_multi_at":{"kind":{"zh":"多元实值极限","en":"Multivariable real limit"},"syntax":"lim_multi_at(f, p, n)","summary":{"zh":"取 f 在 p 处沿其实际定义域趋近的实数极限。","en":"Select the real limit of f at p along its actual domain."},"notes":{"zh":"n ∈ ℕ+；f 是具有完整声明的单参数函数，实际定义域 D ⊆ ℝⁿ，值域包含于 ℝ。p ∈ ℝⁿ 且是 D 的聚点；不要求 p ∈ D。结果 L 满足 f(x) → L（x ∈ D，x → p，x ≠ p）。结果属于 ℝ。使用前须已有 has_multi_limit_at 的候选值证明或存在性证明；写出此运算本身不会证明存在性。设 bowl(x)=x(1)^2+x(2)^2，x∈ℝ²。例：lim_multi_at(bowl,(1,2),2)=5。","en":"n ∈ ℕ+. f is a unary function with a complete declared signature, actual domain D ⊆ ℝⁿ and codomain contained in ℝ. p ∈ ℝⁿ must be an accumulation point of D; p need not belong to D. The result L satisfies f(x) → L as x ∈ D approaches p with x ≠ p. The result belongs to ℝ. A proved has_multi_limit_at candidate or existence is required before selection; writing the selector does not prove existence. Let bowl(x)=x(1)^2+x(2)^2 for x∈ℝ². Example: lim_multi_at(bowl,(1,2),2)=5."}},"lim_vector_at":{"kind":{"zh":"多元向量极限","en":"Multivariable vector limit"},"syntax":"lim_vector_at(F, p, n, m)","summary":{"zh":"取 F 在 p 处的向量极限，以欧几里得范数衡量趋近。","en":"Select the vector limit of F at p, measured in Euclidean norm."},"notes":{"zh":"n,m ∈ ℕ+；F 是具有完整声明的单参数函数，实际定义域 D ⊆ ℝⁿ，值域包含于 ℝᵐ。p ∈ ℝⁿ 且是 D 的聚点；不要求 p ∈ D。结果 L 满足 ‖F(x)−L‖ → 0（x ∈ D，x → p，x ≠ p）。结果属于 ℝᵐ。使用前须已有 has_vector_limit_at 的候选值证明或存在性证明；写出此运算本身不会证明存在性。设 field(x)=(x(1),x(2),x(3))，x∈ℝ³。例：lim_vector_at(field,(1,2,3),3,3)(2)=2。","en":"n,m ∈ ℕ+. F is a unary function with a complete declared signature, actual domain D ⊆ ℝⁿ and codomain contained in ℝᵐ. p ∈ ℝⁿ must be an accumulation point of D; p need not belong to D. The result L satisfies ‖F(x)−L‖ → 0 as x ∈ D approaches p with x ≠ p. The result belongs to ℝᵐ. A proved has_vector_limit_at candidate or existence is required before selection; writing the selector does not prove existence. Let field(x)=(x(1),x(2),x(3)) for x∈ℝ³. Example: lim_vector_at(field,(1,2,3),3,3)(2)=2."}},"partial_derivative":{"kind":{"zh":"偏导数","en":"Partial derivative"},"syntax":"partial_derivative(f, p, n, i)","summary":{"zh":"取 f 在 p 处沿第 i 个坐标方向的偏导数。","en":"Select the partial derivative of f at p in coordinate i."},"notes":{"zh":"n ∈ ℕ+；f 是具有完整声明的单参数函数，实际定义域 D ⊆ ℝⁿ，值域包含于 ℝ。p ∈ D，i ∈ {1,…,n}；D 包含 p 沿该坐标方向的一段开区间。结果为 limₕ→₀ (f(p+h eᵢ)−f(p))/h。结果属于 ℝ。使用前须已有 has_partial_derivative_at 的候选值证明或存在性证明；写出此运算本身不会证明存在性。设 bowl(x)=x(1)^2+x(2)^2，x∈ℝ²。例：partial_derivative(bowl,(1,2),2,1)=2。","en":"n ∈ ℕ+. f is a unary function with a complete declared signature, actual domain D ⊆ ℝⁿ and codomain contained in ℝ. p ∈ D and i ∈ {1,…,n}; D contains an open coordinate segment through p in direction eᵢ. The result is limₕ→₀ (f(p+h eᵢ)−f(p))/h. The result belongs to ℝ. A proved has_partial_derivative_at candidate or existence is required before selection; writing the selector does not prove existence. Let bowl(x)=x(1)^2+x(2)^2 for x∈ℝ². Example: partial_derivative(bowl,(1,2),2,1)=2."}},"scalar_differential":{"kind":{"zh":"实值函数的全微分","en":"Scalar total differential"},"syntax":"scalar_differential(f, p, n)","summary":{"zh":"取实值函数在 p 处全微分的 1×n 实矩阵。","en":"Select the 1×n real matrix of the total differential of a scalar function at p."},"notes":{"zh":"n ∈ ℕ+；f 是具有完整声明的单参数函数，实际定义域 D ⊆ ℝⁿ，值域包含于 ℝ。p 为 D 的内点。矩阵 A 满足 f(p+h)−f(p)−A h = o(‖h‖)；A 是行矩阵，区别于梯度的 n 维向量。仅有各偏导数存在还不够。结果属于 matrix(R,1,n)。使用前须已有 has_scalar_differential_at 的候选值证明或存在性证明；写出此运算本身不会证明存在性。设 bowl(x)=x(1)^2+x(2)^2，x∈ℝ²。例：scalar_differential(bowl,(1,2),2)(1,1)=2。","en":"n ∈ ℕ+. f is a unary function with a complete declared signature, actual domain D ⊆ ℝⁿ and codomain contained in ℝ. p is an interior point of D. The row matrix A satisfies f(p+h)−f(p)−A h = o(‖h‖). It is distinct from the n-vector gradient. Existence of the coordinate partial derivatives alone is insufficient. The result belongs to matrix(R,1,n). A proved has_scalar_differential_at candidate or existence is required before selection; writing the selector does not prove existence. Let bowl(x)=x(1)^2+x(2)^2 for x∈ℝ². Example: scalar_differential(bowl,(1,2),2)(1,1)=2."}},"differential":{"kind":{"zh":"向量值函数的全微分","en":"Vector total differential"},"syntax":"differential(F, p, n, m)","summary":{"zh":"取向量值函数在 p 处全微分的 m×n 实矩阵。","en":"Select the m×n real matrix of the total differential of a vector-valued function at p."},"notes":{"zh":"n,m ∈ ℕ+；F 是具有完整声明的单参数函数，实际定义域 D ⊆ ℝⁿ，值域包含于 ℝᵐ。p 为 D 的内点。结果 A 满足 ‖F(p+h)−F(p)−A h‖/‖h‖ → 0；n 是输入维数，m 是输出维数，参数次序不可互换。结果属于 matrix(R,m,n)。使用前须已有 has_total_derivative_at 的候选值证明或存在性证明；写出此运算本身不会证明存在性。设 field(x)=(x(1),x(2),x(3))，x∈ℝ³。例：differential(field,(1,2,3),3,3)(2,2)=1。","en":"n,m ∈ ℕ+. F is a unary function with a complete declared signature, actual domain D ⊆ ℝⁿ and codomain contained in ℝᵐ. p is an interior point of D. The result A satisfies ‖F(p+h)−F(p)−A h‖/‖h‖ → 0. n is the input dimension and m the output dimension; their argument positions are fixed. The result belongs to matrix(R,m,n). A proved has_total_derivative_at candidate or existence is required before selection; writing the selector does not prove existence. Let field(x)=(x(1),x(2),x(3)) for x∈ℝ³. Example: differential(field,(1,2,3),3,3)(2,2)=1."}},"gradient_at":{"kind":{"zh":"梯度","en":"Gradient"},"syntax":"gradient_at(f, p, n)","summary":{"zh":"取由 f 在 p 处各坐标偏导数组成的 n 维实向量。","en":"Select the real n-vector of the coordinate partial derivatives of f at p."},"notes":{"zh":"n ∈ ℕ+；f 是具有完整声明的单参数函数，实际定义域 D ⊆ ℝⁿ，值域包含于 ℝ。p ∈ D。结果 g 的第 i 分量为 ∂ᵢf(p)，i=1,…,n。该接口刻画各偏导数，不单独断言全可微。结果属于 ℝⁿ。使用前须已有 has_gradient_at 的候选值证明或存在性证明；写出此运算本身不会证明存在性。设 bowl(x)=x(1)^2+x(2)^2，x∈ℝ²。例：gradient_at(bowl,(1,2),2)(2)=4。","en":"n ∈ ℕ+. f is a unary function with a complete declared signature, actual domain D ⊆ ℝⁿ and codomain contained in ℝ. p ∈ D. Component i of the result g is ∂ᵢf(p), for i=1,…,n. This interface characterizes coordinate partial derivatives and does not by itself assert total differentiability. The result belongs to ℝⁿ. A proved has_gradient_at candidate or existence is required before selection; writing the selector does not prove existence. Let bowl(x)=x(1)^2+x(2)^2 for x∈ℝ². Example: gradient_at(bowl,(1,2),2)(2)=4."}},"jacobian":{"kind":{"zh":"雅可比矩阵","en":"Jacobian matrix"},"syntax":"jacobian(F, p, n, m)","summary":{"zh":"取由 F 各分量的一阶偏导数组成的 m×n 实矩阵。","en":"Select the m×n real matrix of the first partial derivatives of the components of F."},"notes":{"zh":"n,m ∈ ℕ+；F 是具有完整声明的单参数函数，实际定义域 D ⊆ ℝⁿ，值域包含于 ℝᵐ。p ∈ D。结果 J 的第 r 行、第 c 列为 (∂F_r/∂x_c)(p)：行对应输出分量，列对应输入坐标。各条目存在不自动保证全可微。结果属于 matrix(R,m,n)。使用前须已有 has_jacobian_at 的候选值证明或存在性证明；写出此运算本身不会证明存在性。设 field(x)=(x(1),x(2),x(3))，x∈ℝ³。例：jacobian(field,(1,2,3),3,3)(1,2)=0。","en":"n,m ∈ ℕ+. F is a unary function with a complete declared signature, actual domain D ⊆ ℝⁿ and codomain contained in ℝᵐ. p ∈ D. Entry J(r,c) is (∂F_r/∂x_c)(p): rows index output components and columns index input coordinates. Existence of these entries does not automatically establish total differentiability. The result belongs to matrix(R,m,n). A proved has_jacobian_at candidate or existence is required before selection; writing the selector does not prove existence. Let field(x)=(x(1),x(2),x(3)) for x∈ℝ³. Example: jacobian(field,(1,2,3),3,3)(1,2)=0."}},"hessian":{"kind":{"zh":"海森矩阵","en":"Hessian matrix"},"syntax":"hessian(f, p, n)","summary":{"zh":"取由 f 的迭代二阶偏导数组成的 n×n 实矩阵。","en":"Select the n×n real matrix of the iterated second partial derivatives of f."},"notes":{"zh":"n ∈ ℕ+；f 是具有完整声明的单参数函数，实际定义域 D ⊆ ℝⁿ，值域包含于 ℝ。p ∈ D。条目 H(i,j) 先对第 i 坐标求偏导，再对第 j 坐标求偏导。此接口不自动断言 H 对称；交换次序需要额外条件。结果属于 matrix(R,n,n)。使用前须已有 has_hessian_at 的候选值证明或存在性证明；写出此运算本身不会证明存在性。设 bowl(x)=x(1)^2+x(2)^2，x∈ℝ²。例：hessian(bowl,(1,2),2)(1,2)=0。","en":"n ∈ ℕ+. f is a unary function with a complete declared signature, actual domain D ⊆ ℝⁿ and codomain contained in ℝ. p ∈ D. Entry H(i,j) differentiates first in coordinate i and then in coordinate j. Symmetry is not part of this interface; exchanging the order requires additional hypotheses. The result belongs to matrix(R,n,n). A proved has_hessian_at candidate or existence is required before selection; writing the selector does not prove existence. Let bowl(x)=x(1)^2+x(2)^2 for x∈ℝ². Example: hessian(bowl,(1,2),2)(1,2)=0."}},"divergence":{"kind":{"zh":"散度","en":"Divergence"},"syntax":"divergence(F, p, n)","summary":{"zh":"取实向量场在 p 处各对角偏导数之和。","en":"Select the sum of the diagonal partial derivatives of a real vector field at p."},"notes":{"zh":"n ∈ ℕ+；F 是具有完整声明的单参数函数，实际定义域 D ⊆ ℝⁿ，值域包含于 ℝⁿ。p ∈ D。结果为 Σᵢ₌₁ⁿ ∂ᵢFᵢ(p)；只要求所用对角偏导数存在，不另行要求全部雅可比条目或全微分存在。结果属于 ℝ。使用前须已有 has_divergence_at 的候选值证明或存在性证明；写出此运算本身不会证明存在性。设 field(x)=(x(1),x(2),x(3))，x∈ℝ³。例：divergence(field,(1,2,3),3)=3。","en":"n ∈ ℕ+. F is a unary function with a complete declared signature, actual domain D ⊆ ℝⁿ and codomain contained in ℝⁿ. p ∈ D. The result is Σᵢ₌₁ⁿ ∂ᵢFᵢ(p). Only the diagonal partial derivatives used in this sum are required; the full Jacobian or total differential is not an additional requirement. The result belongs to ℝ. A proved has_divergence_at candidate or existence is required before selection; writing the selector does not prove existence. Let field(x)=(x(1),x(2),x(3)) for x∈ℝ³. Example: divergence(field,(1,2,3),3)=3."}},"curl":{"kind":{"zh":"旋度","en":"Curl"},"syntax":"curl(F, p)","summary":{"zh":"取三维实向量场在 p 处的旋度。","en":"Select the curl of a three-dimensional real vector field at p."},"notes":{"zh":"F 是具有完整声明的单参数函数，实际定义域 D ⊆ ℝ³，值域包含于 ℝ³。p ∈ D。结果为 (∂₂F₃−∂₃F₂, ∂₃F₁−∂₁F₃, ∂₁F₂−∂₂F₁)(p)；要求这六个偏导数存在。维数固定为 3，不接受额外维数参数。结果属于 ℝ³。使用前须已有 has_curl_at 的候选值证明或存在性证明；写出此运算本身不会证明存在性。设 field(x)=(x(1),x(2),x(3))，x∈ℝ³。例：curl(field,(1,2,3))(1)=0。","en":"F is a unary function with a complete declared signature, actual domain D ⊆ ℝ³ and codomain contained in ℝ³. p ∈ D. The result is (∂₂F₃−∂₃F₂, ∂₃F₁−∂₁F₃, ∂₁F₂−∂₂F₁)(p), requiring those six partial derivatives. The dimension is fixed at 3; there is no dimension argument. The result belongs to ℝ³. A proved has_curl_at candidate or existence is required before selection; writing the selector does not prove existence. Let field(x)=(x(1),x(2),x(3)) for x∈ℝ³. Example: curl(field,(1,2,3))(1)=0."}},"laplacian":{"kind":{"zh":"拉普拉斯算子值","en":"Laplacian value"},"syntax":"laplacian(f, p, n)","summary":{"zh":"取实值函数在 p 处各同坐标二阶偏导数之和。","en":"Select the sum of the pure second partial derivatives of a real-valued function at p."},"notes":{"zh":"n ∈ ℕ+；f 是具有完整声明的单参数函数，实际定义域 D ⊆ ℝⁿ，值域包含于 ℝ。p ∈ D。结果为 Σᵢ₌₁ⁿ ∂ᵢ(∂ᵢf)(p)；要求这些同坐标二阶偏导数存在，不另行要求全部混合偏导数存在。结果属于 ℝ。使用前须已有 has_laplacian_at 的候选值证明或存在性证明；写出此运算本身不会证明存在性。设 bowl(x)=x(1)^2+x(2)^2，x∈ℝ²。例：laplacian(bowl,(1,2),2)=4。","en":"n ∈ ℕ+. f is a unary function with a complete declared signature, actual domain D ⊆ ℝⁿ and codomain contained in ℝ. p ∈ D. The result is Σᵢ₌₁ⁿ ∂ᵢ(∂ᵢf)(p). These pure second partial derivatives are required; existence of every mixed partial is not an additional requirement. The result belongs to ℝ. A proved has_laplacian_at candidate or existence is required before selection; writing the selector does not prove existence. Let bowl(x)=x(1)^2+x(2)^2 for x∈ℝ². Example: laplacian(bowl,(1,2),2)=4."}},"has_multi_limit_at":{"kind":{"zh":"多元实值极限关系","en":"Multivariable real-limit relation"},"syntax":"$has_multi_limit_at(f, p, n, L)","summary":{"zh":"断言 f 沿实际定义域趋近 p 时的极限为实数 L。","en":"Assert that f tends to the real value L along its actual domain at p."},"notes":{"zh":"n ∈ ℕ+；f 是具有完整声明的单参数函数，实际定义域 D ⊆ ℝⁿ，值域包含于 ℝ。p ∈ ℝⁿ 是 D 的聚点，L ∈ ℝ。∀ε>0，∃δ>0，∀x∈D：0<‖x−p‖<δ ⇒ |f(x)−L|<ε；不要求 p∈D 或 f(p)=L。设 bowl(x)=x(1)^2+x(2)^2，x∈ℝ²。例：$has_multi_limit_at(bowl,(1,2),2,5)。","en":"n ∈ ℕ+. f is a unary function with a complete declared signature, actual domain D ⊆ ℝⁿ and codomain contained in ℝ. p ∈ ℝⁿ is an accumulation point of D and L ∈ ℝ. For every ε>0 there is δ>0 such that x∈D and 0<‖x−p‖<δ imply |f(x)−L|<ε. Neither p∈D nor f(p)=L is required. Let bowl(x)=x(1)^2+x(2)^2 for x∈ℝ². Example: $has_multi_limit_at(bowl,(1,2),2,5)."}},"has_vector_limit_at":{"kind":{"zh":"多元向量极限关系","en":"Multivariable vector-limit relation"},"syntax":"$has_vector_limit_at(F, p, n, m, L)","summary":{"zh":"断言 F 在 p 处沿实际定义域的向量极限为 L。","en":"Assert that the vector limit of F along its actual domain at p is L."},"notes":{"zh":"n,m ∈ ℕ+；F 是具有完整声明的单参数函数，实际定义域 D ⊆ ℝⁿ，值域包含于 ℝᵐ。p ∈ ℝⁿ 是 D 的聚点，L ∈ ℝᵐ。∀ε>0，∃δ>0，∀x∈D：0<‖x−p‖<δ ⇒ ‖F(x)−L‖<ε；不要求 p∈D。输入与输出均使用欧几里得范数。设 field(x)=(x(1),x(2),x(3))，x∈ℝ³。例：$has_vector_limit_at(field,(1,2,3),3,3,(1,2,3))。","en":"n,m ∈ ℕ+. F is a unary function with a complete declared signature, actual domain D ⊆ ℝⁿ and codomain contained in ℝᵐ. p ∈ ℝⁿ is an accumulation point of D and L ∈ ℝᵐ. For every ε>0 there is δ>0 such that x∈D and 0<‖x−p‖<δ imply ‖F(x)−L‖<ε. p need not belong to D. Both norms are Euclidean. Let field(x)=(x(1),x(2),x(3)) for x∈ℝ³. Example: $has_vector_limit_at(field,(1,2,3),3,3,(1,2,3))."}},"is_multi_continuous_at":{"kind":{"zh":"多元实值连续性","en":"Multivariable real continuity"},"syntax":"$is_multi_continuous_at(f, p, n)","summary":{"zh":"断言实值函数 f 在其实际定义域中的 p 处连续。","en":"Assert that the real-valued function f is continuous at p in its actual domain."},"notes":{"zh":"n ∈ ℕ+；f 是具有完整声明的单参数函数，实际定义域 D ⊆ ℝⁿ，值域包含于 ℝ。p ∈ D。∀ε>0，∃δ>0，∀x∈D：‖x−p‖<δ ⇒ |f(x)−f(p)|<ε。这里使用 f(p)，不要求 p 是 D 的聚点；孤立点也可连续。设 bowl(x)=x(1)^2+x(2)^2，x∈ℝ²。例：$is_multi_continuous_at(bowl,(1,2),2)。","en":"n ∈ ℕ+. f is a unary function with a complete declared signature, actual domain D ⊆ ℝⁿ and codomain contained in ℝ. p ∈ D. For every ε>0 there is δ>0 such that x∈D and ‖x−p‖<δ imply |f(x)−f(p)|<ε. This uses f(p) and does not require p to be an accumulation point; continuity also applies at isolated domain points. Let bowl(x)=x(1)^2+x(2)^2 for x∈ℝ². Example: $is_multi_continuous_at(bowl,(1,2),2)."}},"is_vector_continuous_at":{"kind":{"zh":"多元向量连续性","en":"Multivariable vector continuity"},"syntax":"$is_vector_continuous_at(F, p, n, m)","summary":{"zh":"断言向量值函数 F 在其实际定义域中的 p 处连续。","en":"Assert that the vector-valued function F is continuous at p in its actual domain."},"notes":{"zh":"n,m ∈ ℕ+；F 是具有完整声明的单参数函数，实际定义域 D ⊆ ℝⁿ，值域包含于 ℝᵐ。p ∈ D。∀ε>0，∃δ>0，∀x∈D：‖x−p‖<δ ⇒ ‖F(x)−F(p)‖<ε。两个范数分别属于输入与输出欧几里得空间；不额外要求 p 是聚点。设 field(x)=(x(1),x(2),x(3))，x∈ℝ³。例：$is_vector_continuous_at(field,(1,2,3),3,3)。","en":"n,m ∈ ℕ+. F is a unary function with a complete declared signature, actual domain D ⊆ ℝⁿ and codomain contained in ℝᵐ. p ∈ D. For every ε>0 there is δ>0 such that x∈D and ‖x−p‖<δ imply ‖F(x)−F(p)‖<ε. The two norms belong to the input and output Euclidean spaces respectively. No accumulation-point condition is added. Let field(x)=(x(1),x(2),x(3)) for x∈ℝ³. Example: $is_vector_continuous_at(field,(1,2,3),3,3)."}},"has_partial_derivative_at":{"kind":{"zh":"偏导数关系","en":"Partial-derivative relation"},"syntax":"$has_partial_derivative_at(f, p, n, i, a)","summary":{"zh":"断言 f 在 p 处沿第 i 坐标的偏导数等于 a。","en":"Assert that the partial derivative of f at p in coordinate i equals a."},"notes":{"zh":"n ∈ ℕ+；f 是具有完整声明的单参数函数，实际定义域 D ⊆ ℝⁿ，值域包含于 ℝ。p ∈ D，i ∈ {1,…,n}，a ∈ ℝ。须存在 r>0 使 |h|<r 时 p+h eᵢ∈D，并有 (f(p+h eᵢ)−f(p))/h → a（h→0，h≠0）。单个偏导数的存在不保证全可微。设 bowl(x)=x(1)^2+x(2)^2，x∈ℝ²。例：$has_partial_derivative_at(bowl,(1,2),2,1,2)。","en":"n ∈ ℕ+. f is a unary function with a complete declared signature, actual domain D ⊆ ℝⁿ and codomain contained in ℝ. p ∈ D, i ∈ {1,…,n} and a ∈ ℝ. There must be r>0 with p+h eᵢ∈D for |h|<r, and (f(p+h eᵢ)−f(p))/h → a as h→0 with h≠0. One partial derivative does not establish total differentiability. Let bowl(x)=x(1)^2+x(2)^2 for x∈ℝ². Example: $has_partial_derivative_at(bowl,(1,2),2,1,2)."}},"has_second_partial_derivative_at":{"kind":{"zh":"迭代二阶偏导数关系","en":"Iterated second-partial relation"},"syntax":"$has_second_partial_derivative_at(f, p, n, i, j, a)","summary":{"zh":"断言先沿第 i 坐标、再沿第 j 坐标求偏导的结果在 p 处等于 a。","en":"Assert that differentiating first in coordinate i and then in coordinate j gives a at p."},"notes":{"zh":"n ∈ ℕ+；f 是具有完整声明的单参数函数，实际定义域 D ⊆ ℝⁿ，值域包含于 ℝ。p ∈ D，i,j ∈ {1,…,n}，a ∈ ℝ。须在包含 p 的局部子域 E⊆D 上有实值函数 g(q)=∂ᵢf(q)，并且 ∂ⱼg(p)=a。次序为 ∂ⱼ(∂ᵢf)(p)，不自动交换 i 与 j。设 oscillation(x)=sin(x(1)*x(2))，x∈ℝ²。例：$has_second_partial_derivative_at(oscillation,(0,2),2,1,2,1)。","en":"n ∈ ℕ+. f is a unary function with a complete declared signature, actual domain D ⊆ ℝⁿ and codomain contained in ℝ. p ∈ D, i,j ∈ {1,…,n} and a ∈ ℝ. There must be a subdomain E⊆D containing p and a real-valued function g on E with g(q)=∂ᵢf(q) for every q∈E and ∂ⱼg(p)=a. The order is ∂ⱼ(∂ᵢf)(p); exchanging i and j is not automatic. Let oscillation(x)=sin(x(1)*x(2)) for x∈ℝ². Example: $has_second_partial_derivative_at(oscillation,(0,2),2,1,2,1)."}},"has_scalar_differential_at":{"kind":{"zh":"实值全微分关系","en":"Scalar total-differential relation"},"syntax":"$has_scalar_differential_at(f, p, n, A)","summary":{"zh":"断言 1×n 实矩阵 A 表示 f 在 p 处的全微分。","en":"Assert that a 1×n real matrix A represents the total differential of f at p."},"notes":{"zh":"n ∈ ℕ+；f 是具有完整声明的单参数函数，实际定义域 D ⊆ ℝⁿ，值域包含于 ℝ。p 为 D 的内点，A ∈ matrix(R,1,n)。|f(p+h)−f(p)−A h|/‖h‖ → 0（h→0，h≠0）。这是统一的线性近似要求，强于仅有坐标偏导数存在。设 bowl(x)=x(1)^2+x(2)^2，x∈ℝ²。例：$has_scalar_differential_at(bowl,(1,2),2,fn(row closed_range(1,1),col closed_range(1,2)) R {(2,4)(col)})。","en":"n ∈ ℕ+. f is a unary function with a complete declared signature, actual domain D ⊆ ℝⁿ and codomain contained in ℝ. p is an interior point of D and A ∈ matrix(R,1,n). The remainder satisfies |f(p+h)−f(p)−A h|/‖h‖ → 0 as h→0 with h≠0. This uniform linear approximation is stronger than existence of coordinate partial derivatives alone. Let bowl(x)=x(1)^2+x(2)^2 for x∈ℝ². Example: $has_scalar_differential_at(bowl,(1,2),2,fn(row closed_range(1,1),col closed_range(1,2)) R {(2,4)(col)})."}},"has_total_derivative_at":{"kind":{"zh":"向量值全微分关系","en":"Vector total-differential relation"},"syntax":"$has_total_derivative_at(F, p, n, m, A)","summary":{"zh":"断言 m×n 实矩阵 A 表示 F 在 p 处的全微分。","en":"Assert that an m×n real matrix A represents the total differential of F at p."},"notes":{"zh":"n,m ∈ ℕ+；F 是具有完整声明的单参数函数，实际定义域 D ⊆ ℝⁿ，值域包含于 ℝᵐ。p 为 D 的内点，A ∈ matrix(R,m,n)。‖F(p+h)−F(p)−A h‖/‖h‖ → 0（h→0，h≠0）。行数 m 对应输出，列数 n 对应输入。设 field(x)=(x(1),x(2),x(3))，x∈ℝ³。例：$has_total_derivative_at(field,(1,2,3),3,3,identity_matrix(3))。","en":"n,m ∈ ℕ+. F is a unary function with a complete declared signature, actual domain D ⊆ ℝⁿ and codomain contained in ℝᵐ. p is an interior point of D and A ∈ matrix(R,m,n). The remainder satisfies ‖F(p+h)−F(p)−A h‖/‖h‖ → 0 as h→0 with h≠0. The m rows correspond to output components and the n columns to input coordinates. Let field(x)=(x(1),x(2),x(3)) for x∈ℝ³. Example: $has_total_derivative_at(field,(1,2,3),3,3,identity_matrix(3))."}},"is_multi_differentiable_at":{"kind":{"zh":"多元实值可微性","en":"Multivariable scalar differentiability"},"syntax":"$is_multi_differentiable_at(f, p, n)","summary":{"zh":"断言存在表示 f 在 p 处全微分的 1×n 实矩阵。","en":"Assert the existence of a 1×n real matrix representing the total differential of f at p."},"notes":{"zh":"n ∈ ℕ+；f 是具有完整声明的单参数函数，实际定义域 D ⊆ ℝⁿ，值域包含于 ℝ。等价于存在 A ∈ matrix(R,1,n) 使 has_scalar_differential_at(f,p,n,A)。因此 p 须为 D 的内点；仅有各偏导数存在不能推出此命题。设 bowl(x)=x(1)^2+x(2)^2，x∈ℝ²。例：$is_multi_differentiable_at(bowl,(1,2),2)。","en":"n ∈ ℕ+. f is a unary function with a complete declared signature, actual domain D ⊆ ℝⁿ and codomain contained in ℝ. This means that some A ∈ matrix(R,1,n) satisfies has_scalar_differential_at(f,p,n,A). In particular, p must be an interior point of D. Coordinate partial derivatives alone do not imply this proposition. Let bowl(x)=x(1)^2+x(2)^2 for x∈ℝ². Example: $is_multi_differentiable_at(bowl,(1,2),2)."}},"is_vector_differentiable_at":{"kind":{"zh":"多元向量值可微性","en":"Multivariable vector differentiability"},"syntax":"$is_vector_differentiable_at(F, p, n, m)","summary":{"zh":"断言存在表示 F 在 p 处全微分的 m×n 实矩阵。","en":"Assert the existence of an m×n real matrix representing the total differential of F at p."},"notes":{"zh":"n,m ∈ ℕ+；F 是具有完整声明的单参数函数，实际定义域 D ⊆ ℝⁿ，值域包含于 ℝᵐ。等价于存在 A ∈ matrix(R,m,n) 使 has_total_derivative_at(F,p,n,m,A)。因此 p 须为 D 的内点；仅有全部雅可比条目存在还不够。设 field(x)=(x(1),x(2),x(3))，x∈ℝ³。例：$is_vector_differentiable_at(field,(1,2,3),3,3)。","en":"n,m ∈ ℕ+. F is a unary function with a complete declared signature, actual domain D ⊆ ℝⁿ and codomain contained in ℝᵐ. This means that some A ∈ matrix(R,m,n) satisfies has_total_derivative_at(F,p,n,m,A). Thus p must be an interior point of D. Existence of every Jacobian entry alone is insufficient. Let field(x)=(x(1),x(2),x(3)) for x∈ℝ³. Example: $is_vector_differentiable_at(field,(1,2,3),3,3)."}},"has_gradient_at":{"kind":{"zh":"梯度关系","en":"Gradient relation"},"syntax":"$has_gradient_at(f, p, n, g)","summary":{"zh":"断言实向量 g 的各分量是 f 在 p 处的坐标偏导数。","en":"Assert that the entries of the real vector g are the coordinate partial derivatives of f at p."},"notes":{"zh":"n ∈ ℕ+；f 是具有完整声明的单参数函数，实际定义域 D ⊆ ℝⁿ，值域包含于 ℝ。p ∈ D，g ∈ ℝⁿ。对每个 i∈{1,…,n}，须有 ∂ᵢf(p)=g(i)。这里的梯度是向量，不是 1×n 矩阵；此关系不单独保证全可微。设 bowl(x)=x(1)^2+x(2)^2，x∈ℝ²。例：$has_gradient_at(bowl,(1,2),2,(2,4))。","en":"n ∈ ℕ+. f is a unary function with a complete declared signature, actual domain D ⊆ ℝⁿ and codomain contained in ℝ. p ∈ D and g ∈ ℝⁿ. For every i∈{1,…,n}, ∂ᵢf(p)=g(i) is required. The gradient is a vector, not a 1×n matrix. This relation alone does not guarantee total differentiability. Let bowl(x)=x(1)^2+x(2)^2 for x∈ℝ². Example: $has_gradient_at(bowl,(1,2),2,(2,4))."}},"has_jacobian_at":{"kind":{"zh":"雅可比矩阵关系","en":"Jacobian-matrix relation"},"syntax":"$has_jacobian_at(F, p, n, m, J)","summary":{"zh":"断言 J 按输出分量与输入坐标收集 F 的一阶偏导数。","en":"Assert that J collects the first partial derivatives of F by output component and input coordinate."},"notes":{"zh":"n,m ∈ ℕ+；F 是具有完整声明的单参数函数，实际定义域 D ⊆ ℝⁿ，值域包含于 ℝᵐ。p ∈ D，J ∈ matrix(R,m,n)。对每个 r∈{1,…,m}、c∈{1,…,n}，须有 J(r,c)=(∂F_r/∂x_c)(p)。这不额外断言全微分存在。设 field(x)=(x(1),x(2),x(3))，x∈ℝ³。例：$has_jacobian_at(field,(1,2,3),3,3,identity_matrix(3))。","en":"n,m ∈ ℕ+. F is a unary function with a complete declared signature, actual domain D ⊆ ℝⁿ and codomain contained in ℝᵐ. p ∈ D and J ∈ matrix(R,m,n). For every r∈{1,…,m} and c∈{1,…,n}, J(r,c)=(∂F_r/∂x_c)(p) is required. The relation does not additionally assert existence of the total differential. Let field(x)=(x(1),x(2),x(3)) for x∈ℝ³. Example: $has_jacobian_at(field,(1,2,3),3,3,identity_matrix(3))."}},"has_hessian_at":{"kind":{"zh":"海森矩阵关系","en":"Hessian-matrix relation"},"syntax":"$has_hessian_at(f, p, n, H)","summary":{"zh":"断言 H 按指定顺序收集 f 的全部迭代二阶偏导数。","en":"Assert that H collects all iterated second partial derivatives of f in the specified order."},"notes":{"zh":"n ∈ ℕ+；f 是具有完整声明的单参数函数，实际定义域 D ⊆ ℝⁿ，值域包含于 ℝ。p ∈ D，H ∈ matrix(R,n,n)。对每个 i,j∈{1,…,n}，H(i,j)=∂ⱼ(∂ᵢf)(p)：先 i 后 j。H 对称不是定义的一部分。设 bowl(x)=x(1)^2+x(2)^2，x∈ℝ²。例：$has_hessian_at(bowl,(1,2),2,fn(row closed_range(1,2),col closed_range(1,2)) R {2*identity_matrix(2)(row,col)})。","en":"n ∈ ℕ+. f is a unary function with a complete declared signature, actual domain D ⊆ ℝⁿ and codomain contained in ℝ. p ∈ D and H ∈ matrix(R,n,n). For each i,j∈{1,…,n}, H(i,j)=∂ⱼ(∂ᵢf)(p), differentiating first in i and then in j. Symmetry is not part of the definition. Let bowl(x)=x(1)^2+x(2)^2 for x∈ℝ². Example: $has_hessian_at(bowl,(1,2),2,fn(row closed_range(1,2),col closed_range(1,2)) R {2*identity_matrix(2)(row,col)})."}},"has_divergence_at":{"kind":{"zh":"散度关系","en":"Divergence relation"},"syntax":"$has_divergence_at(F, p, n, a)","summary":{"zh":"断言 F 在 p 处的对角偏导数之和等于实数 a。","en":"Assert that the sum of the diagonal partial derivatives of F at p equals the real number a."},"notes":{"zh":"n ∈ ℕ+；F 是具有完整声明的单参数函数，实际定义域 D ⊆ ℝⁿ，值域包含于 ℝⁿ。p ∈ D，a ∈ ℝ。要求每个 ∂ᵢFᵢ(p) 存在，且 a=Σᵢ₌₁ⁿ ∂ᵢFᵢ(p)。这不要求其他雅可比条目或全微分存在。设 field(x)=(x(1),x(2),x(3))，x∈ℝ³。例：$has_divergence_at(field,(1,2,3),3,3)。","en":"n ∈ ℕ+. F is a unary function with a complete declared signature, actual domain D ⊆ ℝⁿ and codomain contained in ℝⁿ. p ∈ D and a ∈ ℝ. Every ∂ᵢFᵢ(p) must exist and a=Σᵢ₌₁ⁿ ∂ᵢFᵢ(p). Other Jacobian entries and the total differential are not required. Let field(x)=(x(1),x(2),x(3)) for x∈ℝ³. Example: $has_divergence_at(field,(1,2,3),3,3)."}},"has_curl_at":{"kind":{"zh":"旋度关系","en":"Curl relation"},"syntax":"$has_curl_at(F, p, c)","summary":{"zh":"断言三维向量场 F 在 p 处的旋度等于向量 c。","en":"Assert that the curl of the three-dimensional vector field F at p is c."},"notes":{"zh":"F 是具有完整声明的单参数函数，实际定义域 D ⊆ ℝ³，值域包含于 ℝ³。p ∈ D，c ∈ ℝ³。须有六个对应偏导数，且 c=(∂₂F₃−∂₃F₂, ∂₃F₁−∂₁F₃, ∂₁F₂−∂₂F₁)(p)。此接口固定三维；不另设维数参数。设 field(x)=(x(1),x(2),x(3))，x∈ℝ³。例：$has_curl_at(field,(1,2,3),(0,0,0))。","en":"F is a unary function with a complete declared signature, actual domain D ⊆ ℝ³ and codomain contained in ℝ³. p ∈ D and c ∈ ℝ³. The six relevant partial derivatives must exist and c=(∂₂F₃−∂₃F₂, ∂₃F₁−∂₁F₃, ∂₁F₂−∂₂F₁)(p). This interface is fixed to three dimensions and has no dimension argument. Let field(x)=(x(1),x(2),x(3)) for x∈ℝ³. Example: $has_curl_at(field,(1,2,3),(0,0,0))."}},"has_laplacian_at":{"kind":{"zh":"拉普拉斯关系","en":"Laplacian relation"},"syntax":"$has_laplacian_at(f, p, n, a)","summary":{"zh":"断言 f 在 p 处的同坐标二阶偏导数之和等于实数 a。","en":"Assert that the sum of the pure second partial derivatives of f at p equals the real number a."},"notes":{"zh":"n ∈ ℕ+；f 是具有完整声明的单参数函数，实际定义域 D ⊆ ℝⁿ，值域包含于 ℝ。p ∈ D，a ∈ ℝ。要求每个 ∂ᵢ(∂ᵢf)(p) 存在，且 a=Σᵢ₌₁ⁿ ∂ᵢ(∂ᵢf)(p)。不要求所有混合偏导数或完整海森矩阵存在。设 bowl(x)=x(1)^2+x(2)^2，x∈ℝ²。例：$has_laplacian_at(bowl,(1,2),2,4)。","en":"n ∈ ℕ+. f is a unary function with a complete declared signature, actual domain D ⊆ ℝⁿ and codomain contained in ℝ. p ∈ D and a ∈ ℝ. Every ∂ᵢ(∂ᵢf)(p) must exist and a=Σᵢ₌₁ⁿ ∂ᵢ(∂ᵢf)(p). All mixed partials or a full Hessian matrix are not required. Let bowl(x)=x(1)^2+x(2)^2 for x∈ℝ². Example: $has_laplacian_at(bowl,(1,2),2,4)."}},"union":{"kind":{"zh":"集合运算符","en":"Set operator"},"syntax":"union(A, B)","summary":{"zh":"由属于 A 或属于 B 的所有元素组成的集合。","en":"The set of all elements belonging to A or to B."},"notes":{"zh":"union(A,B) = A ∪ B. A、B 均为集合。x ∈ union(A,B) ⇔ (x ∈ A ∨ x ∈ B)。例如 union({0},{1})={0,1}。这是集合运算，不将“所有集合”虚构成一个普通函数的参数域；元素不必是数。","en":"union(A,B) = A ∪ B. A and B are sets. x ∈ union(A,B) ⇔ (x ∈ A ∨ x ∈ B). For example, union({0},{1})={0,1}. This is a set operation; it does not posit a set of all sets as an ordinary function domain. Elements need not be numbers."},"role":"operator"},"intersect":{"kind":{"zh":"集合运算符","en":"Set operator"},"syntax":"intersect(A, B)","summary":{"zh":"由同时属于 A 和 B 的所有元素组成的集合。","en":"The set of all elements belonging to both A and B."},"notes":{"zh":"intersect(A,B) = A ∩ B. A、B 均为集合。x ∈ intersect(A,B) ⇔ (x ∈ A ∧ x ∈ B)。例如 intersect({0,1},{1,2})={1}。交集可以为空；例如 1 不属于 intersect({1,2},{2,3})，因为 1 不属于第二个集合。","en":"intersect(A,B) = A ∩ B. A and B are sets. x ∈ intersect(A,B) ⇔ (x ∈ A ∧ x ∈ B). For example, intersect({0,1},{1,2})={1}. The intersection may be empty. In particular, 1 does not belong to intersect({1,2},{2,3}), since 1 is not in the second set."},"role":"operator"},"∪":{"kind":{"zh":"集合运算符","en":"Set operator"},"syntax":"A ∪ B","summary":{"zh":"由属于 A 或属于 B 的所有元素组成的集合。","en":"The set of all elements belonging to A or to B."},"notes":{"zh":"union(A,B) = A ∪ B. A、B 均为集合。x ∈ union(A,B) ⇔ (x ∈ A ∨ x ∈ B)。例如 union({0},{1})={0,1}。这是集合运算，不将“所有集合”虚构成一个普通函数的参数域；元素不必是数。","en":"union(A,B) = A ∪ B. A and B are sets. x ∈ union(A,B) ⇔ (x ∈ A ∨ x ∈ B). For example, union({0},{1})={0,1}. This is a set operation; it does not posit a set of all sets as an ordinary function domain. Elements need not be numbers."},"role":"operator"},"∩":{"kind":{"zh":"集合运算符","en":"Set operator"},"syntax":"A ∩ B","summary":{"zh":"由同时属于 A 和 B 的所有元素组成的集合。","en":"The set of all elements belonging to both A and B."},"notes":{"zh":"intersect(A,B) = A ∩ B. A、B 均为集合。x ∈ intersect(A,B) ⇔ (x ∈ A ∧ x ∈ B)。例如 intersect({0,1},{1,2})={1}。交集可以为空；例如 1 不属于 intersect({1,2},{2,3})，因为 1 不属于第二个集合。","en":"intersect(A,B) = A ∩ B. A and B are sets. x ∈ intersect(A,B) ⇔ (x ∈ A ∧ x ∈ B). For example, intersect({0,1},{1,2})={1}. The intersection may be empty. In particular, 1 does not belong to intersect({1,2},{2,3}), since 1 is not in the second set."},"role":"operator"},"×":{"kind":{"zh":"笛卡尔积","en":"Cartesian product"},"syntax":"A × B","summary":{"zh":"各因子集合的元素按顺序组成的元组集合。","en":"The set of ordered tuples whose coordinates lie in the respective factors."},"notes":{"zh":"例如 p ∈ cart(A,B) 要求 p(1) ∈ A、p(2) ∈ B，并具有该二元组的完整坐标域。各因子可以不同；它不同于单个元组 (a,b)。","en":"For example, p ∈ cart(A,B) requires p(1) ∈ A and p(2) ∈ B, together with the complete coordinate domain of a pair. Factors may differ. This is a set, distinct from the individual tuple (a,b)."},"role":"operator"},"∘":{"kind":{"zh":"函数复合","en":"Function composition"},"syntax":"g ∘ f","summary":{"zh":"先应用 f，再应用 g 的复合函数。","en":"The composite function applying f first, then g."},"notes":{"zh":"一元 f 时，compose(g,f)(x)=g(f(x))；多参数时保留 f 的全部输入参数。须有两个函数的完整接口；外层 g 为一元函数，内层 f 至少有一个参数。对 f 的合法输入，f 的值还须满足 g 的参数域与附加条件。","en":"For unary f, compose(g,f)(x)=g(f(x)); for multiple arguments, all input parameters of f are retained. Both functions need complete interfaces. The outer function g is unary; the inner f has at least one argument. For each admissible input of f, its output must satisfy g’s domain and guards."},"role":"operator"},"factorial":{"kind":{"zh":"阶乘函数","en":"Factorial function"},"syntax":"factorial(n); n!","summary":{"zh":"自然数 n 的阶乘，结果为正整数。","en":"The factorial of a natural number n, with a positive-integer result."},"notes":{"zh":"输入域为 ℕ，结果属于 ℕ+。0! = 1；n≥1 时 n! = 1 · 2 · … · n。例如 5! = 120，factorial(4) = 24；负数和非整数不在输入域内。后缀 n! 与 factorial(n) 表示同一对象；exist! 中的 ! 则属于唯一存在量词。","en":"The input domain is ℕ and the result belongs to ℕ+. By definition 0! = 1 and, for n≥1, n! = 1 · 2 · … · n. For example, 5! = 120 and factorial(4) = 24. Negative numbers and nonintegers are outside the domain. The postfix n! denotes the same object as factorial(n); the ! in exist! belongs instead to the unique-existence quantifier."}},"!":{"kind":{"zh":"阶乘函数","en":"Factorial function"},"syntax":"n!","summary":{"zh":"自然数 n 的阶乘，结果为正整数。","en":"The factorial of a natural number n, with a positive-integer result."},"notes":{"zh":"输入域为 ℕ，结果属于 ℕ+。0! = 1；n≥1 时 n! = 1 · 2 · … · n。例如 5! = 120，factorial(4) = 24；负数和非整数不在输入域内。后缀 n! 与 factorial(n) 表示同一对象；exist! 中的 ! 则属于唯一存在量词。","en":"The input domain is ℕ and the result belongs to ℕ+. By definition 0! = 1 and, for n≥1, n! = 1 · 2 · … · n. For example, 5! = 120 and factorial(4) = 24. Negative numbers and nonintegers are outside the domain. The postfix n! denotes the same object as factorial(n); the ! in exist! belongs instead to the unique-existence quantifier."},"role":"operator"},"&":{"kind":{"zh":"结构类型","en":"Structure type"},"syntax":"&Structure","summary":{"zh":"满足指定结构的字段域与约束的对象组成的类型。","en":"The type of objects satisfying the fields and constraints of the specified structure."},"notes":{"zh":"& 引用一个已定义的结构类型；带参数的结构先代入类型参数，再使用各字段的要求。声明 p &Point 规定 p 的结构接口，p.x 则访问其字段。","en":"The & prefix refers to a defined structure type. A parameterized structure substitutes its type arguments before using the field requirements. A declaration p &Point specifies p’s structure interface; p.x selects a field."}},".":{"kind":{"zh":"结构字段访问","en":"Structure field access"},"syntax":"object.field","summary":{"zh":"取出结构对象中由字段名指定的分量。","en":"Select the component named by a field of a structure object."},"notes":{"zh":"对象须属于相应的结构类型；字段的类型与约束由该结构定义确定。p.x 访问字段 x；这不同于使用点号作乘法，也不是引入一个新的独立对象。","en":"The object must have the corresponding structure type. The structure definition determines the field’s type and constraints. p.x selects its x field; the dot is not multiplication, and the access introduces no new independent object."}},"\\":{"kind":{"zh":"模板实例","en":"Template instance"},"syntax":"\\Template<arguments>","summary":{"zh":"将实参代入模板，取得对应的实例对象。","en":"Substitute arguments into a template to obtain its instance object."},"notes":{"zh":"须满足模板参数的类型及附加条件，再使用实例中定义的字段或接口。反斜杠引入模板实例，尖括号中的对象是实参；不同实参的实例不会仅因使用同一模板而被视为相等。","en":"The template arguments must satisfy the declared types and guards before the instance fields or interfaces are used. A backslash introduces the instance and angle brackets contain its arguments. Instances with different arguments are not identified merely because they use the same template."}},"...":{"kind":{"zh":"闭整数范围","en":"Closed integer range"},"syntax":"a ... b","summary":{"zh":"包含左右端点的整数范围。","en":"The integer range including both endpoints."},"notes":{"zh":"a,b ∈ ℤ。k ∈ closed_range(a,b) ⇔ k ∈ ℤ 且 a ≤ k ≤ b；a > b 时为空集。例如 closed_range(1,3) = {1,2,3}。","en":"a,b ∈ ℤ. k ∈ closed_range(a,b) iff k ∈ ℤ and a ≤ k ≤ b. The set is empty when a > b; for example closed_range(1,3) = {1,2,3}."},"role":"operator"}},"statements":{"Fact":{"kind":{"zh":"语句","en":"Statement"},"syntax":"fact","summary":{"zh":"断言一个数学事实，并在当前上下文中验证它。","en":"Assert a mathematical fact and verify it in the current context."},"notes":{"zh":"验证成功后，后文可以引用该事实。陈述失败只表示当前检查未建立结论，并不证明结论为假。","en":"After verification, later statements may cite the fact. A failed check means the conclusion was not established, not that it is false."}},"LetObjStmt":{"kind":{"zh":"语句","en":"Statement"},"syntax":"let a = expression","summary":{"zh":"将名称绑定到给定的数学对象。","en":"Bind a name to a specified mathematical object."},"notes":{"zh":"先检查右侧表达式有定义；名称随后表示这个对象。绑定与引入任意参数不同。","en":"The right-hand expression must be well-defined. The name denotes that object, rather than an arbitrary parameter."}},"HaveObjInNonemptySetStmt":{"kind":{"zh":"语句","en":"Statement"},"syntax":"have x A","summary":{"zh":"从已知非空的集合 A 中引入对象 x。","en":"Introduce an object x from a known nonempty set A."},"notes":{"zh":"这给出 x ∈ A，不指定 x 的具体值。若同时声明多个对象，它们可以相等。","en":"This establishes x ∈ A without specifying a value. Several introduced objects need not be distinct."}},"HaveObjEqualStmt":{"kind":{"zh":"语句","en":"Statement"},"syntax":"have a A = expression","summary":{"zh":"在声明域内用等式定义对象。","en":"Define an object by equality within a declared domain."},"notes":{"zh":"右侧表达式须有定义且属于 A；随后得到对象的归属事实和定义等式。","en":"The expression must be well-defined and belong to A. The declaration supplies both membership and the defining equality."}},"HaveObjByExistFactsStmt":{"kind":{"zh":"语句","en":"Statement"},"syntax":"have x A:\n    condition","summary":{"zh":"利用已知存在性引入满足条件的对象。","en":"Introduce an object satisfying conditions using established existence."},"notes":{"zh":"需要已有的相应存在事实；不能用这条语句任意假定条件成立。","en":"The matching existence fact must already be established; the conditions are not introduced as arbitrary assumptions."}},"ObtainObjFromExistFact":{"kind":{"zh":"语句","en":"Statement"},"syntax":"obtain x from exist x A st {condition}","summary":{"zh":"从一个已建立的存在命题中取出见证。","en":"Extract a witness from an established existential statement."},"notes":{"zh":"见证满足声明域和存在命题的条件；这一步不声称所有对象都满足这些条件。","en":"The witness satisfies the declared domain and existential conditions; this does not assert those conditions for every object."}},"ObtainObjFromAtomicFact":{"kind":{"zh":"语句","en":"Statement"},"syntax":"obtain x from $P(arguments)","summary":{"zh":"从谓词事实所提供的存在性中提取见证。","en":"Extract a witness from existence supplied by a predicate fact."},"notes":{"zh":"见证的性质取决于该谓词实际给出的存在性条件，不能仅凭谓词名称猜测。","en":"The witness properties come from the predicate’s retained existential conditions, not from interpreting its name."}},"HaveByPreimageStmt":{"kind":{"zh":"语句","en":"Statement"},"syntax":"have by fn_preimage: x from y $in fn_range(f)","summary":{"zh":"利用原像的存在性选取具有指定函数值的对象。","en":"Select an input with a specified function value using a preimage existence result."},"notes":{"zh":"须验证所用函数、目标值及相应原像非空等要求；声明不把任意函数当作满射。","en":"The function, target value and required nonempty fiber must be justified; this declaration does not assume that an arbitrary function is surjective."}},"HaveByReplacementAxiomStmt":{"kind":{"zh":"语句","en":"Statement"},"syntax":"have by replacement_axiom: Image from prop relation, set A","summary":{"zh":"按替换公理构造由已给定集合逐点产生的像集。","en":"Construct an image set by replacement from an existing set."},"notes":{"zh":"构造使用给定的定义关系及其唯一性要求，不形成所有对象的无界集合。","en":"The construction uses its specified relation and required uniqueness; it does not form an unrestricted set of all objects."}},"HaveFnEqualStmt":{"kind":{"zh":"函数定义","en":"Function definition"},"syntax":"have fn f(x A: condition) B = expression","summary":{"zh":"以一个表达式定义函数值。","en":"Define function values by an expression."},"notes":{"zh":"参数须满足声明域和条件；函数体在这些条件下须有定义且属于 B。应用函数时按绑定变量的身份代入实参。","en":"Arguments must satisfy the declared domains and guards. Under those conditions, the body must be well-defined and belong to B. Application substitutes arguments by bound-variable identity."}},"HaveFnEqualCaseByCaseStmt":{"kind":{"zh":"分段函数定义","en":"Function definition by cases"},"syntax":"have fn f(x A) B by cases:\n    case condition: expression","summary":{"zh":"按互不冲突且穷尽定义域的分支定义函数。","en":"Define a function by mutually compatible cases covering its domain."},"notes":{"zh":"每个分支须满足对应的条件和返回域要求；对具体实参求值时，使用实际被验证的分支。","en":"Each branch must satisfy its guard and return-domain requirements. A concrete application uses the branch whose guard was actually established."}},"HaveFnByInducStmt":{"kind":{"zh":"递归函数定义","en":"Recursive function definition"},"syntax":"have fn f(n N) B by induc n from k:\n    case condition: expression","summary":{"zh":"按整数度量递归定义函数。","en":"Define a function recursively using an integer measure."},"notes":{"zh":"初始分支给出基础值；递归调用须符合归纳度量的下降要求，且各分支满足返回域。","en":"Initial cases provide base values. Recursive calls must satisfy the decreasing-measure requirements and each branch must lie in the return domain."}},"HaveFnByForallExistUniqueStmt":{"kind":{"zh":"由唯一存在性定义函数","en":"Function from unique existence"},"syntax":"have fn f by exist!:\n    ? forall x A:\n        exist! y B st {condition}","summary":{"zh":"由逐点唯一存在性定义函数。","en":"Define a function from pointwise unique existence."},"notes":{"zh":"须证明每个合法输入恰有一个满足条件的输出；这不要求给出一个可直接计算的函数体。","en":"Every admissible input must have exactly one output satisfying the specification. An explicitly computable body is not required."}},"DefPropStmt":{"kind":{"zh":"谓词定义","en":"Predicate definition"},"syntax":"prop P(x A):\n    condition","summary":{"zh":"定义带类型参数的谓词及其等价条件。","en":"Define a predicate with typed parameters and equivalent defining conditions."},"notes":{"zh":"对声明域内的参数，P 成立等价于定义体中的全部条件同时成立。定义本身不证明某个具体实例。","en":"For arguments in the declared domains, P holds exactly when all defining conditions hold. A definition does not prove a particular instance."}},"DefAbstractPropStmt":{"kind":{"zh":"抽象谓词","en":"Abstract predicate"},"syntax":"abstract_prop P(x A)","summary":{"zh":"声明谓词的参数接口，不给出等价定义。","en":"Declare a predicate’s parameter interface without a defining equivalence."},"notes":{"zh":"后续事实或定理可使用 P；这个声明不使任何 P 的实例自动成立。","en":"Later facts and theorems may use P, but the declaration establishes no instance of P."}},"DefTemplateStmt":{"kind":{"zh":"模板定义","en":"Template definition"},"syntax":"template<S set>:\n    definition","summary":{"zh":"以类型化参数定义一族可实例化的数学接口。","en":"Define a family of mathematical interfaces parameterized by typed arguments."},"notes":{"zh":"实例化时检查参数条件，再使用相应定义；模板参数与实例定义内部的局部参数具有不同作用域。","en":"Instantiation checks the template arguments before using the resulting definition. Template parameters and local binders have distinct scopes."}},"DefStructStmt":{"kind":{"zh":"结构定义","en":"Structure definition"},"syntax":"struct Name:\n    field A","summary":{"zh":"用带类型的字段及约束定义结构。","en":"Define a structure through typed fields and constraints."},"notes":{"zh":"字段可以依赖此前字段；结构对象须满足相应字段域及结构约束。访问字段不会凭空建立额外性质。","en":"Fields may depend on earlier fields. A structure value must satisfy the field domains and constraints; field access establishes no additional property by itself."}},"DefAlgoByCasesStmt":{"kind":{"zh":"算法定义","en":"Algorithm definition"},"syntax":"algo f(x A) B by cases:\n    case condition: expression","summary":{"zh":"定义带可执行分支的函数算法。","en":"Define a function algorithm with executable cases."},"notes":{"zh":"数学函数接口和执行分支分别受到检查；是否可执行与一个命题是否已被证明是不同问题。","en":"The mathematical function interface and executable branches are checked separately. Executability is distinct from proving a proposition."}},"DefAlgoByInducStmt":{"kind":{"zh":"递归算法定义","en":"Recursive algorithm definition"},"syntax":"algo f(n N) B by induc n from k:\n    case condition: expression","summary":{"zh":"定义带归纳度量的递归算法。","en":"Define a recursive algorithm with an induction measure."},"notes":{"zh":"递归分支须满足相应度量及返回域要求；不是允许无限自调用的赋值语句。","en":"Recursive branches must meet the measure and return-domain requirements; the declaration is not unrestricted self-assignment."}},"DefThmStmt":{"kind":{"zh":"定理","en":"Theorem"},"syntax":"thm name:\n    ? fact\n    proof","summary":{"zh":"证明并命名一个可复用的数学结论。","en":"Prove and name a reusable mathematical result."},"notes":{"zh":"? 标出定理目标；证明使用声明的参数与前提。后续应用时须验证实例化后的要求。","en":"The ? marker identifies the goal. The proof uses its declared parameters and premises; later applications must establish the instantiated requirements."}},"AxiomStmt":{"kind":{"zh":"公理声明","en":"Axiom declaration"},"syntax":"axiom name:\n    ? forall ...","summary":{"zh":"命名一个作为基础假设接受的全称命题。","en":"Name a universal proposition accepted as a foundational assumption."},"notes":{"zh":"检查接口和表达式合法性，不提供该公理的证明；依赖它的结论仍依赖该假设。","en":"Its interface and formation are checked, but no proof of the axiom is supplied. Conclusions using it retain that assumption dependency."}},"DefStrategyStmt":{"kind":{"zh":"证明策略","en":"Proof strategy"},"syntax":"strategy name:\n    ? forall ...\n    proof","summary":{"zh":"定义一个可复用的证明策略。","en":"Define a reusable proof strategy."},"notes":{"zh":"策略根据目标匹配参数，并验证实例化前提；匹配成功不能替代前提证明。","en":"A strategy matches parameters against a goal and verifies the instantiated premises. A successful match does not replace the premise proofs."}},"ByDefStmt":{"kind":{"zh":"按定义证明","en":"Proof by definition"},"syntax":"by def $P(arguments)","summary":{"zh":"按谓词的定义证明一个具体实例。","en":"Prove a concrete predicate instance by its definition."},"notes":{"zh":"将实参代入定义，验证参数要求及全部定义条件，再建立实例事实。实例的证明与谓词声明是不同步骤。","en":"Substitute the arguments, verify their requirements and all defining conditions, then establish the instance. This is distinct from declaring the predicate."}},"ByThmStmt":{"kind":{"zh":"应用定理","en":"Theorem application"},"syntax":"by thm theorem(arguments) => fact","summary":{"zh":"应用已有定理，选择并建立其中一个原子结论。","en":"Apply an existing theorem and establish one selected atomic conclusion."},"notes":{"zh":"须检查实参、实例化前提和结论的对应关系。所选结论必须由该次定理应用提供；不能将任意目标附在定理名称之后。","en":"Check the arguments, instantiated premises and correspondence with the selected conclusion. The conclusion must be supplied by that application; an arbitrary goal cannot be appended to a theorem name."}},"ByCasesStmt":{"kind":{"zh":"分类证明","en":"Proof by cases"},"syntax":"by cases:\n    ? fact\n    case condition:\n        proof","summary":{"zh":"通过穷尽可能性的分类讨论证明结论。","en":"Prove conclusions by an exhaustive case split."},"notes":{"zh":"每种情况中都须证明所需结论，或证明该情况不可能发生；分支假设只在对应分支有效。","en":"Each case must establish the requested conclusions or be shown impossible. A branch assumption is local to its branch."}},"ByContraStmt":{"kind":{"zh":"反证法","en":"Proof by contradiction"},"syntax":"by contra:\n    ? fact\n    proof","summary":{"zh":"假设目标的否定，并由矛盾证明原目标。","en":"Prove a goal by deriving a contradiction under its negation."},"notes":{"zh":"须实际建立互相矛盾的事实。反证假设不会作为无条件结论交给后文。","en":"Incompatible facts must actually be established. The temporary negation is not exported as an unconditional conclusion."}},"ByEnumerateFiniteSetStmt":{"kind":{"zh":"有限枚举证明","en":"Finite enumeration proof"},"syntax":"by enumerate finite_set:\n    ? forall x S => condition\n    proof","summary":{"zh":"逐个验证有限集合中的对象，证明一个全称命题。","en":"Prove a universal statement by checking each element of a finite set."},"notes":{"zh":"集合必须可按该指令支持的方式枚举；验证一个例子不能替代检查全部元素。","en":"The carrier must be enumerable by this command. Checking one example does not establish every case."}},"ByForStmt":{"kind":{"zh":"范围枚举证明","en":"Range enumeration proof"},"syntax":"by for:\n    ? forall i range(a, b) => condition\n    proof","summary":{"zh":"通过有限范围的逐项检查证明全称结论。","en":"Prove a universal conclusion by checking a finite range."},"notes":{"zh":"按指令支持的范围或笛卡尔积枚举所有参数组合，并对每组检查结论。","en":"Enumerate all parameter combinations in the supported ranges or Cartesian products and verify the conclusion in each case."}},"ByInducStmt":{"kind":{"zh":"数学归纳法","en":"Mathematical induction"},"syntax":"by induc n from k:\n    ? fact\n    proof","summary":{"zh":"用基础情形与归纳步骤证明整数指标上的结论。","en":"Prove an integer-indexed conclusion using a base case and induction step."},"notes":{"zh":"基础情形验证起点；归纳步骤在相应归纳假设下证明下一指标的结论。起点和参数域也须满足要求。","en":"The base case establishes the starting point. The step proves the next case under the corresponding induction hypothesis. The start and parameter domain must also satisfy their requirements."}},"ByStrongInducStmt":{"kind":{"zh":"强归纳法","en":"Strong induction"},"syntax":"by strong_induc n from k:\n    ? fact\n    proof","summary":{"zh":"用所有较小指标的结论作归纳假设。","en":"Use conclusions at all smaller admissible indices as the induction hypothesis."},"notes":{"zh":"仍须验证基础情形；强归纳允许在归纳步骤中使用起点之后且小于当前指标的已假定结论。","en":"A base case is still required. The induction step may use assumed conclusions from the starting point up to, but not including, the current index."}},"ByExtensionStmt":{"kind":{"zh":"集合外延证明","en":"Set extensionality"},"syntax":"by extension A = B","summary":{"zh":"用集合的相互包含证明集合相等。","en":"Prove equality of sets by mutual inclusion."},"notes":{"zh":"分别验证 A ⊆ B 和 B ⊆ A。仅证明其中一个方向，通常只能得到包含关系。","en":"Establish A ⊆ B and B ⊆ A separately. A single direction generally establishes only inclusion."}},"ByFnExtensionStmt":{"kind":{"zh":"函数外延证明","en":"Function extensionality"},"syntax":"by fn_extension f = g","summary":{"zh":"在共同的函数接口上用逐点相等证明函数相等。","en":"Prove equality of functions by pointwise equality on a common interface."},"notes":{"zh":"须满足函数域与接口匹配要求，再证明每个合法输入上的值相同；有限个样本相等通常不够。","en":"The function domains and interfaces must match, and values must agree at every admissible input. Agreement at finitely many sample inputs generally does not suffice."}},"ReleaseThmStmt":{"kind":{"zh":"定理实例化","en":"Theorem instantiation"},"syntax":"release thm theorem(arguments)","summary":{"zh":"应用定理，并引入该次实例化的全部结论。","en":"Apply a theorem and introduce all conclusions of that instantiation."},"notes":{"zh":"先验证参数域、函数参数要求和实例化前提。定理前提不是由这条语句直接假定的。","en":"First verify parameter domains, function-argument requirements and instantiated premises. This command does not assume the theorem’s premises."}},"ReleaseStructDefStmt":{"kind":{"zh":"展开结构定义","en":"Unpack a structure definition"},"syntax":"release struct def object","summary":{"zh":"展开一个结构对象的定义性质。","en":"Unpack the defining properties of a structure object."},"notes":{"zh":"按该结构的实际定义引入字段约束及相应关系；不会自动证明定义中未给出的性质。","en":"Introduce the field constraints and relations supplied by the actual structure definition; no unstated properties are established."}},"ReleaseObjDefStmt":{"kind":{"zh":"展开对象定义","en":"Unpack an object definition"},"syntax":"release obj def object","summary":{"zh":"显式引入对象定义所给出的事实。","en":"Explicitly introduce the facts provided by an object definition."},"notes":{"zh":"使用当前可见的实际定义；这与任意改写一个数学对象不同。","en":"Use the actual visible definition; this does not permit arbitrary replacement of the object."}},"ReleaseCartDefStmt":{"kind":{"zh":"展开笛卡尔积","en":"Unpack a Cartesian product"},"syntax":"release cart def cart(A, B)","summary":{"zh":"展开笛卡尔积对各坐标的约束。","en":"Unpack Cartesian-product coordinate constraints."},"notes":{"zh":"乘积中的对象由指定数量和类型的坐标刻画；每一坐标必须满足对应因子集合的要求。","en":"A product element is characterized by the specified coordinate count and domains. Each coordinate must meet its factor’s requirements."}},"ReleaseTupleDefStmt":{"kind":{"zh":"展开元组","en":"Unpack a tuple"},"syntax":"release tuple def tuple","summary":{"zh":"展开元组的坐标及维数性质。","en":"Unpack a tuple’s coordinates and dimension properties."},"notes":{"zh":"坐标编号从 1 开始；仅引入该元组实际给出的坐标关系。","en":"Coordinates are numbered from 1; only the actual tuple’s coordinate relations are introduced."}},"ExpandRangeStmt":{"kind":{"zh":"展开范围归属","en":"Expand range membership"},"syntax":"expand: x $in range(a, b)","summary":{"zh":"将可枚举整数范围的归属展开为有限种取值。","en":"Expand membership in an enumerable integer range into finitely many possible values."},"notes":{"zh":"range(a, b) 包含左端 a，不包含右端 b；展开须遵守该整数范围的实际边界。","en":"range(a, b) includes a and excludes b. Expansion respects those integer-range boundaries."}},"ReleaseZornLemmaStmt":{"kind":{"zh":"佐恩引理","en":"Zorn’s lemma"},"syntax":"release zorn_lemma: ...","summary":{"zh":"在满足条件的偏序结构上应用佐恩引理。","en":"Apply Zorn’s lemma to a partially ordered structure satisfying its hypotheses."},"notes":{"zh":"须建立所用偏序、非空性和链的上界等规定前提，才能引入相应极大元素结论。","en":"The required partial order, nonemptiness and chain-upper-bound premises must be established before the maximal-element conclusion is introduced."}},"ReleaseAxiomOfChoiceStmt":{"kind":{"zh":"选择公理","en":"Axiom of choice"},"syntax":"release axiom_of_choice: ...","summary":{"zh":"对非空集合族应用选择公理。","en":"Apply the axiom of choice to a family of nonempty sets."},"notes":{"zh":"选择函数为族中的每个集合选取一个属于该集合的元素；必须满足该指令实际要求的集合族条件。","en":"A choice function selects an element from each member of the family. The command’s family hypotheses must be established."}},"ReleaseRegularityAxiomStmt":{"kind":{"zh":"正则公理","en":"Axiom of regularity"},"syntax":"release regularity_axiom(S)","summary":{"zh":"对集合 S 应用正则公理。","en":"Apply the axiom of regularity to S."},"notes":{"zh":"非空集合存在一个与它不交的元素；具体结论及前提以本次指令保留的记录为准。","en":"A nonempty set has an element disjoint from it. The precise premises and conclusions are those retained for this application."}},"RegisterTransitivePropStmt":{"kind":{"zh":"性质登记","en":"Property registration"},"syntax":"register transitive: ...","summary":{"zh":"登记一个二元谓词的传递性规则。","en":"Register the transitivity law of a binary predicate."},"notes":{"zh":"规则形状为 P(a,b) ∧ P(b,c) ⇒ P(a,c)，变量须满足所登记接口的类型和适用条件。 登记前须验证相应的全称规律。","en":"The law has shape P(a,b) ∧ P(b,c) ⇒ P(a,c), subject to the registered interface’s types and applicability conditions. The corresponding universal law must be verified before registration."}},"RegisterSymmetricPropStmt":{"kind":{"zh":"性质登记","en":"Property registration"},"syntax":"register symmetric: ...","summary":{"zh":"登记一个二元谓词的对称性规则。","en":"Register the symmetry law of a binary predicate."},"notes":{"zh":"规则形状为 P(a,b) ⇒ P(b,a)，变量须满足所登记接口的类型和适用条件。 登记前须验证相应的全称规律。","en":"The law has shape P(a,b) ⇒ P(b,a), subject to the registered interface’s types and applicability conditions. The corresponding universal law must be verified before registration."}},"RegisterReflexivePropStmt":{"kind":{"zh":"性质登记","en":"Property registration"},"syntax":"register reflexive: ...","summary":{"zh":"登记一个二元谓词的自反性规则。","en":"Register the reflexivity law of a binary predicate."},"notes":{"zh":"规则形状为 P(a,a)，变量须满足所登记接口的类型和适用条件。 登记前须验证相应的全称规律。","en":"The law has shape P(a,a), subject to the registered interface’s types and applicability conditions. The corresponding universal law must be verified before registration."}},"WitnessExistFact":{"kind":{"zh":"存在见证","en":"Existential witness"},"syntax":"witness exist x A st {condition} from a: ...","summary":{"zh":"提供具体对象，证明一个存在命题。","en":"Supply concrete objects to prove an existential statement."},"notes":{"zh":"须证明见证属于声明域，并验证将见证代入后的全部条件。一个见证不自动证明唯一存在。","en":"Each witness must lie in its declared domain and satisfy all instantiated conditions. A witness alone does not prove unique existence."}},"WitnessAtomicFact":{"kind":{"zh":"谓词见证","en":"Predicate witness"},"syntax":"witness $P(arguments) from ...","summary":{"zh":"通过具体见证验证谓词中的存在性条件。","en":"Verify a predicate’s existential condition by supplying witnesses."},"notes":{"zh":"见证必须满足该谓词定义所要求的条件；展示一个任意对象不构成存在性证明。","en":"The witnesses must satisfy the conditions required by the predicate definition. Displaying an arbitrary object is not an existence proof."}},"WitnessNonemptySet":{"kind":{"zh":"非空见证","en":"Nonemptiness witness"},"syntax":"witness $is_nonempty_set(A) from a: ...","summary":{"zh":"给出 A 的一个元素，证明 A 非空。","en":"Prove A nonempty by supplying an element of A."},"notes":{"zh":"须验证 a ∈ A；仅给对象 a 命名不能建立它属于 A。","en":"Membership a ∈ A must be verified; naming an object does not establish its membership."}},"ClaimStmt":{"kind":{"zh":"局部断言","en":"Local claim"},"syntax":"claim:\n    ? fact\n    proof","summary":{"zh":"在局部证明中建立一个指定结论。","en":"Establish a specified conclusion in a local proof."},"notes":{"zh":"块内可引入辅助步骤；只有被证明的目标交给外层使用，局部辅助声明不会全部逸出。","en":"The block may introduce auxiliary steps. The established target is exported, not every local helper declaration."}},"SketchStmt":{"kind":{"zh":"证明草稿","en":"Proof sketch"},"syntax":"sketch:\n    proof","summary":{"zh":"检查一个局部证明草稿，其结果不向外发布。","en":"Check a local proof sketch without exporting its results."},"notes":{"zh":"草稿中的数学语句仍须通过相应检查；它不等于 trust。","en":"Mathematical statements in the sketch remain subject to checking; a sketch is not a trust boundary."}},"TrustStmt":{"kind":{"zh":"显式信任","en":"Explicit trust"},"syntax":"trust:\n    fact","summary":{"zh":"将列出的事实作为显式假设接受。","en":"Accept the listed facts as explicit assumptions."},"notes":{"zh":"仍检查表达式有定义，但跳过事实的真值证明。严格模式拒绝此类边界；依赖关系应标明信任来源。","en":"Formation is still checked, but truth proofs are skipped. Strict mode rejects this boundary; dependent results retain its trust provenance."}},"TrustHaveStmt":{"kind":{"zh":"带信任的对象声明","en":"Object declaration with trust"},"syntax":"trust have x A:\n    condition","summary":{"zh":"引入对象，并显式信任列出的性质。","en":"Introduce objects and explicitly trust the listed properties."},"notes":{"zh":"这不是由已有存在性证明得到的构造。仍须检查表达式有定义，严格模式拒绝此类边界。","en":"This is not a construction justified by established existence. Formation remains checked and strict mode rejects this boundary."}},"EvalStmt":{"kind":{"zh":"精确求值","en":"Exact evaluation"},"syntax":"eval expression","summary":{"zh":"精确求值，并保留原表达式与结果的等式。","en":"Evaluate an expression exactly and retain its equality with the result."},"notes":{"zh":"表达式必须有定义且受当前求值器支持；这不等于对任意函数执行数值近似。","en":"The expression must be well-defined and supported by the evaluator. This is not unrestricted numerical approximation of an arbitrary function."}}},"builtin_theorems":{"FiniteSetHasBijectiveIndex":{"kind":{"zh":"内置定理","en":"Builtin theorem"},"syntax":"finite_set_has_bijective_index(S)","summary":{"zh":"有限集合的元素可以恰好编号一次。","en":"Every finite set admits an enumeration in which each element occurs exactly once."},"notes":{"zh":"S 为有限集合，n=finite_set_size(S)。结论为存在 idx ∈ finite_seq(S,n)，使 idx 是 closed_range(1,n) 到 S 的双射。n=0 时编号域为空；一般可以有多个满足条件的编号。存在命题提供编号的见证，使用时可通过 obtain 取出。","en":"S must be finite. Let n=finite_set_size(S). The conclusion provides an idx ∈ finite_seq(S,n) that is a bijection from closed_range(1,n) onto S. For n=0 the index domain is empty. An enumeration need not be unique; obtain can unpack the existential witness."},"example":"release thm finite_set_has_bijective_index({1, 2})\nexist idx finite_seq({1, 2}, finite_set_size({1, 2})) st {$bijective(closed_range(1, finite_set_size({1, 2})), {1, 2}, idx)}"},"SubsetOfFiniteSetIsFinite":{"kind":{"zh":"内置定理","en":"Builtin theorem"},"syntax":"subset_of_finite_set_is_finite(A, B)","summary":{"zh":"有限集合的每个子集仍为有限集合。","en":"Every subset of a finite set is finite."},"notes":{"zh":"前提为 A 是集合、B 是有限集合且 A ⊆ B；结论为 A 有限。不预先要求 A 有限，也不要求 A 或 B 非空。例中 {1} ⊆ {1,2}，从右侧集合的有限性得到左侧的有限性。","en":"The premises are that A is a set, B is finite and A ⊆ B; the conclusion is that A is finite. Finiteness of A is not assumed, and neither set must be nonempty. The example uses {1} ⊆ {1,2}."},"example":"release thm subset_of_finite_set_is_finite({1}, {1, 2})\n$is_finite_set({1})"},"IndexCartesianMember":{"kind":{"zh":"内置定理","en":"Builtin theorem"},"syntax":"index_cart_member(f, P)","summary":{"zh":"由逐个纤维中的取值条件，证明函数属于指标笛卡尔积。","en":"Establish membership in an indexed Cartesian product from the fiberwise choice conditions."},"notes":{"zh":"第二个参数须为 P=index_cart(I,S,g)。须证明 f 是从 I 到 family_union(S) 的函数，并满足 is_choice_function_for(I,S,g,f)，即对每个 i∈I 有 f(i)∈g(i)。结论为 f∈P。构造 P 仍要求 I、S 非空及 g 的完整函数接口；这不是仅由 f 有定义便能得到的结论。","en":"The second argument must be P=index_cart(I,S,g). The premises give f:I→family_union(S) and is_choice_function_for(I,S,g,f), meaning f(i)∈g(i) for every i∈I. The conclusion is f∈P. The constructor still requires nonempty I and S and a complete interface for g; having a defined f alone is insufficient."},"example":"thm member:\n    ? forall g fn(k {1}) {{1}}, f fn(index {1}) family_union({{1}}):\n        $is_choice_function_for({1}, {{1}}, g, f)\n        =>:\n            f $in index_cart({1}, {{1}}, g)\n    release thm index_cart_member(f, index_cart({1}, {{1}}, g))"},"IndexCartesianNonemptyByChoiceFromFamily":{"kind":{"zh":"内置定理","en":"Builtin theorem"},"syntax":"index_cart_nonempty_by_choice_from_family(P)","summary":{"zh":"在整个载体集合族均非空的前提下，用选择公理建立指标乘积非空。","en":"Use choice to establish nonemptiness of an indexed product when every set in its carrying family is nonempty."},"notes":{"zh":"参数须为 P=index_cart(I,S,g)，其构造须有定义。前提为对每个 A∈S，A 是非空集合；结论为 P 非空，即存在函数 f 在每个 i∈I 处选取 g(i) 的一个元素。此版本检查整个 S，包括未被 g 取到的成员；I、S 的非空要求仍属于构造的条件。","en":"The argument must be the well-defined constructor P=index_cart(I,S,g). The premise requires every A∈S to be a nonempty set. Choice then yields a member f of P, selecting an element of g(i) at every i∈I. This version checks all of S, including unused members. The constructor still requires nonempty I and S."},"example":"thm choice_from_family:\n    ? forall S nonempty_set, g fn(k {1}) S:\n        forall A S:\n            $is_nonempty_set(A)\n        =>:\n            $is_nonempty_set(index_cart({1}, S, g))\n    release thm index_cart_nonempty_by_choice_from_family(index_cart({1}, S, g))"},"IndexCartesianNonemptyByChoiceFromPointwise":{"kind":{"zh":"内置定理","en":"Builtin theorem"},"syntax":"index_cart_nonempty_by_choice_from_pointwise(P)","summary":{"zh":"由每个实际纤维非空，用选择公理建立指标乘积非空。","en":"Use choice to establish nonemptiness of an indexed product from nonemptiness of each actual fiber."},"notes":{"zh":"参数须为有定义的 P=index_cart(I,S,g)。前提为对每个 i∈I，g(i) 是非空集合；结论为 P 非空。此版本只量化实际使用的纤维 g(i)，不额外要求 S 中未使用的成员非空；构造自身仍要求 I、S 非空及 g 的函数接口。","en":"The argument must be the well-defined P=index_cart(I,S,g). For every i∈I, the fiber g(i) must be a nonempty set; the conclusion is that P is nonempty. Only actual fibers are quantified, so unused members of S need not be nonempty. The constructor still requires nonempty I and S and the interface for g."},"example":"thm choice_from_pointwise:\n    ? forall g fn(k {1}) {{1}}:\n        forall alpha {1}:\n            $is_nonempty_set(g(alpha))\n        =>:\n            $is_nonempty_set(index_cart({1}, {{1}}, g))\n    release thm index_cart_nonempty_by_choice_from_pointwise(index_cart({1}, {{1}}, g))"},"FiniteSetReduceSingleton":{"kind":{"zh":"内置定理","en":"Builtin theorem"},"syntax":"finite_set_reduce_singleton(r, x)","summary":{"zh":"单元素集合上的折叠只需将初值与该元素的函数值合并一次。","en":"A fold over a singleton combines the seed with that element’s function value once."},"notes":{"zh":"第一个参数须为 r=finite_set_reduce(S,f,op,seed)，并须证明 S={x}。结论为 r=op(seed,f(x))。折叠自身的条件仍须成立：f 在 S 上有定义，op 在共同载体 T 上封闭且满足结合律、交换律，seed∈T；seed 不必是单位元。","en":"The first argument must be r=finite_set_reduce(S,f,op,seed), and S={x} must be proved. The conclusion is r=op(seed,f(x)). The fold must remain well-defined: f is defined on S; op is a closed, associative and commutative operation on a common carrier T; and seed∈T. The seed need not be an identity element."},"example":"have fn identity(x Z) Z = x\nhave fn add(a, b Z) Z = a + b\nrelease thm finite_set_reduce_singleton(finite_set_reduce({2}, identity, add, 0), 2)\nidentity(2) = 2\nadd(0, identity(2)) = add(0, 2) = 2\nfinite_set_reduce({2}, identity, add, 0) = add(0, identity(2)) = 2"},"FiniteSetSumSubstitution":{"kind":{"zh":"内置定理","en":"Builtin theorem"},"syntax":"finite_set_sum_substitution(left, right)","summary":{"zh":"逐点相等或合法的双射换元保持有限集合上的和。","en":"Pointwise equality or a valid bijective change of variables preserves a finite-set sum."},"notes":{"zh":"两个参数均须为有定义的 finite_set_sum，求和函数取复数值。通常须证明索引集合相等及逐点值相等。若一侧显式为拉回形式 f(g(y))，则检查 g 从该侧索引集到另一侧索引集的双射性，并核对对应求和项。两条路线的结论都是 left=right；仅有相同项数不够。","en":"Both arguments must be well-defined finite_set_sum objects with complex-valued summands. The common-set route proves equal index sets and pointwise equal values. If one side has the explicit pullback form f(g(y)), the interface checks that g bijects its index set onto the other and that summands correspond. Either route concludes left=right. Equal cardinalities alone are insufficient."},"example":"thm substitution:\n    ? forall f fn(t {1, 2}) R, g fn(u {1, 2}) {1, 2}:\n        $bijective({1, 2}, {1, 2}, g)\n        =>:\n            finite_set_sum({1, 2}, f) = finite_set_sum({1, 2}, fn(y {1, 2}) R {f(g(y))})\n    release thm finite_set_sum_substitution(finite_set_sum({1, 2}, f), finite_set_sum({1, 2}, fn(y {1, 2}) R {f(g(y))}))"},"SumOverBijectiveFiniteSetEnumerations":{"kind":{"zh":"内置定理","en":"Builtin theorem"},"syntax":"sum_over_bijective_finite_set_enumerations(left, right)","summary":{"zh":"同一有限集合的两种双射编号给出相同的求和结果。","en":"Two bijective enumerations of the same finite set give the same sum."},"notes":{"zh":"参数为两项有定义的 sum(a,b,...)，整数端点 a≤b 相同；求和项须能核对为同一函数 f 在 e₁(i)、e₂(i) 处的值。两个编号的返回集合均须为同一有限集 S，并证明 e₁、e₂ 都是 closed_range(a,b) 到 S 的双射。具名求和函数须有已证明的对应定义体；结论为两项和相等。","en":"The arguments are well-defined sum(a,b,...) objects with the same integer endpoints a≤b. Their terms must be recoverable as f(e₁(i)) and f(e₂(i)) for the same f. Both enumerators have the same finite return set S and must biject closed_range(a,b) onto S. Named callbacks need proved corresponding bodies. The conclusion equates the two sums."},"example":"thm enumeration:\n    ? forall f fn(t {1, 2}) R, e1, e2 fn(u closed_range(1, 2)) {1, 2}, left_fn, right_fn fn(k closed_range(1, 2)) R:\n        $bijective(closed_range(1, 2), {1, 2}, e1)\n        $bijective(closed_range(1, 2), {1, 2}, e2)\n        left_fn = fn(k closed_range(1, 2)) R{f(e1(k))}\n        right_fn = fn(k closed_range(1, 2)) R{f(e2(k))}\n        =>:\n            sum(1, 2, left_fn) = sum(1, 2, right_fn)\n    by thm sum_over_bijective_finite_set_enumerations(sum(1, 2, left_fn), sum(1, 2, right_fn)) => sum(1, 2, left_fn) = sum(1, 2, right_fn)"},"FiniteSetSumLessEqualFromPointwise":{"kind":{"zh":"内置定理","en":"Builtin theorem"},"syntax":"finite_set_sum_le_from_pointwise(left, right)","summary":{"zh":"同一有限集合上的逐点不等式可以求和。","en":"A pointwise inequality on a common finite set can be summed."},"notes":{"zh":"参数为 left=finite_set_sum(S,f)、right=finite_set_sum(T,g)。须证明 S=T，并对每个 x∈S 证明 f(x)≤g(x)；所有求和项须有定义并为实数。结论为 left≤right。前提比较的是同一个 x 对应的两项，不是比较两组任意元素。","en":"Write left=finite_set_sum(S,f) and right=finite_set_sum(T,g). Prove S=T and f(x)≤g(x) for every x∈S, with defined real summands. The conclusion is left≤right. The pointwise comparison pairs terms at the same x, rather than arbitrary terms from the two sums."},"example":"release thm finite_set_sum_le_from_pointwise(finite_set_sum({1, 2}, fn(x {1, 2}) R {1}), finite_set_sum({1, 2}, fn(y {1, 2}) R {2}))"},"FiniteSetSummandLessEqualSum":{"kind":{"zh":"内置定理","en":"Builtin theorem"},"syntax":"finite_set_summand_le_sum(term, total)","summary":{"zh":"非负项的有限和不小于其中任意一项。","en":"A finite sum of nonnegative terms is at least any one of its terms."},"notes":{"zh":"第二个参数须为 total=finite_set_sum(S,h)，第一个参数须为一个一元函数应用 term=h(x₀)（须核对对应关系）。前提为 x₀∈S，以及对每个 x∈S 有 0≤h(x)。结论为 term≤total。非负性要求针对全部项，而不只是被选中的一项。","en":"The second argument must be total=finite_set_sum(S,h); the first must be a unary application term=h(x₀), with that correspondence checked. Prove x₀∈S and 0≤h(x) for every x∈S. Then term≤total. Nonnegativity is required for all summands, not just the selected one."},"example":"thm summand_bound:\n    ? forall h fn(y {1, 2}) R:\n        forall z {1, 2}:\n            0 <= h(z)\n        =>:\n            h(1) <= finite_set_sum({1, 2}, h)\n    release thm finite_set_summand_le_sum(h(1), finite_set_sum({1, 2}, h))"},"SumLessEqualFromPointwise":{"kind":{"zh":"内置定理","en":"Builtin theorem"},"syntax":"sum_le_sum_from_pointwise(left, right)","summary":{"zh":"相同整数范围上的逐点不等式可以求和。","en":"A pointwise inequality on a common integer range can be summed."},"notes":{"zh":"参数须为有定义的 sum(a,b,f) 与 sum(c,d,g)，并证明 a=c、b=d，以及范围内 f(i)≤g(i)。sum 的端点为整数且 a≤b，求和项为实数。当前逐点前提对匿名函数沿其声明参数域量化，并附 a≤i≤b 条件；其余情形沿整数域量化。结论为 left≤right。","en":"The arguments must be well-defined sum(a,b,f) and sum(c,d,g), with a=c, b=d and f(i)≤g(i) on the range. Endpoints are integers with a≤b, and terms are real. The current pointwise premise quantifies over an anonymous callback’s declared parameter domain, restricted by a≤i≤b; otherwise it uses the integers. The conclusion is left≤right."},"example":"release thm sum_le_sum_from_pointwise(sum(1, 2, fn(x Z) R {x}), sum(1, 2, fn(y Z) R {y + 1}))"},"RationalHasUniqueReducedFraction":{"kind":{"zh":"内置定理","en":"Builtin theorem"},"syntax":"rational_has_unique_reduced_fraction(x)","summary":{"zh":"每个有理数有唯一的既约分数表示：分母为正整数，分子与分母互素。","en":"Every rational number has a unique reduced-fraction representation with a positive denominator and coprime numerator and denominator."},"notes":{"zh":"前提为 x∈ℚ。结论为存在且仅存在一对 p∈ℤ、d∈ℕ+，使 x=p/d 且 gcd(p,d)=1。分母取正与互素条件共同确定唯一表示；例如 0.5 对应 p=1、d=2。结果是唯一存在命题，具体分子、分母可由它取出。","en":"The premise is x∈ℚ. There is exactly one pair p∈ℤ, d∈ℕ+ with x=p/d and gcd(p,d)=1. A positive denominator and coprimality determine a unique representation; for 0.5 the pair is p=1, d=2. The result is a unique-existence proposition from which the numerator and denominator can be obtained."},"example":"release thm rational_has_unique_reduced_fraction(0.5)\nexist! p Z, d N+ st {0.5 = p / d, gcd(p, d) = 1}"},"PrimeDividesPower":{"kind":{"zh":"内置定理","en":"Builtin theorem"},"syntax":"prime_divides_power(a, k, p)","summary":{"zh":"素数 p 若整除整数 a 的正整数次幂 aᵏ，则 p 整除 a。","en":"If a prime p divides a positive integer power aᵏ of an integer a, then p divides a."},"notes":{"zh":"前提为 a∈ℤ，k,p∈ℕ+，prime(p)，以及 p∣aᵏ；结论为 p∣a。Litex 的整除谓词把被除数写在前面：dvd(a^k,p) 推出 dvd(a,p)。例如 2∣6² 可以推出 2∣6。","en":"The premises are a∈ℤ, k,p∈ℕ+, prime(p) and p∣aᵏ; the conclusion is p∣a. Litex writes the dividend first: dvd(a^k,p) gives dvd(a,p). For example, 2∣6² yields 2∣6."},"example":"$prime(2)\n$dvd(6 ^ 2, 2)\nrelease thm prime_divides_power(6, 2, 2)\n$dvd(6, 2)"},"GcdWithPrimeIsOneOrPrime":{"kind":{"zh":"内置定理","en":"Builtin theorem"},"syntax":"gcd_with_prime_is_one_or_prime(a, p)","summary":{"zh":"整数与素数的最大公因数只能是 1 或该素数。","en":"The gcd of an integer and a prime is either 1 or that prime."},"notes":{"zh":"前提为 a∈ℤ，p∈ℕ+ 且 prime(p)。结论是 gcd(a,p)=1 或 gcd(a,p)=p 的析取；a 可以为零或负数。定理本身不替调用者选择哪一个分支成立。例中 gcd(14,5)=1。","en":"The premises are a∈ℤ, p∈ℕ+ and prime(p). The conclusion is the disjunction gcd(a,p)=1 or gcd(a,p)=p; a may be zero or negative. The theorem supplies the disjunction rather than selecting a branch. In the example gcd(14,5)=1."},"example":"$prime(5)\nrelease thm gcd_with_prime_is_one_or_prime(14, 5)\ngcd(14, 5) = 1 or gcd(14, 5) = 5"},"PrimeDividesProduct":{"kind":{"zh":"内置定理","en":"Builtin theorem"},"syntax":"prime_divides_product(a, b, p)","summary":{"zh":"素数整除两个整数的积时，必整除其中至少一个因子。","en":"A prime dividing a product of two integers divides at least one factor."},"notes":{"zh":"前提为 a,b∈ℤ，p∈ℕ+，prime(p)，以及 p∣ab；结论为 p∣a 或 p∣b。Litex 中分别写作 dvd(a*b,p)、dvd(a,p) or dvd(b,p)。结论不要求两个因子都被整除，也不指定是哪一个。","en":"The premises are a,b∈ℤ, p∈ℕ+, prime(p) and p∣ab. The conclusion is p∣a or p∣b. In Litex these are dvd(a*b,p) and dvd(a,p) or dvd(b,p). At least one factor is divisible; both need not be, and the theorem does not select a factor."},"example":"$prime(3)\n$dvd(4 * 9, 3)\nrelease thm prime_divides_product(4, 9, 3)\n$dvd(4, 3) or $dvd(9, 3)"},"PrimeDivisor":{"kind":{"zh":"内置定理","en":"Builtin theorem"},"syntax":"prime_divisor(m)","summary":{"zh":"每个不小于 2 的正整数都有一个素因子。","en":"Every positive integer at least 2 has a prime divisor."},"notes":{"zh":"前提为 m∈ℕ+ 且 2≤m。结论为存在 p∈ℕ+，满足 prime(p) 且 m%p=0，因此 p∣m。返回的是存在性证明；具体素因子可用 obtain 从该命题取出。此结论不指定最小素因子或完整素因数分解。","en":"The premises are m∈ℕ+ and 2≤m. The conclusion gives some p∈ℕ+ with prime(p) and m%p=0, hence p∣m. This is an existence result; obtain can unpack a divisor. It does not specify the least prime divisor or a complete factorization."},"example":"release thm prime_divisor(12)\n\nobtain factor from exist p N+ st {$prime(p), 12 % p = 0}\n\n$dvd(12, factor)"}}};
  // END GENERATED LANGUAGE REFERENCE

  function mountReadingReader(root, options) {
    options=options||{};
    let bundle=options.document||{sources:[],statements:[],rules:[]};
    let loader=options.loader||null,generation=0,navigationSerial=0;
    let operationStatus="",operationError=false;
    let bookQuery="",bookOpen=null,bookIndex=null,bookSerial=0,bookPage=0,bookSearch,bookResults,bookStatus;
    let allOccurrencesLoaded=!loader;
    let locale=options.locale||bundle.language||"en";
    let state={source:null,statement:null,symbol:null,fact:null,wd:null,focusLine:null,explanationOpen:false};
    let history=[];
    let sources,statements,statementsBySource,facts,symbols,rules,occurrences,usedRules,evidenceNodes,inferences,wellDefinedness;
    let codePane,detailPane,rulebook,ruleGrid,ruleSearch,usedOnly,paging;
    let referencesBySource,declarationsBySource,symbolRoles,builtinTheoremSymbols,theoremApplications,symbolDefinitions,symbolBindings,symbolParameters,displayNames;
    let rulePage=0,activeRule=null;
    let rulebookState={query:"",usedOnly:true,open:false,category:"all"};
    let destroyed=false,tokenHelp=null,inferencePopover=null,proofPopover=null,proofCandidate=null,proofHoverToken=null,proofTimer=null,proofCloseTimer=null,proofFocusSuppression=null;
    let inferenceCandidate=null,inferenceTimer=null,inferenceCloseTimer=null;
    let factsBySourceLine,factSubjects,quantifiedFacts,existentialFacts,scopes,sourceIssues,issuesByLine;
    const drafts=new Map(),originals=new Map(),idePositions=new Map(),tokenHelpOpeners=new WeakMap(),tokenHelpRenderers=new WeakMap();
    let restoreIdeFocus=false;
    let revision=0,checkedRevision=0,checking=false,editError="",checkSerial=0;
    const editText=(zh,en)=>lang()==="zh"?zh:en;
    function pending(){return revision!==checkedRevision;}
    function draftContent(source){return drafts.get(source.path)??source.content??"";}
    async function checkDraft(){
      if(destroyed||checking||!options.onCheck)return;
      const request=++checkSerial,epoch=generation,submitted=revision,startedAt=navigationSerial,path=sources.get(state.source)?.path,cursor=idePositions.get(sources.get(state.source)?.path)?.start;checking=true;editError="";
      root.querySelector(".lr-editor-error")?.remove();
      const control=root.querySelector(".lr-check");if(control){control.disabled=true;control.textContent=editText("检查中…","Checking…");}root.querySelector(".lr-source-pane")?.setAttribute("aria-busy","true");
      try{
        const result=await options.onCheck({changes:Object.fromEntries(drafts),sourcePath:path,locale:lang()});
        if(destroyed||request!==checkSerial||epoch!==generation||submitted!==revision)return;
        if(result?.kind!=="reading"||!Array.isArray(result.sources)||!Array.isArray(result.statements))throw new Error(editText("检查服务没有返回可用的阅读记录。","The checker did not return usable reading records."));
        const moved=navigationSerial!==startedAt,activePath=moved?sources.get(state.source)?.path:path,activeLine=state.focusLine;
        api.update(result,{preserveDrafts:true});checkedRevision=submitted;
        let selected=[...sources.values()].find(source=>source.path===activePath);
        if(!moved&&(!selected||selected.editor_unchecked)){
          const blockedBy=[...sourceIssues.values()].find(issue=>sources.has(issue.sourceId));
          if(blockedBy)selected=sources.get(blockedBy.sourceId);
        }
        if(selected){
          const line=moved?activeLine||1:String(selected.content||"").slice(0,cursor??0).split("\n").length,entries=statementsBySource.get(selected.id)||[],issue=!moved&&[...sourceIssues.values()].find(issue=>issue.sourceId===selected.id);
          const target=(!moved&&entries.find(value=>value.status==="rejected"))||entries.filter(value=>value.line<=line).sort((a,b)=>b.line-a.line)[0]||initialStatement(selected.id);
          state.source=selected.id;state.statement=target?.id||null;state.focusLine=moved?line:issue?.line||target?.line||line;
        }
        render();if(options.onNavigate)options.onNavigate({...state},{bundle_id:bundle.bundle_id||null});
      }catch(error){if(!destroyed&&request===checkSerial&&epoch===generation&&submitted===revision)editError=error?.message||String(error);}
      finally{if(request===checkSerial){checking=false;if(!destroyed)render();}}
    }
    function renderEditor(source,sourcePane,header){
      if(!originals.has(source.path))originals.set(source.path,source.content||"");
      const check=button(checking?editText("检查中…","Checking…"):editText("检查","Check"),"lr-button lr-check",checkDraft);check.disabled=checking;sourcePane.setAttribute("aria-busy",String(checking));
      const restore=button(editText("恢复原文","Restore original"),"lr-button lr-restore",()=>{const original=originals.get(source.path);if(input.value===original)return;const start=input.selectionStart,end=input.selectionEnd;input.value=original;input.setSelectionRange(Math.min(start,original.length),Math.min(end,original.length));changed();render();root.querySelector(".lr-ide-input")?.focus({preventScroll:true});});
      restore.hidden=draftContent(source)===originals.get(source.path);
      header.append(check,restore);
      const editor=element("div","lr-ide"),canvas=element("div","lr-ide-canvas"),input=element("textarea","lr-editor-input lr-ide-input");
      input.dataset.sourcePath=source.path;input.value=draftContent(source);input.spellcheck=false;input.wrap="off";input.setAttribute("aria-label",editText("Litex 编辑器","Litex editor"));input.setAttribute("autocapitalize","off");input.setAttribute("autocomplete","off");input.setAttribute("autocorrect","off");
      codePane.classList.add("lr-ide-code");codePane.scrollTop=0;codePane.scrollLeft=0;
      canvas.append(codePane,input);editor.append(canvas);sourcePane.append(editor,element("div","lr-editor-hint",editText("悬浮查看定义与证明 · ⌘ / Ctrl + 点击跳转或固定 · ⌘ / Ctrl + Enter 检查","Hover for definitions and proof · ⌘ / Ctrl + click to follow or keep open · ⌘ / Ctrl + Enter to check")));
      const drawDraft=()=>{
        codePane.replaceChildren();
        // Unchecked text receives lexical colors only, never old symbol identities.
        for(const [i,line] of input.value.split("\n").entries()){
          const row=element("div","lr-code-row"),number=element("span","lr-line-number",String(i+1)),code=element("code","lr-source-code");
          row.dataset.line=String(i+1);
          for(const token of line.match(/#[^\n]*|\b[0-9]+(?:\.[0-9]+)?\b|[A-Za-z_][A-Za-z_0-9]*|[^A-Za-z_0-9#]+|./g)||[]){
            const role=token.startsWith("#")?"comment":lexicalKinds.get(token)||(/^\d/.test(token)?"number":"identifier");code.append(element("span","lr-syntax-"+role,token));
          }
          if(!line)code.append(document.createTextNode(" "));row.append(number,code);codePane.append(row);
        }
      };
      const remember=()=>idePositions.set(source.path,{start:input.selectionStart,end:input.selectionEnd,top:editor.scrollTop,left:editor.scrollLeft});
      editor.addEventListener("scroll",remember);input.addEventListener("select",remember);
      const changed=()=>{drafts.set(source.path,input.value);revision++;editError="";navigationSerial++;operationStatus="";operationError=false;root.querySelectorAll(".lr-operation-status").forEach(node=>node.remove());hideTokenHelp();drawDraft();remember();restore.hidden=input.value===originals.get(source.path);state.focusLine=input.value.slice(0,input.selectionStart).split("\n").length;invalidateEvidence();if(bookQuery)renderBookResults();if(options.onNavigate)options.onNavigate({...state},{bundle_id:bundle.bundle_id||null});};
      input.addEventListener("input",changed);
      // The input owns typing; semantic hover resolves against the real checked
      // tokens underneath it, using their existing help callbacks and FactIds.
      const underneath=event=>{
        input.style.pointerEvents="none";const target=document.elementFromPoint(event.clientX,event.clientY);input.style.pointerEvents="";
        return target&&codePane.contains(target)?target:null;
      };
      input.addEventListener("pointermove",event=>{
        if(pending()||source.editor_unchecked){hideTokenHelp();return;}
        const target=underneath(event),result=target?.closest(".lr-inference-toggle");if(result){hoverInferences(result);return;}leaveInferences();if(hoverProofTarget(target))return;
        const token=target?.closest(".lr-token,[data-syntax]");
        const show=token&&tokenHelpOpeners.get(token);if(show)show();else hideTokenHelp();
      });
      input.addEventListener("pointerleave",()=>{hideTokenHelp();leaveProof();leaveInferences();});
      input.addEventListener("pointerdown",event=>{
        if(pending())return;
        const target=underneath(event),action=target?.closest(".lr-inference-toggle,.lr-reference-count,.lr-inline-failure");
        const token=target?.closest(".lr-token,[data-keyword],.lr-chain-equality");
        if(action||((event.ctrlKey||event.metaKey)&&token)){event.preventDefault();event.stopPropagation();remember();(action||token).click();}
      });
      const inspectCaret=(keyword=null,open=false)=>{
        remember();if(pending()||source.editor_unchecked)return;
        const before=input.value.slice(0,input.selectionStart),line=before.split("\n").length,start=before.lastIndexOf("\n")+1;
        const owner=owningStatement(source.id,line,new TextEncoder().encode(input.value.slice(0,start)).length);
        if(state.statement===owner?.id&&state.focusLine===line&&!state.fact&&!state.symbol&&(state.keyword||null)===keyword&&(!open||state.explanationOpen))return;
        navigationSerial++;
        const lineFacts=lineProofFacts(source.id,line),fact=!keyword&&lineFacts.length===1?lineFacts[0]:null;
        closeInferences();closeProof();state={source:source.id,statement:owner?.id||null,focusLine:line,symbol:null,fact:fact?.id||null,wd:null,keyword,explanationOpen:open};
        const cited=new Set(fact?factCitations(fact):array(owner?.cited_fact_ids)),premiseLines=new Set([...cited].map(id=>factLocation(facts.get(id))).filter(value=>value.sourceId===source.id).map(value=>value.line));
        for(const row of codePane.querySelectorAll(".lr-code-row")){const number=Number(row.dataset.line);row.classList.toggle("lr-selected",number===line);row.classList.toggle("lr-premise",number!==line&&premiseLines.has(number));}
        for(const toggle of codePane.querySelectorAll(".lr-inference-toggle")){toggle.classList.remove("lr-inferred-selected");toggle.classList.toggle("lr-inferred-premise",JSON.parse(toggle.dataset.facts).some(id=>cited.has(id)));}
        codePane.querySelectorAll(".lr-symbol-selected,.lr-reference-selected").forEach(node=>node.classList.remove("lr-symbol-selected","lr-reference-selected"));
        root.querySelector(".lr-inspector-title").textContent=inspectorTitle();const presentation=statementPresentation(owner);root.querySelector(".lr-type-label").textContent=keyword||presentation.syntax||presentation.title;
        detailPane.replaceChildren();renderInspectorContents();showExplanation();
        if(options.onNavigate)options.onNavigate({...state},{bundle_id:bundle.bundle_id||null});
      };
      input.addEventListener("click",event=>{if(event.ctrlKey||event.metaKey||underneath(event)?.closest(".lr-inference-toggle,.lr-reference-count,.lr-inline-failure"))return;closeExplanation();inspectCaret();});input.addEventListener("keyup",event=>{if(["ArrowUp","ArrowDown","ArrowLeft","ArrowRight","Home","End"].includes(event.key))inspectCaret();});
      input.addEventListener("keydown",event=>{
        if(event.isComposing)return;
        if(event.key==="Escape"){hideTokenHelp();closeExplanation();return;}
        if((event.metaKey||event.ctrlKey)&&event.key==="Enter"){event.preventDefault();remember();checkDraft();}
        else if(event.key==="Tab"){event.preventDefault();input.setRangeText("    ",input.selectionStart,input.selectionEnd,"end");changed();}
        else if(event.key==="Enter"){
          const before=input.value.slice(0,input.selectionStart),line=before.slice(before.lastIndexOf("\n")+1),indent=line.match(/^ */)[0]+(line.trimEnd().endsWith(":")?"    ":"");
          event.preventDefault();input.setRangeText("\n"+indent,input.selectionStart,input.selectionEnd,"end");changed();
        }
      });
      if(pending()||source.editor_unchecked)drawDraft();
      const line=Math.max(1,state.focusLine||1),offset=input.value.split("\n").slice(0,line-1).reduce((sum,text)=>sum+text.length+1,0),position=idePositions.get(source.path);
      input.setSelectionRange(Math.min(position?.start??offset,input.value.length),Math.min(position?.end??offset,input.value.length));
      editor.scrollTop=position?.top??Math.max(0,(line-4)*24);editor.scrollLeft=position?.left??0;
      if(restoreIdeFocus)input.focus({preventScroll:true});
    }
    function invalidateEvidence(){
      closeInferences();closeExplanation();closeProof();
      state={...state,statement:null,symbol:null,fact:null,wd:null,chainStep:null,issue:null,keyword:null,reference:null};
      root.querySelectorAll(".lr-inline-inferences,.lr-definition-references,.lr-diagnostics:not(.lr-operation-status),.lr-inline-failure,.lr-editor-error,.lr-service-diagnostics").forEach(node=>node.remove());
      root.querySelectorAll(".lr-book-heading .lr-badge,.lr-book-heading .lr-origin-note").forEach(node=>node.remove());
      const heading=root.querySelector(".lr-book-heading");
      if(heading&&!heading.querySelector(".lr-pending"))heading.append(element("span","lr-pending",editText("待检查","Not checked")));
      const typeLabel=root.querySelector(".lr-type-label");if(typeLabel)typeLabel.textContent=editText("草稿","Draft");
      if(detailPane)detailPane.replaceChildren(element("p","lr-empty-note",editText("源码已修改，检查后显示新的数学含义和证明依据。","Source changed. Check it to see fresh mathematical meaning and proof grounds.")));
    }
    function lang(){return locale.startsWith("zh")?"zh":"en";}
    function t(key){return copy[lang()][key]||key;}
    function sourceTitle(source){
      for(const locale of [lang(),"en","zh"]){const title=source?.titles?.[locale];if(typeof title==="string"&&title.trim())return title;}
      return source?.path||"Litex Reading";
    }
    function statementPresentation(statement){
      const path=String(statement?.statement_kind||"").split("."),family=path[0],kind=path[path.length-1],entry=statementTypes[kind]||statementTypes[family];
      let mode={Fact:"fact",Definition:"definition",Trust:"trust",By:"proof",ReleaseAndExpand:"release",Register:"registration",Witness:"proof",ProofBlock:"proof",Command:"command"}[family]||"unknown";
      if(family==="Definition"&&path[1]==="DefineObj")mode="declaration";
      if(["DefThmStmt","DefStrategyStmt"].includes(kind))mode="proof";
      if(kind==="AxiomStmt")mode="trust";
      const hints={fact:"statementFactHint",definition:"statementDefinitionHint",declaration:"statementDeclarationHint",proof:"statementProofHint",release:"statementReleaseHint",registration:"statementRegistrationHint",trust:"statementTrustHint",command:"statementCommandHint",unknown:"typeUnavailable"};
      return {title:entry?.[lang()==="zh"?1:0]||t("statementDetails"),syntax:entry?.[2],mode,hint:t(entry?.[3]||hints[mode])};
    }
    function index(){
      sources=new Map(array(bundle.sources).map(value=>[value.id,value]));
      statements=new Map(array(bundle.statements).map(value=>[value.id,value]));
      statementsBySource=new Map();for(const value of statements.values()){if(!statementsBySource.has(value.source_id))statementsBySource.set(value.source_id,[]);statementsBySource.get(value.source_id).push(value);}
      facts=new Map(array(bundle.facts).map(value=>[value.id,value]));
      scopes=new Map(array(bundle.scopes).map(value=>[value.id,value]));
      evidenceNodes=new Map(array(bundle.evidence_nodes).map(value=>[value.id,value.node]));
      // Older exports retain some checked conclusions only on their execution
      // record. Derive display views from those exact successful results.
      for(const statement of statements.values()){
        const execution=proofResult(statement.evidence);
        if(statement.status==="accepted"&&["ExecByThmStmtSuccess","ExecReleaseThmStmtSuccess"].includes(execution.type)){
          const outputs=execution.type==="ExecByThmStmtSuccess"?[execution.fields?.stored]:array(execution.fields?.stored);
          for(const output of outputs){const stored=theoremConclusion(output),fact=stored&&facts.get(stored.id);if(!fact||fact.producer_statement_id!==statement.id)continue;
            // A direct returned conclusion belongs to this invocation, even if
            // its instantiated AST retains the declaration's source location.
            facts.set(fact.id,{...fact,role:"verified",is_primary:true,evidence:statement.evidence,source_id:statement.source_id,line:statement.line});
          }
        }
        const id=statement.mathematics?.kind==="fact"&&statement.mathematics.subject_fact_id,fact=facts.get(id);
        if(!fact||statement.status!=="accepted"||fact.producer_statement_id!==statement.id)continue;
        const record=proofResult(statement.evidence),proof={ExecByDefStmtSuccess:record.fields?.proof,ExecByThmStmtSuccess:record.fields?.selected_proof,ExecByContraStmtSuccess:statement.evidence}[record.type];
        if(!fact.evidence&&proof)facts.set(id,{...fact,role:"verified",is_primary:true,evidence:proof});
        if(record.type==="ExecByContraStmtSuccess"){
          const assumption=resolveEvidence(record.fields.reverse_assumption_fact_id),local=facts.get(assumption.fact_id);
          if(assumption.kind==="fact_reference"&&local&&local.producer_statement_id===statement.id)facts.set(local.id,{...local,role:"hypothesis",evidence:record.fields.reverse_assumption_wd});
        }
      }
      // Only primary source facts have authority over a source row. Incidental
      // instantiated facts can reuse a definition's line and must not own it.
      factsBySourceLine=new Map();
      for(const fact of facts.values())if(fact.is_primary&&fact.source_id&&fact.line&&["verified","hypothesis"].includes(fact.role)){
        const producer=statements.get(fact.producer_statement_id);
        if(fact.role==="hypothesis"&&producer?.mathematics?.kind==="predicate_definition")continue;
        const key=fact.source_id+":"+fact.line;if(!factsBySourceLine.has(key))factsBySourceLine.set(key,[]);factsBySourceLine.get(key).push(fact);
      }
      symbols=new Map(array(bundle.symbols).map(value=>[value.id,value]));
      rules=new Map(array(bundle.rules).map(value=>[value.id,value]));
      indexSourceIssues();
      inferences=new Map(array(bundle.inferences).map(value=>[value.id,value]));
      wellDefinedness=new Map(array(bundle.well_definedness).map(value=>[value.id,value]));
      occurrences=array(bundle.occurrences);
      referencesBySource=new Map();declarationsBySource=new Map();
      const spanKey=value=>[value.source_id,value.symbol_id,value.start_byte,value.end_byte].join("|"),definitions=new Set(occurrences.filter(value=>value.definition===true).map(spanKey)),seenUses=new Set();
      for(const occurrence of occurrences){
        const key=spanKey(occurrence);if(occurrence.definition!==false||definitions.has(key)||seenUses.has(key))continue;seenUses.add(key);
        if(!referencesBySource.has(occurrence.source_id))referencesBySource.set(occurrence.source_id,new Map());
        const sourceUses=referencesBySource.get(occurrence.source_id);if(!sourceUses.has(occurrence.symbol_id))sourceUses.set(occurrence.symbol_id,[]);sourceUses.get(occurrence.symbol_id).push(occurrence);
      }
      const seenDeclarations=new Set();
      for(const statement of statements.values()){
        const canonical=statement.source_statement_id||statement.id;
        let ids=array(statement.declaration_symbol_ids);
        if(!ids.length){
          ids=[...symbols.values()].filter(symbol=>symbol.definition_statement_id===canonical).map(symbol=>symbol.id);
          const model=statement.mathematics,names=model?.kind==="objects"?array(model.parameters).flatMap(param=>array(param.names)):model?.kind==="binding"?[model.name]:[];
          if(names.length)ids.push(...occurrences.filter(value=>value.source_id===statement.source_id&&value.statement_id===canonical&&value.definition&&names.includes(symbols.get(value.symbol_id)?.name)).map(value=>value.symbol_id));
        }
        for(const id of ids){const definition=occurrences.find(value=>value.source_id===statement.source_id&&value.statement_id===canonical&&value.symbol_id===id&&value.definition===true);if(!definition||seenDeclarations.has(spanKey(definition)))continue;seenDeclarations.add(spanKey(definition));if(!declarationsBySource.has(statement.source_id))declarationsBySource.set(statement.source_id,[]);declarationsBySource.get(statement.source_id).push(definition);}
      }
      symbolDefinitions=new Map();
      for(const symbol of symbols.values())if(statements.has(symbol.definition_statement_id))symbolDefinitions.set(symbol.id,statements.get(symbol.definition_statement_id));
      for(const statement of statements.values())for(const id of array(statement.declaration_symbol_ids))if(!symbolDefinitions.has(id))symbolDefinitions.set(id,statements.get(statement.source_statement_id)||statement);
      for(const occurrence of occurrences)if(occurrence.definition&&!symbolDefinitions.has(occurrence.symbol_id)&&statements.has(occurrence.statement_id))symbolDefinitions.set(occurrence.symbol_id,statements.get(occurrence.statement_id));
      // Parameter groups carry resolved symbol identities. Keep the declared
      // domain separate from any membership facts inferred later in a proof.
      symbolBindings=new Map();symbolParameters=new Map();
      for(const occurrence of occurrences)if(occurrence.definition&&!symbolBindings.has(occurrence.symbol_id))symbolBindings.set(occurrence.symbol_id,occurrence);
      for(const node of evidenceNodes.values())if(node?.type==="TypedParameterGroup"){
        const type=resolveEvidence(node.fields?.param_type),domain=resolveEvidence(type.fields?.["0"]);
        const kind={Obj:"element",Set:"set",NonemptySet:"nonempty_set",FiniteSet:"finite_set"}[type.variant];
        if(!kind||kind==="element"&&typeof domain.text!=="string")continue;
        for(const parameter of array(node.fields?.params))if(parameter.kind==="symbol_reference"&&!symbolParameters.has(parameter.symbol_id))symbolParameters.set(parameter.symbol_id,{names:[parameter.name],kind,domain:domain.text});
      }
      // Only names belonging to a recorded export and resolved symbol can be
      // shortened. Ambiguous names outside the current source stay qualified.
      displayNames=new Map();
      const configurations=new Map(array(bundle.configurations).map(value=>[value.id,value.configuration]));
      const byName=new Map();for(const symbol of symbols.values()){if(!byName.has(symbol.name))byName.set(symbol.name,new Set());byName.get(symbol.name).add(symbol.id);}
      for(const source of sources.values()){
        const names=new Map(),config=configurations.get(source.configuration_id);
        for(const [i,entry] of array(config?.exports).entries())for(const symbol of symbols.values()){
          if(!["export:"+entry.path+":"+symbol.name,"named:"+entry.path+":"+symbol.name].includes(symbol.id))continue;
          const local=[...(byName.get(symbol.name)||[])].filter(id=>symbolDefinitions.get(id)?.source_id===source.id);
          if(local.length?local.length!==1||local[0]!==symbol.id:byName.get(symbol.name)?.size!==1)continue;
          names.set("f"+i+"::"+symbol.name,symbol.name);names.set(entry.name+"::"+symbol.name,symbol.name);
        }
        displayNames.set(source.id,names);
      }
      symbolRoles=new Map();builtinTheoremSymbols=new Set();theoremApplications=new Map();factSubjects=new Map();quantifiedFacts=new Map();existentialFacts=new Map();
      for(const symbol of symbols.values()){
        const kind=symbol.kind;
        symbolRoles.set(symbol.id,symbol.id.startsWith("builtin:set:")?"type":["DefPropStmt","DefAbstractPropStmt"].includes(kind)?"predicate":["DefThmStmt","AxiomStmt","DefStrategyStmt"].includes(kind)?"theorem":["DefStructStmt","DefTemplateStmt"].includes(kind)?"type":"object");
      }
      for(const statement of statements.values())if(["HaveFnEqualStmt","HaveFnEqualCaseByCaseStmt","HaveFnByInducStmt","HaveFnByForallExistUniqueStmt","DefAlgoByCasesStmt","DefAlgoByInducStmt"].includes(String(statement.statement_kind||"").split(".").at(-1)))for(const id of array(statement.declaration_symbol_ids))symbolRoles.set(id,"function");
      const assignRole=(id,kind)=>{if(id&&(!symbolRoles.has(id)||symbolRoles.get(id)==="object"))symbolRoles.set(id,kind);};
      const inspectRole=node=>{
        if(node.fields?.fact_id?.kind==="fact_identity")factSubjects.set(node.fields.fact_id.fact_id,node);
        if(node.type==="ForallFact"&&node.fields?.fact_id?.kind==="fact_identity")quantifiedFacts.set(node.fields.fact_id.fact_id,node);
        const existVariant=node.type==="ExistShapedFact"?node.variant:["Fact","ExistOrAndChainAtomicFact"].includes(node.type)?{ExistFact:"Exist",ExistUniqueFact:"ExistUnique",NotExistFact:"NotExist"}[node.variant]:null;
        if(existVariant){const plain=resolveEvidence(node.fields?.["0"]);if(plain.type==="PlainExistFact"&&plain.fields?.fact_id?.kind==="fact_identity")existentialFacts.set(plain.fields.fact_id.fact_id,{node:plain,variant:existVariant});}
        if(node.type==="TheoremCall"){const name=resolveEvidence(node.fields?.name);if(name.kind==="symbol_reference")symbolRoles.set(name.symbol_id,"theorem");}
        if(["ExecReleaseThmStmtSuccess","ExecByThmStmtSuccess"].includes(node.type)){
          const call=resolveEvidence(node.fields?.call),name=resolveEvidence(call.fields?.name),callee=resolveEvidence(node.fields?.callee);
          if(name.kind==="symbol_reference"){
            const application=resolveEvidence(node.fields?.builtin);
            if(callee.type==="ResolvedTheoremCallee"&&callee.variant==="Builtin")builtinTheoremSymbols.add(name.symbol_id);
            if(application.type==="BuiltinThmApplication"){if(!theoremApplications.has(name.symbol_id))theoremApplications.set(name.symbol_id,[]);theoremApplications.get(name.symbol_id).push(application);}
          }
        }
        if(node.type==="FnObjHead"&&node.variant==="Identifier")assignRole(node.fields?.["0"]?.symbol_id,"function");
        if(["NormalAtomicFact","NotNormalAtomicFact"].includes(node.type))assignRole(node.fields?.predicate?.symbol_id,"predicate");
      };
      const seenRoles=new Set();for(const statement of statements.values())walkEvidence(statement.evidence,inspectRole,seenRoles);
      if(!statements.size)rulebookState.usedOnly=false;
      usedRules=new Map();
      for(const statement of statements.values())for(const id of statementRules(statement)){if(!usedRules.has(id))usedRules.set(id,new Set());usedRules.get(id).add(statement.id);}
      if(!sources.has(state.source))state.source=sources.has(bundle.entry_source_id)?bundle.entry_source_id:sources.keys().next().value||null;
      if(!pending()&&!statements.has(state.statement)){state.statement=initialStatement(state.source)?.id||null;state.focusLine=statements.get(state.statement)?.line||null;}
    }
    function initialStatement(sourceId){const entries=statementsBySource.get(sourceId)||[];return entries.find(value=>value.status==="accepted"&&array(value.cited_fact_ids).length)||entries[0];}
    function walkEvidence(value,callback,seen=new Set()){
      const pending=[value];
      while(pending.length){const node=pending.pop();if(!node||typeof node!=="object")continue;callback(node);
        if(node.kind==="evidence_reference"){const key="evidence:"+node.evidence_id;if(!seen.has(key)){seen.add(key);pending.push(evidenceNodes.get(node.evidence_id));}}
        else if(node.kind==="statement_reference"){const key="statement:"+node.statement_id;if(!seen.has(key)){seen.add(key);pending.push(statements.get(node.statement_id)?.evidence);}}
        else pending.push(...(Array.isArray(node)?node:Object.values(node)).slice().reverse());
      }
    }
    function statementRules(statement){if(Array.isArray(statement.rule_ids))return new Set(statement.rule_ids);const applied=new Set();walkEvidence(statement.evidence,node=>{if(node.rule_id)applied.add(node.rule_id);});return applied;}
    function resolveEvidence(value){const seen=new Set();while(value?.kind==="evidence_reference"){if(seen.has(value.evidence_id))return {kind:"unavailable"};seen.add(value.evidence_id);value=evidenceNodes.get(value.evidence_id);}return value||{kind:"unavailable"};}
    function factLocation(fact){const producer=statements.get(fact?.producer_statement_id);if(factInferences(fact?.id).length&&producer)return {sourceId:producer.source_id,line:producer.line};return {sourceId:fact?.source_id||producer?.source_id,line:fact?.line||producer?.line};}
    async function navigate(next, remember=true){
      if(destroyed)return false;
      const serial=++navigationSerial,epoch=generation,candidate=proofPopover?.selection||inferencePopover?.selection;
      const origin=candidate&&(next.fact!==candidate.fact||next.chainStep!==candidate.chainStep||next.statement!==candidate.statement)?candidate:null;
      const sourceId=statements.get(next.statement)?.source_id||next.source||state.source;
      try{
        if(loader&&sources.has(sourceId)&&typeof sources.get(sourceId).content!=="string"){
          operationStatus=t("loading");operationError=false;render();
          const chunk=await loader.loadSource(sourceId);
          if(destroyed||epoch!==generation)return false;
          mergeReadingChunk(bundle,chunk);index();
          if(serial!==navigationSerial)return false;
        }
        if(loader&&next.symbol&&!allOccurrencesLoaded){
          operationStatus=t("loadingIndex");operationError=false;render();
          const part=await loader.loadOccurrences();
          if(destroyed||epoch!==generation)return false;
          mergeReadingChunk(bundle,part);allOccurrencesLoaded=true;index();
          if(serial!==navigationSerial)return false;
        }
        const declaration=next.symbol&&symbolDefinitions.get(next.symbol),definitionSource=declaration&&sources.get(declaration.source_id);
        if(loader&&definitionSource&&typeof definitionSource.content!=="string"){
          const chunk=await loader.loadSource(definitionSource.id);if(destroyed||epoch!==generation)return false;
          mergeReadingChunk(bundle,chunk);index();if(serial!==navigationSerial)return false;
        }
      }catch(error){if(epoch===generation&&serial===navigationSerial&&!destroyed){operationStatus=t("loadFailed")+": "+error.message;operationError=true;render();}return false;}
      if(destroyed||epoch!==generation||serial!==navigationSerial)return false;
      operationStatus="";operationError=false;
      if(remember)history.push({...state,...origin});
      state={...state,reference:null,keyword:null,chainStep:null,issue:null,explanationOpen:false,...next};
      if(next.statement){const statement=statements.get(next.statement);if(statement)state.source=statement.source_id;}
      render();
      if(state.focusLine)root.querySelector('[data-line="'+state.focusLine+'"]')?.scrollIntoView({block:"nearest",behavior:"smooth"});
      if(options.onNavigate)options.onNavigate({...state},{bundle_id:bundle.bundle_id||null});
      return true;
    }
    function selectStatement(id,line){return navigate({statement:id,symbol:null,fact:null,wd:null,focusLine:line||statements.get(id)?.line,explanationOpen:true});}
    function selectSymbol(id,statementId,line){if(pending())return false;return navigate({symbol:id,statement:statementId||state.statement,fact:null,wd:null,focusLine:line||null,explanationOpen:true});}
    function referenceUses(symbolId,sourceId){return (referencesBySource.get(sourceId)?.get(symbolId)||[]).slice().sort((a,b)=>a.start_byte-b.start_byte);}
    function occurrenceLocation(occurrence){
      const source=sources.get(occurrence.source_id),content=source?.content;if(typeof content!=="string")return null;
      const offsets=bytePositions(content),start=offsets.get(occurrence.start_byte),end=offsets.get(occurrence.end_byte);if(start===undefined||end===undefined)return null;
      const lineStart=content.lastIndexOf("\n",start-1)+1,next=content.indexOf("\n",end),lineEnd=next<0?content.length:next;
      return {line:content.slice(0,start).split("\n").length,before:content.slice(lineStart,start),token:content.slice(start,end),after:content.slice(end,lineEnd)};
    }
    function openReferences(symbolId,sourceId,opener){
      closeInferences();
      const name=displayText(symbols.get(symbolId)?.name||"",sourceId),uses=referenceUses(symbolId,sourceId),title=t("referenceFor").replace("{name}",name),row=opener.closest(".lr-code-row");
      const node=openSourcePreview(opener,title,body=>{
        body.append(element("p","lr-empty-note",t("referenceHelp")));if(!uses.length)body.append(element("p","lr-empty-note",t("noReferences")));
        for(const occurrence of uses){const location=occurrenceLocation(occurrence);if(!location)continue;
          const link=button("","lr-reference-location",()=>navigate({source:sourceId,statement:statements.has(occurrence.statement_id)?occurrence.statement_id:null,symbol:null,fact:null,wd:null,focusLine:location.line,reference:occurrence}));
          const snippet=element("code");snippet.append(document.createTextNode(location.before),element("mark",null,location.token),document.createTextNode(location.after));link.append(element("span","lr-reference-line",t("referenceLine").replace("{line}",location.line)),snippet);body.append(link);
        }
      },{persistent:true,selection:{source:sourceId,statement:row?.dataset.statement||null,symbol:null,fact:null,wd:null,focusLine:Number(row?.dataset.line)||null,explanationOpen:false}});
      (node.querySelector(".lr-reference-location")||node.querySelector(".lr-explanation-close"))?.focus();
    }
    function closeInferences(restoreFocus=false){
      clearTimeout(inferenceTimer);clearTimeout(inferenceCloseTimer);inferenceTimer=null;inferenceCandidate=null;
      if(!inferencePopover)return;
      const {node,owner}=inferencePopover;inferencePopover=null;node.remove();owner.setAttribute("aria-expanded","false");owner.removeAttribute("aria-controls");
      if(restoreFocus)restoreSourceFocus(owner);
    }
    function leaveInferences(){
      clearTimeout(inferenceTimer);inferenceTimer=null;inferenceCandidate=null;clearTimeout(inferenceCloseTimer);
      if(inferencePopover?.transient)inferenceCloseTimer=setTimeout(closeInferences,300);
    }
    function hoverInferences(owner){
      if(pending()||proofFocusSuppression===owner||proofPopover?.persistent)return;
      clearTimeout(inferenceCloseTimer);if(inferencePopover?.owner===owner||inferenceCandidate===owner)return;
      closeInferences();inferenceCandidate=owner;
      inferenceTimer=setTimeout(()=>{inferenceTimer=null;if(!destroyed&&owner.isConnected&&inferenceCandidate===owner)openInferences(JSON.parse(owner.dataset.facts),state.source,owner,true);},450);
    }
    function positionInferences(){
      if(!inferencePopover)return;
      const {node,owner}=inferencePopover,box=owner.getBoundingClientRect();
      if(!sourceAnchorVisible(owner,box)){closeInferences();return;}
      placeAtSource(node,box);
    }
    function openInferences(ids,sourceId,owner,transient=false){
      if(inferencePopover?.owner===owner){
        clearTimeout(inferenceCloseTimer);
        if(inferencePopover.transient&&!transient){inferencePopover.transient=false;inferencePopover.node.setAttribute("role","dialog");inferencePopover.node.querySelector("summary")?.focus({preventScroll:true});return;}
        if(transient)return;closeInferences();return;
      }
      closeInferences();closeProof();closeExplanation();hideTokenHelp();
      const panel=element("div","lr-inference-popover"),id="lr-inferences-"+Math.random().toString(36).slice(2),disclosure=element("details","lr-inferred-facts"),heading=element("summary","lr-inference-heading");
      panel.id=id;panel.setAttribute("role",transient?"region":"dialog");panel.setAttribute("aria-label",t("inferredFacts"));
      const close=button("×","lr-inference-close",()=>closeInferences(true));close.setAttribute("aria-label",t("closeInferences"));
      heading.append(element("strong",null,t("inferredFacts")+" · "+ids.length));disclosure.append(heading);panel.append(disclosure,close);
      for(const factId of ids){
        const fact=facts.get(factId),text=factDisplayText(fact),result=button(text,"lr-inferred-result",()=>selectFact(factId));
        result.dataset.fact=factId;result.setAttribute("aria-label",t("inferred")+" "+text);
        if(factId===state.fact)result.classList.add("lr-inferred-selected");
        const item=element("div","lr-inferred-item");item.append(result);
        const seen=new Set();for(const origin of inferenceOrigins(factId).filter(value=>["definition","parameter_type"].includes(value.kind))){const label=inferenceOriginLabel(origin);if(seen.has(label))continue;seen.add(label);item.append(element("small","lr-inference-origin",label));}
        disclosure.append(item);
      }
      disclosure.addEventListener("toggle",positionInferences);
      panel.addEventListener("pointerenter",()=>clearTimeout(inferenceCloseTimer));panel.addEventListener("pointerleave",leaveInferences);panel.addEventListener("focusin",()=>{clearTimeout(inferenceCloseTimer);if(inferencePopover?.node===panel)inferencePopover.transient=false;});
      const row=owner.closest(".lr-code-row");
      owner.setAttribute("aria-expanded","true");owner.setAttribute("aria-controls",id);root.append(panel);inferencePopover={node:panel,owner,transient,selection:{source:sourceId,statement:row?.dataset.statement||null,symbol:null,fact:null,wd:null,chainStep:null,issue:null,focusLine:Number(row?.dataset.line)||null,explanationOpen:false}};positionInferences();
      if(!transient)heading.focus({preventScroll:true});
    }
    function factInferences(id){return array(facts.get(id)?.inference_ids).map(key=>inferences.get(key)).filter(Boolean);}
    function statementInferredFacts(statement){const published=new Set(array(statement?.produced_fact_ids));return array(statement?.inferred_fact_ids).filter(id=>published.has(id));}
    function inferenceOrigins(id){return factInferences(id).flatMap(inference=>array(inference.conclusion_origins).filter(origin=>origin.fact_id===id));}
    function inferenceOriginLabel(origin){
      const name=displayText(symbols.get(origin.source_symbol_id)?.name||"");
      if(origin.kind==="definition")return name?t("fromNamedDefinition").replace("{name}",name):t("fromDefinition");
      if(origin.kind==="parameter_type")return name?t("fromNamedParamType").replace("{name}",name):t("fromParamType");
      return origin.rule_id?t("fromRule").replace("{name}",ruleTitle(origin.rule_id)):t("originUnavailable");
    }
    function appendInferenceOrigins(target,id,interactive){
      const origins=inferenceOrigins(id);
      if(!origins.length){target.append(element("small","lr-inference-origin",t("originUnavailable")));return;}
      for(const origin of origins){
        const title=inferenceOriginLabel(origin),definition=statements.get(origin.definition_statement_id);
        const action=definition?()=>selectStatement(definition.id):rules.has(origin.rule_id)?()=>showRule(origin.rule_id):null;
        const note=interactive&&action?button(title,"lr-origin-link",action):element("small","lr-inference-origin",title);
        if(definition)note.title=sourceTitle(sources.get(definition.source_id))+" · "+t("sourceLine")+" "+definition.line;
        target.append(note);
      }
    }
    function factSelection(id,chainStep=null){const fact=facts.get(id);if(!fact)return null;const producer=statements.get(fact.producer_statement_id),location=factLocation(fact);return {statement:producer?.id||null,source:producer?.source_id||(sources.has(location.sourceId)?location.sourceId:state.source),symbol:null,fact:id,chainStep,wd:null,issue:null,focusLine:producer?(location.sourceId===producer.source_id?location.line:producer.line):(sources.has(location.sourceId)?location.line:null),explanationOpen:true};}
    function selectFact(id,chainStep=null){if(pending())return false;const selection=factSelection(id,chainStep);return selection?navigate(selection):false;}
    function selectWellDefinedness(id){if(pending())return false;const record=wellDefinedness.get(id);if(!record)return false;const producer=statements.get(record.producer_statement_id);return navigate({statement:producer?.id||null,source:producer?.source_id||state.source,symbol:null,fact:null,wd:id,focusLine:producer?.line||null,explanationOpen:true});}
    function wdCitations(record){const cited=new Set(factCitations({evidence:record?.evidence}));if(facts.has(record?.source_fact_id))cited.add(record.source_fact_id);return [...cited];}
    function factCitations(fact){const cited=new Set(),inferred=factInferences(fact?.id),outputs=new Set(inferred.flatMap(value=>array(value.fact_ids)));for(const inference of inferred)cited.add(inference.source_fact_id);for(const evidence of inferred.length?inferred.map(value=>value.evidence):[fact?.evidence])walkEvidence(evidence,node=>{if(node.kind==="fact_reference"&&node.fact_id!==fact?.id&&!outputs.has(node.fact_id)&&facts.has(node.fact_id))cited.add(node.fact_id);});return [...cited];}
    function ruleTitle(id){
      const rule=rules.get(id),friendly=rule?.category==="infer"&&rule?.family==="InferNormalAtomicFactResult"&&rule.variant==="ParamTypes"?t("parameterTypesRule"):rule?.category==="infer"&&["ExpandDefinition","Definition"].includes(rule?.variant)?t("definitionExpansionRule"):null;
      return rule?.labels?.[lang()]?.name||friendly||rule?.name||humanize(rule?.variant||id.split(".").pop());
    }
    function ruleMessage(id){const rule=rules.get(id);return rule?.labels?.[lang()]?.message||rule?.message||"";}
    function label(role){return roles[role]?.[lang()==="zh"?1:0]||humanize(role);}
    function badge(content,failed){return element("span","lr-badge"+(failed?" lr-badge-failed":""),content);}
    function section(title){const node=element("div","lr-section-label",title);detailPane.append(node);}
    function displayText(value,sourceId=state.source){
      const names=displayNames.get(sourceId);
      return String(value||"").replace(/[\p{L}_][\p{L}\p{N}_]*(?:::[\p{L}_][\p{L}\p{N}_]*)+/gu,name=>names?.get(name)||name);
    }
    function mathText(value,sourceId=state.source){return displayText(value,sourceId).replace(/<=>/g,"⇔").replace(/=>:?/g,"⇒").replace(/\$not_in\b/g,"∉").replace(/\$in\b/g,"∈").replace(/\$subset\b/g,"⊆").replace(/\$superset\b/g,"⊇").replace(/!=/g,"≠").replace(/<=/g,"≤").replace(/>=/g,"≥").replace(/\bforall\b/g,"∀").replace(/\bexist!/g,"∃!").replace(/\bexist\b/g,"∃").replace(/\$(?=[\p{L}_])/gu,"");}
    function formula(value,sourceId=state.source){return element("div","lr-formula",mathText(value,sourceId));}
    function quantifiedText(value,sourceId,ancestors=new Set()){
      const node=resolveEvidence(value);if(ancestors.has(node))return null;
      const next=new Set(ancestors);next.add(node);
      if(node.type==="Fact"&&node.variant==="ForallFact")return quantifiedText(node.fields?.["0"],sourceId,next);
      if(["Fact","ExistOrAndChainAtomicFact"].includes(node.type)&&!node.text)return quantifiedText(node.fields?.["0"],sourceId,next);
      if(node.type!=="ForallFact")return typeof node.text==="string"?mathText(node.text,sourceId):null;
      const parameters=resolveEvidence(node.fields?.typed_parameters),heads=[];
      for(const entry of array(parameters.fields?.groups)){
        const group=resolveEvidence(entry),type=resolveEvidence(group.fields?.param_type),params=array(group.fields?.params);
        if(!params.length||params.some(param=>param.kind!=="symbol_reference"))return null;
        const names=params.map(param=>displayText(param.name,sourceId)).join(", ");
        const kinds={Set:["集合","set"],NonemptySet:["非空集合","nonempty set"],FiniteSet:["有限集合","finite set"]};
        if(kinds[type.variant])heads.push(lang()==="zh"?kinds[type.variant][0]+" "+names:params.map(param=>kinds[type.variant][1]+" "+displayText(param.name,sourceId)).join(" and every "));
        else if(type.variant==="Obj"){
          const domain=resolveEvidence(type.fields?.["0"]);if(typeof domain.text!=="string")return null;
          const id=resolveEvidence(domain.fields?.["0"]).symbol_id,glyph={"builtin:set:R":"ℝ","builtin:set:Q":"ℚ","builtin:set:Z":"ℤ","builtin:set:N":"ℕ","builtin:set:C":"ℂ"}[id];
          heads.push((lang()==="zh"?" ":"")+names+" ∈ "+(glyph||mathText(domain.text,sourceId)));
        }else return null;
      }
      const premises=array(node.fields?.dom_facts).map(fact=>quantifiedText(fact,sourceId,next)),conclusions=array(node.fields?.then_facts).map(fact=>quantifiedText(fact,sourceId,next));
      if(!heads.length||!conclusions.length||[...premises,...conclusions].some(text=>text===null))return null;
      const indent=(text,width)=>text.split("\n").map(line=>" ".repeat(width)+line).join("\n");
      const header=lang()==="zh"?"对于任意"+heads.join("，以及任意")+"：":"For every "+heads.join(", and every ")+":";
      return header+"\n"+(premises.length?premises.map(text=>indent(text,4)).join("\n")+"\n    ⇒\n":"")+conclusions.map(text=>indent(text,premises.length?8:4)).join("\n");
    }
    function existentialText(fact){
      const shape=existentialFacts.get(fact?.id);if(!shape||fact.source_id&&!["ExecByThmStmtSuccess","ExecReleaseThmStmtSuccess"].includes(proofResult(fact.evidence).type))return null;
      const sourceId=factLocation(fact).sourceId,groups=array(resolveEvidence(shape.node.fields.typed_parameters).fields?.groups).map(resolveEvidence),identities=new Map(),used=new Set(),aliases=new Map();
      // A display rename is allowed only when every occurrence of a spelling
      // in this retained AST denotes that same identity. Fresh names exclude
      // both free names and authored names visible in the source.
      walkEvidence(shape.node,node=>{if(node.kind==="symbol_reference"){used.add(node.name);if(!identities.has(node.name))identities.set(node.name,new Set());identities.get(node.name).add(node.symbol_id);}});
      for(const occurrence of occurrences)if(occurrence.source_id===sourceId){const name=symbols.get(occurrence.symbol_id)?.name;if(name)used.add(name);}
      for(const group of groups)for(const param of array(group.fields?.params)){
        if(param.kind!=="symbol_reference")return null;
        if(symbolBindings.has(param.symbol_id))continue;
        if(identities.get(param.name)?.size!==1)return null;
        let name=["k","m","n","u","v","w"].find(value=>!used.has(value)),suffix=1;while(!name){if(!used.has("k"+suffix))name="k"+suffix;suffix++;}
        used.add(name);aliases.set(param.name,name);
      }
      if(!aliases.size)return null;
      const rename=text=>mathText(String(text).replace(/[\p{L}_][\p{L}\p{N}_]*(?:::[\p{L}_][\p{L}\p{N}_]*)*/gu,name=>aliases.get(name)||name),sourceId),heads=[];
      for(const group of groups){
        const type=resolveEvidence(group.fields?.param_type),names=array(group.fields?.params).map(param=>aliases.get(param.name)||displayText(param.name,sourceId)).join(", ");
        if(type.variant==="Obj"){
          const domain=resolveEvidence(type.fields?.["0"]);if(typeof domain.text!=="string")return null;
          const domainId=resolveEvidence(domain.fields?.["0"]).symbol_id,glyph={"builtin:set:Z":"ℤ","builtin:set:N":"ℕ","builtin:set:R":"ℝ","builtin:set:Q":"ℚ","builtin:set:C":"ℂ"}[domainId];
          heads.push(names+" ∈ "+(glyph||rename(domain.text)));
        }else{const kind={Set:"setKind",NonemptySet:"nonemptySetKind",FiniteSet:"finiteSetKind"}[type.variant];if(!kind)return null;heads.push(names+" "+t(kind));}
      }
      const clauses=array(shape.node.fields.facts).map(value=>{
        let node=resolveEvidence(value);const seen=new Set();
        while(!node.text&&node.fields?.["0"]&&!seen.has(node)){seen.add(node);node=resolveEvidence(node.fields["0"]);}
        return typeof node.text==="string"?rename(node.text):null;
      });
      if(!heads.length||!clauses.length||clauses.some(value=>value===null))return null;
      const prefix={Exist:["存在 ","There exists "],ExistUnique:["存在唯一的 ","There exists exactly one "],NotExist:["不存在 ","There does not exist "]}[shape.variant];if(!prefix)return null;
      return prefix[lang()==="zh"?0:1]+heads.join(", ")+(lang()==="zh"?"，使得：":" such that:")+"\n"+clauses.map(value=>value.split("\n").map(line=>"    "+line).join("\n")).join("\n    ∧ ");
    }
    function factDisplayText(fact){
      const sourceId=factLocation(fact).sourceId,node=quantifiedFacts.get(fact?.id);
      return existentialText(fact)||(node&&quantifiedText(node,sourceId))||mathText(fact?.text||"",sourceId);
    }
    function factFormula(fact){return element("div","lr-formula",factDisplayText(fact));}
    function latexFormula(value,display,sourceId=state.source){
      if(typeof value!=="string"||!global.katex?.render)return null;
      // Generated identifiers are escaped inside mathit; keep the surrounding
      // LaTeX structure intact, including scopes and every mathematical clause.
      value=value.replace(/\\mathit\{((?:\\_|[\p{L}\p{N}:_])+)\}/gu,(whole,name)=>{
        const plain=name.replace(/\\_/g,"_"),short=displayText(plain,sourceId);
        return short===plain?whole:"\\mathit{"+short.replace(/_/g,"\\_")+"}";
      });
      const node=element("div","lr-latex");
      // The retained display compiler uses a root gathered environment for
      // quantified comparisons. Align only that outer layout, never matrices.
      if(value.startsWith("\\begin{gathered}"))node.classList.add("lr-latex-gathered");
      // Fold only the display compiler's two-row outer alignment. Nested
      // environments (matrices, cases, etc.) keep their original layout.
      const aligned=/^\\begin\{aligned\}&([\s\S]*)\\end\{aligned\}$/.exec(value);
      if(aligned&&!aligned[1].includes("\\begin{")&&aligned[1].split("\\\\&").length===2){value=aligned[1].replace("\\\\&","\\ ");display=false;node.classList.add("lr-latex-inline");}
      try{global.katex.render(value,node,{displayMode:display,throwOnError:true,trust:false,strict:"ignore",maxExpand:500,maxSize:50,output:"htmlAndMathml"});return node;}catch(_){return null;}
    }
    function renderPredicateLatex(model,sourceId,target=detailPane){
      const data=model.latex,domains=array(data?.parameters),clauses=array(data?.facts);
      const parameterCount=array(model.parameters).reduce((count,param)=>count+(typeof param==="string"?1:array(param.names).length),0);
      if(!clauses.length||clauses.length!==array(model.facts).length||domains.length!==parameterCount)return false;
      const domainNodes=domains.map(value=>latexFormula(value,false,sourceId)),clauseNodes=clauses.map(value=>latexFormula(value,true,sourceId));
      if([...domainNodes,...clauseNodes].some(value=>!value))return false;
      const linked=(node,id,className)=>{if(!facts.has(id)){node.classList.add(className);return node;}const link=button("","lr-math-fact "+className,()=>selectFact(id));link.append(node);if(id===state.fact){link.classList.add("lr-current-math");link.setAttribute("aria-current","true");}return link;};
      const conditions=predicateIntro(model,sourceId,target);
      if(domainNodes.length){const row=element("div","lr-predicate-domains");domainNodes.forEach((node,index)=>{const item=element("span","lr-domain-item");item.append(linked(node,array(model.parameter_fact_ids)[index],"lr-latex-domain"));if(index<domainNodes.length-1)item.append(element("span","lr-domain-comma",","));row.append(item);});conditions.append(row);}
      clauseNodes.forEach((node,index)=>{const row=element("div","lr-condition-row");row.append(element("span","lr-condition-join",index?"∧":""),linked(node,array(model.fact_ids)[index],"lr-latex-clause"));conditions.append(row);});return true;
    }
    function predicateIntro(model,sourceId,target=detailPane){
      const intro=element("div","lr-iff-intro");
      intro.append(latexFormula(model.latex?.subject,false,sourceId)||formula(model.subject,sourceId));
      const conditions=element("div","lr-predicate-conditions");
      const body=element("div","lr-iff-body");
      body.append(latexFormula("\\Longleftrightarrow",false)||element("span","lr-equivalence-operator","⇔"),conditions);
      target.append(intro,body);return conditions;
    }
    function mathFact(value,id,sourceId){
      if(!facts.has(id))return formula(value,sourceId);
      const node=button("","lr-math-fact",()=>selectFact(id));node.append(quantifiedFacts.has(id)?factFormula(facts.get(id)):formula(value,sourceId));
      if(id===state.fact){node.classList.add("lr-current-math");node.setAttribute("aria-current","true");}return node;
    }
    function parameterText(group,sourceId){const names=array(group.names).join(", ");return group.kind==="element"?names+" ∈ "+mathText(group.domain,sourceId):names+" "+t({set:"setKind",nonempty_set:"nonemptySetKind",finite_set:"finiteSetKind"}[group.kind]||"unavailable");}
    function appendPredicateMeaning(target,model,sourceId){
      if(model.latex){if(renderPredicateLatex(model,sourceId,target))return;target.append(element("p","lr-empty-note",t("typesettingUnavailable")));}
      const params=array(model.parameters),clauses=array(model.facts);
      if(!clauses.length){target.append(element("p","lr-empty-note",t("meaningUnavailable")));return;}
      const conditions=predicateIntro(model,sourceId,target);
      if(params.length){const row=element("div","lr-predicate-domains");params.forEach((param,index)=>{const text=typeof param==="string"?param:array(param.names).join(", ")+(param.kind==="element"?" ∈ "+mathText(param.domain,sourceId):" : "+param.kind),item=element("span","lr-domain-item");item.append(mathFact(text,array(model.parameter_fact_ids)[index],sourceId));if(index<params.length-1)item.append(element("span","lr-domain-comma",","));row.append(item);});conditions.append(row);}
      clauses.forEach((fact,index)=>{const row=element("div","lr-condition-row");row.append(element("span","lr-condition-join",index?"∧":""),mathFact(fact,array(model.fact_ids)[index],sourceId));conditions.append(row);});
    }
    function renderMath(model,sourceId=state.source){
      if(!model||typeof model!=="object")return false;
      const params=array(model.parameters);if(params.length&&!["predicate_definition","predicate_equivalence"].includes(model.kind)){section(t(model.kind==="objects"?"takeObjects":"parameterRange"));params.forEach((param,index)=>detailPane.append(mathFact(typeof param==="string"?param:parameterText(param,sourceId),array(model.parameter_fact_ids)[index],sourceId)));}
      const clauses=array(model.facts);
      if(["predicate_definition","predicate_equivalence"].includes(model.kind)){
        appendPredicateMeaning(detailPane,model,sourceId);return true;
      }
      if(model.kind==="abstract_predicate"){detailPane.append(formula(model.subject,sourceId),element("p","lr-empty-note",t("abstractMeaning")));return true;}
      if(model.kind==="objects"){
        const names=params.flatMap(param=>array(param.names)),values=array(model.values);if(values.length===names.length)values.forEach((value,index)=>detailPane.append(formula(names[index]+" = "+value,sourceId)));
        if(clauses.length){section(t("alsoSatisfies"));clauses.forEach(fact=>detailPane.append(formula(fact,sourceId)));}return true;
      }
      if(model.kind==="binding"){detailPane.append(formula(model.name+" = "+model.value,sourceId));return true;}
      if(model.kind==="function"){
        const domain=array(model.domain_facts);if(domain.length){section(t("alsoSatisfies"));domain.forEach(fact=>detailPane.append(formula(fact,sourceId)));}detailPane.append(formula(model.subject,sourceId));section(t("valueRange"));detailPane.append(formula(model.codomain,sourceId));return true;
      }
      if(model.kind==="fact"){detailPane.append(quantifiedFacts.has(model.subject_fact_id)?factFormula(facts.get(model.subject_fact_id)):formula(model.subject,sourceId));return true;}
      if(model.kind==="facts"){clauses.forEach(fact=>detailPane.append(formula(fact,sourceId)));return true;}
      return false;
    }
    function statementEquivalence(statement){
      const meaning=statement?.mathematics;if(meaning?.kind!=="fact")return null;
      const candidates=[...inferences.values()].filter(inference=>inference.producer_statement_id===statement.id&&inference.mathematics?.kind==="predicate_equivalence"&&(inference.source_fact_id===meaning.subject_fact_id||facts.get(inference.source_fact_id)?.text===meaning.subject));
      return candidates.length===1?candidates[0].mathematics:null;
    }
    function definitionLinks(ids){
      const links=element("div","lr-math-links");for(const id of new Set(ids)){const target=statements.get(id);if(!target)continue;const name=[...symbols.values()].find(symbol=>symbol.definition_statement_id===(target.source_statement_id||target.id))?.name||statementPresentation(target).title;links.append(button(t("viewDefinition").replace("{name}",name),"lr-math-link",()=>selectStatement(id)));}if(links.childElementCount)detailPane.append(links);
    }
    function renderStatus(statement){if(statement?.status==="rejected")detailPane.append(element("p","lr-origin-note",t("unverifiedMeaning")));else if(statement?.status==="not_exported")detailPane.append(element("p","lr-empty-note",t("unexecutedMeaning")));if(statement)renderOrigin(statement);}

    function renderPropGuide(target){
      const guide=element("div","lr-prop-guide"),example=element("pre","lr-guide-example");
      example.append(element("code",null,"prop nonnegative(x R):\n    x >= 0\n\nby def $nonnegative(3)"));
      guide.append(element("p",null,t("propGuidePurpose")),element("p",null,t("propGuideUse")),element("div","lr-section-label",t("propGuideExample")),example,element("p",null,t("propGuideMeaning")),element("p",null,t("propGuideProof")));
      target.append(guide);
    }

    function theoremReference(id){
      if(!builtinTheoremSymbols.has(id))return null;
      const zh=lang()==="zh",application=(theoremApplications.get(id)||[])[0],theorem=resolveEvidence(application?.fields?.theorem),name=symbols.get(id)?.name||"";
      if(theorem.type==="BuiltinTheoremId"){const reference=referenceCard("thm:"+theorem.variant);if(reference)return reference;}
      return {kind:zh?"内置定理":"Builtin theorem",syntax:name,summary:zh?"由 Litex 提供的定理。release thm 验证其实例化前提，并将结论引入当前证明上下文。":"A theorem provided by Litex. release thm verifies its instantiated premises and introduces its conclusions into the current proof context."};
    }
    function referenceCard(name){
      if(typeof name!=="string")return null;
      const zh=lang()==="zh",own=(table)=>Object.prototype.hasOwnProperty.call(table,name)?table[name]:null,set=own(setOperatorHelp),builtin=own(builtinObjectHelp),keyword=own(keywordReference);
      const table=name.startsWith("stmt:")?languageReference.statements:name.startsWith("thm:")?languageReference.builtin_theorems||{}:languageReference.entries,key=name.startsWith("stmt:")?name.slice(5):name.startsWith("thm:")?name.slice(4):name,authored=Object.prototype.hasOwnProperty.call(table,key)?table[key]:null;
      if(authored){const locale=zh?"zh":"en",leaf=name.startsWith("stmt:")?name.slice(5):null,guide=keyword||(["DefPropStmt","ByDefStmt","ByContraStmt","ReleaseThmStmt","HaveFnEqualStmt","ClaimStmt"].includes(leaf)?keywordReference[statementTypes[leaf]?.[2]]:null);return {kind:authored.kind[locale],syntax:authored.syntax,summary:authored.summary[locale],notes:authored.notes[locale],example:authored.example||guide?.example,walkthrough:guide?.walkthrough?.[locale]};}
      if(set)return {kind:zh?"集合运算符":"Set operator",syntax:set[0],summary:set[zh?3:4],input:set[zh?1:2],example:set[5]};
      if(builtin)return {kind:zh?"函数":"Function",syntax:builtin[0],summary:builtin[zh?2:3],input:builtin[1],example:builtin[4]};
      if(keyword){const text=keyword[zh?"zh":"en"];return {kind:text[0],syntax:keyword.syntax,summary:text[1],notes:text[2],example:keyword.example,walkthrough:keyword.walkthrough?.[zh?"zh":"en"]};}
      return null;
    }
    function appendReference(target,card,compact=false){
      target.append(element("small","lr-reference-kind",card.kind),element("p","lr-reference-summary",card.summary),element("pre","lr-reference-syntax",card.syntax));
      if(card.input)target.append(element("small",null,lang()==="zh"?"输入与结果":"Inputs and result"),element("div","lr-builtin-domain",card.input));
      if(card.notes)target.append(element("p","lr-reference-notes",card.notes));
      if(card.example)target.append(element("small",null,lang()==="zh"?"例子":"Example"),element("pre","lr-reference-example",card.example));
      if(card.walkthrough){
        if(compact)target.append(element("small","lr-reference-hint",lang()==="zh"?"点击关键词查看例子的逐项解释。":"Click the keyword for a point-by-point explanation."));
        else{
          const explanation=element("dl","lr-reference-walkthrough");
          for(const [title,text,latex,plain] of card.walkthrough){
            const body=element("dd");body.append(element("p",null,text));
            if(latex)body.append(latexFormula(latex,true)||element("div","lr-formula",plain||latex));
            explanation.append(element("dt",null,title),body);
          }
          target.append(explanation);
        }
      }
    }
    function selectedReferenceCard(){
      const token=Array.from(codePane.querySelectorAll("[data-keyword]")).find(node=>node.dataset.keyword===state.keyword&&Number(node.closest(".lr-code-row")?.dataset.line)===state.focusLine);
      return referenceCard(token?.dataset.referenceKey||state.keyword);
    }
    function renderInspectorContents(){if(state.issue)appendSourceIssue(detailPane,sourceIssues.get(state.issue));else if(state.keyword&&selectedReferenceCard())appendReference(detailPane,selectedReferenceCard());else if(state.keyword==="prop")renderPropGuide(detailPane);else if(state.keyword){detailPane.append(element("p","lr-keyword-meaning",syntaxPhrases[state.keyword]?.[lang()==="zh"?0:1]||syntaxHelp[state.keyword]?.[lang()==="zh"?0:1]||t("typeUnavailable")));}else if(state.symbol)renderSymbol();else if(state.wd)renderWellDefinedness();else if(state.fact)renderFact();else if(!state.statement&&state.focusLine)renderSourceLine();else renderStatement();}

    function render(){
      if(destroyed)return;
      const previousInput=root.querySelector(".lr-ide-input"),previousEditor=root.querySelector(".lr-ide");
      restoreIdeFocus=previousInput===document.activeElement;
      if(previousInput&&previousEditor)idePositions.set(previousInput.dataset.sourcePath,{start:previousInput.selectionStart,end:previousInput.selectionEnd,top:previousEditor.scrollTop,left:previousEditor.scrollLeft});
      closeInferences();hideTokenHelp();closeProof();root.replaceChildren();root.classList.add("lr-root");
      const toolbar=element("div","lr-toolbar");
      const titleBlock=element("div","lr-title-block");const heading=element("div","lr-book-heading");titleBlock.append(heading);toolbar.append(titleBlock);
      const actions=element("div","lr-toolbar-actions");
      const back=button("←","lr-button lr-back",async()=>{const previous=history.pop();if(previous&&!await navigate(previous,false))history.push(previous);});back.setAttribute("aria-label",t("back"));if(history.length)actions.append(back);
      const source=sources.get(state.source);
      heading.append(element("h1","lr-book-title",sourceTitle(source)));
      if(source?.editor_unchecked){const blocked=bundle.run_result==="failure",pending=element("span","lr-pending",blocked?editText("本章待检查：上文未通过","Chapter not checked: earlier steps failed"):editText("本章待检查","Chapter not checked"));pending.title=blocked?editText("此次检查尚未执行到本章。先处理前面章节未通过的步骤，再检查本章。","This check did not reach this chapter. Resolve the earlier rejected steps, then check this chapter."):editText("此次检查只执行到前面的章节。检查本章以继续。","This check covered the preceding chapters. Check this chapter to continue.");heading.append(pending);}
      else if(sources.size){const passed=bundle.run_result==="success",label=sources.size>1?(passed?editText("本次检查通过","Last check passed"):editText("本次检查未通过","Last check failed")):(passed?t("verified"):t("failed"));heading.append(badge(label,!passed));}
      const trustCount=array(bundle.trust_summary?.user_assumptions).length+array(bundle.trust_summary?.axioms).length;if(trustCount)heading.append(element("span","lr-origin-note",t("trust")+" · "+trustCount));
      const records=element("details","lr-records lr-reading-help"),recordsSummary=element("summary",null,t("readingHelp")),recordPanel=element("div","lr-record-panel"),recordActions=element("div","lr-record-actions");
      records.append(recordsSummary,recordPanel);
      recordPanel.append(element("p",null,t("hint")));
      const legend=element("div","lr-legend");for(const key of ["selectedLegend","premiseLegend","occurrenceLegend","inferred"])legend.append(element("span",null,t(key)));recordPanel.append(legend);
      recordPanel.append(element("p",null,t("recordExplanation")),element("p","lr-record-format",t("recordFileExplanation")),recordActions);
      if(options.onOpenFiles)actions.append(button(t("openFiles"),"lr-button lr-open-file",()=>{records.open=false;options.onOpenFiles();}));
      if(options.onOpenProject)recordActions.append(button(t("openProject"),"lr-button",()=>{records.open=false;options.onOpenProject();}));
      records.addEventListener("keydown",event=>{if(event.key==="Escape"&&records.open){records.open=false;recordsSummary.focus();event.stopPropagation();}});
      const advanced=element("details","lr-advanced-help");advanced.append(element("summary",null,t("advancedHelp")),button(t("rulebook"),"lr-math-link",()=>{if(!rulebook?.isConnected)renderRulebook();rulebook.open=true;records.open=false;rulebook.scrollIntoView({block:"nearest",behavior:"smooth"});}));recordPanel.append(advanced);
      const footer=element("footer","lr-reading-footer");footer.append(records);
      if(sources.size)renderBookNavigation(actions);toolbar.append(actions);root.append(toolbar);
      if(operationStatus){const notice=element("p",(operationError?"lr-diagnostics":"lr-loading")+" lr-operation-status",operationStatus);notice.setAttribute("role",operationError?"alert":"status");root.append(notice);}
      const hasLocatedFailure=[...sourceIssues.values()].some(issue=>issue.statementId),serviceDiagnostics=[];
      const unmapped=array(bundle.diagnostics).filter((diagnostic,index)=>{if(sourceIssues.has("diagnostic:"+index))return false;if(diagnostic.kind==="execution"&&hasLocatedFailure){serviceDiagnostics.push(diagnostic);return false;}return true;});
      if(serviceDiagnostics.length){const details=element("details","lr-service-diagnostics");details.append(element("summary",null,editText("检查服务说明","Checking service details")));for(const diagnostic of serviceDiagnostics)details.append(element("pre",null,diagnostic.summary||diagnostic.message||diagnostic.kind));recordPanel.append(details);}
      if(unmapped.length){const diagnostics=element("div","lr-diagnostics");diagnostics.setAttribute("role","status");for(const diagnostic of unmapped)diagnostics.append(element("div",null,diagnostic.summary||diagnostic.message||diagnostic.kind));root.append(diagnostics);}
      if(!sources.size){const empty=element("section","lr-empty");const mark=element("div","lr-empty-mark","∀");mark.setAttribute("aria-hidden","true");empty.append(mark,element("h2",null,t("empty")),element("p",null,t("emptyHint")));root.append(empty,footer);return;}
      const layout=element("div","lr-layout");
      const sourcePane=element("section","lr-source-pane");const header=element("div","lr-pane-header");header.append(element("span",null,options.onCheck?editText("编辑器","Editor"):t("source")));
      codePane=element("div","lr-code");sourcePane.append(header,codePane);
      const presentation=statementPresentation(statements.get(state.statement)),selectedFact=facts.get(state.fact);
      const typeTitle=state.keyword?state.keyword:state.symbol?t("concepts"):state.wd?t("wellDefined"):state.fact?t(factInferences(state.fact).length?"inferred":selectedFact?.role==="verified"?"verifiedFact":selectedFact?.role||"fact"):presentation.title;
      const syntax=state.keyword||state.symbol||state.wd||state.fact?typeTitle:presentation.syntax||typeTitle;
      const details=element("section","lr-details"),inspectorHeader=element("div","lr-pane-header lr-inspector-header");
      inspectorHeader.append(element("span","lr-inspector-title",inspectorTitle()),element("span","lr-type-label",syntax));details.append(inspectorHeader);
      const close=button("×","lr-explanation-close",()=>closeExplanation(true));close.setAttribute("aria-label",editText("关闭说明","Close explanation"));inspectorHeader.append(close);
      details.classList.add("lr-context-explanation");details.setAttribute("role","region");details.setAttribute("aria-label",editText("源码说明","Source explanation"));details.hidden=!state.explanationOpen;
      detailPane=element("div","lr-detail-body");detailPane.setAttribute("aria-live","polite");details.append(detailPane);
      layout.append(sourcePane,details);root.append(layout,footer);
      renderCode();renderInspectorContents();
      if(options.onCheck){renderEditor(source,sourcePane,header);if(pending())invalidateEvidence();
        if(editError){const error=element("p","lr-editor-error",editText("检查未完成：","Check did not complete: ")+editError);error.setAttribute("role","alert");sourcePane.append(error);}}
      showExplanation();
    }

    function owningStatement(sourceId,line,offset){
      const candidates=(statementsBySource.get(sourceId)||[]).filter(value=>value.line<=line&&value.end_byte>value.start_byte&&value.end_byte>offset);
      if(!candidates.length)return null;
      const width=candidates.reduce((size,value)=>Math.min(size,value.end_byte-value.start_byte),Infinity);
      const narrow=candidates.filter(value=>value.end_byte-value.start_byte===width);
      const selected=narrow.find(value=>value.id===state.statement);if(selected)return selected;
      const ancestors=new Set();let current=statements.get(state.statement);while(current&&!ancestors.has(current.id)){ancestors.add(current.id);current=statements.get(current.parent_statement_id);}
      return narrow.find(value=>ancestors.has(value.parent_statement_id))||narrow.find(value=>value.id===(value.source_statement_id||value.id))||narrow[0];
    }

    function selectBookLine(entry){
      bookOpen=false;return navigate({source:entry.source_id,statement:entry.statement_id||null,symbol:null,fact:null,wd:null,focusLine:entry.line});
    }

    function renderBookNavigation(target){
      const details=element("details","lr-book-nav");details.open=bookOpen??false;details.addEventListener("toggle",()=>{bookOpen=details.open;});details.append(element("summary",null,t("book")));
      const chapters=element("nav","lr-chapters");chapters.setAttribute("aria-label",t("chapters"));
      const dependencies=element("details","lr-book-dependencies");dependencies.open=sources.get(state.source)?.role==="dependency";const dependencyLinks=element("div","lr-chapters");let dependencyCount=0;
      for(const source of sources.values()){
        const link=button(sourceTitle(source),"lr-chapter"+(source.id===state.source?" lr-active-chapter":""),()=>{bookOpen=false;const first=initialStatement(source.id);return navigate({source:source.id,statement:first?.id||null,symbol:null,fact:null,wd:null,focusLine:first?.line||1});});
        if(source.id===state.source)link.setAttribute("aria-current","page");
        if(source.role==="dependency"){dependencyLinks.append(link);dependencyCount++;}else chapters.append(link);
      }
      const panel=element("div","lr-book-panel");details.append(panel);
      // Optional host-authored links to independent reading bundles. Failed
      // examples must never be merged into the verified chapter sequence.
      for(const group of array(options.exampleGroups)){
        const links=element("nav","lr-chapters lr-extra-examples"),label=group.titles?.[lang()]||group.titles?.en||group.titles?.zh;
        if(!label)continue;links.setAttribute("aria-label",label);
        for(const entry of array(group.items)){
          const href=entry.hrefs?.[lang()]||entry.href;
          if(typeof href!=="string"||!href||!/^(?:\.\.\/)*(?:[A-Za-z0-9_-]+\/)*$/.test(href))continue;
          const title=entry.titles?.[lang()]||entry.titles?.en||entry.titles?.zh;if(!title)continue;
          const link=element("a","lr-chapter",title);link.href=href+(global.location?.protocol==="file:"?"index.html":"")+"?lang="+lang();links.append(link);
        }
        if(group.includeSources===true)links.prepend(...Array.from(chapters.childNodes));
        if(links.childElementCount){const category=element("section","lr-example-group");category.append(element("div","lr-section-label",label),links);panel.append(category);}
      }
      if(chapters.childElementCount)panel.append(chapters);if(dependencyCount){dependencies.append(element("summary",null,t("dependencies")+" · "+dependencyCount),dependencyLinks);panel.append(dependencies);}
      const tools=element("div","lr-book-search");bookSearch=element("input");bookSearch.type="search";bookSearch.placeholder=t("bookSearch");bookSearch.setAttribute("aria-label",t("bookSearch"));bookSearch.value=bookQuery;bookStatus=element("output","lr-empty-note");bookStatus.setAttribute("aria-live","polite");tools.append(bookSearch,bookStatus);bookResults=element("div","lr-book-results");panel.append(tools,bookResults);target.append(details);
      details.addEventListener("keydown",event=>{if(event.key==="Escape"){details.open=false;details.querySelector("summary").focus();}});
      bookSearch.addEventListener("input",()=>{bookQuery=bookSearch.value;bookPage=0;renderBookResults();});if(bookQuery)renderBookResults();
    }

    async function renderBookResults(){
      const serial=++bookSerial,epoch=generation,query=bookQuery.trim().toLowerCase();
      bookResults.replaceChildren();bookStatus.textContent="";if(!query)return;
      if(bookIndex===null){
        bookStatus.textContent=t("loadingIndex");
        try{
          if(loader){const part=await loader.loadSearch();if(destroyed||epoch!==generation)return;bookIndex=array(part.entries);}
          else{
            bookIndex=[];const encoder=new TextEncoder();
            for(const source of sources.values()){let offset=0;for(const [index,line] of String(source.content||"").split("\n").entries()){if(line.trim()){const owner=owningStatement(source.id,index+1,offset);bookIndex.push({source_id:source.id,line:index+1,text:line,statement_id:owner?.source_statement_id||owner?.id||null});}offset+=encoder.encode(line).length+1;}}
          }
        }catch(error){if(epoch===generation&&serial===bookSerial){bookStatus.textContent=t("loadFailed")+": "+error.message;}return;}
      }
      if(destroyed||epoch!==generation||serial!==bookSerial)return;
      // The retained index owns checked source; the existing draft map owns
      // working-copy text. Draft lines carry no execution statement identity.
      const bySource=new Map();for(const entry of bookIndex){if(!bySource.has(entry.source_id))bySource.set(entry.source_id,[]);bySource.get(entry.source_id).push(entry);}
      for(const source of sources.values())if(drafts.has(source.path)&&drafts.get(source.path)!==source.content){
        bySource.set(source.id,drafts.get(source.path).split("\n").flatMap((text,index)=>text.trim()?[{source_id:source.id,line:index+1,text,statement_id:null}]:[]));
      }
      const entries=[...sources.keys()].flatMap(id=>bySource.get(id)||[]);
      const matches=entries.filter(entry=>[entry.text,sourceTitle(sources.get(entry.source_id)),...Object.values(sources.get(entry.source_id)?.titles||{}).filter(value=>typeof value==="string"),sources.get(entry.source_id)?.path].join(" ").toLowerCase().includes(query));
      const pageSize=24,pages=Math.max(1,Math.ceil(matches.length/pageSize));bookPage=Math.min(bookPage,pages-1);bookStatus.textContent=matches.length?matches.length+" · "+(bookPage+1)+" / "+pages:t("noMatches");
      for(const entry of matches.slice(bookPage*pageSize,(bookPage+1)*pageSize)){
        const result=button("","lr-fact-link lr-book-result",()=>selectBookLine(entry));result.append(element("code",null,entry.text),element("small",null,sourceTitle(sources.get(entry.source_id))+" · "+t("sourceLine")+" "+entry.line));bookResults.append(result);
      }
      if(pages>1){const paging=element("div","lr-rule-paging"),previous=button("← "+t("previous"),"lr-button",()=>{bookPage--;renderBookResults();}),next=button(t("next")+" →","lr-button",()=>{bookPage++;renderBookResults();});previous.disabled=bookPage===0;next.disabled=bookPage+1>=pages;paging.append(previous,next);bookResults.append(paging);}
    }

    function renderSourceLine(){detailPane.append(element("p","lr-empty-note",t("noStatement")));}

    function lineProofFacts(sourceId,line){return factsBySourceLine.get(sourceId+":"+line)||[];}
    function indexSourceIssues(){
      sourceIssues=new Map();issuesByLine=new Map();
      const add=issue=>{
        const source=sources.get(issue.sourceId);if(!source||!Number.isInteger(issue.line)||issue.line<1)return;
        if(typeof source.content==="string"&&issue.line>source.content.split("\n").length)return;
        sourceIssues.set(issue.id,issue);const key=issue.sourceId+":"+issue.line;if(!issuesByLine.has(key))issuesByLine.set(key,[]);issuesByLine.get(key).push(issue);
      };
      array(bundle.diagnostics).forEach((diagnostic,index)=>{if(diagnostic.source_id)add({id:"diagnostic:"+index,sourceId:diagnostic.source_id,line:diagnostic.line,column:diagnostic.column,phase:diagnostic.phase,message:diagnostic.summary||diagnostic.message});});
      for(const statement of statements.values())if(statement.status==="rejected"){
        const failure=statement.failure||{},location=failure.source_location?.source_id?failure.source_location:failedSourceLocation(statement.evidence),located=location?.source_id&&sources.has(location.source_id)&&Number.isInteger(location.line);
        add({id:"statement:"+statement.id,statementId:statement.id,sourceId:located?location.source_id:statement.source_id,line:located?location.line:statement.line,column:located?location.column:null,phase:failure.phase,category:failure.category,obligation:failure.obligation||failure.goal,expression:failure.expression,message:failure.message,statementStart:!located});
      }
    }
    function failedAtomicVerification(evidence){
      let node=resolveEvidence(evidence);const seen=new Set();
      while(node&&typeof node==="object"&&!seen.has(node)){
        seen.add(node);const fields=node.fields||{};
        if(["VerifyAtomicExceptEqualityFactFailed","VerifyEqualityFailed"].includes(node.type))return node;
        const failed=fields.failed_then||fields.failed_adjacent||fields.failed_statement||fields.failure;
        if(failed){node=resolveEvidence(failed);continue;}
        if(!fields["0"])return null;node=resolveEvidence(fields["0"]);
      }
      return null;
    }
    function failedSourceLocation(evidence){
      let node=resolveEvidence(evidence);const seen=new Set();
      while(node&&typeof node==="object"&&!seen.has(node)){
        seen.add(node);const fields=node.fields||{},failed=fields.failed_then||fields.failed_adjacent||fields.failed_statement||fields.failure;
        if(failed){node=resolveEvidence(failed);continue;}
        if(["VerifyAtomicExceptEqualityFactFailed","VerifyEqualityFailed","VerifyChainFactFailed"].includes(node.type)&&fields.fact){
          let fact=resolveEvidence(fields.fact);const wrapped=new Set();
          while(fact&&!wrapped.has(fact)){wrapped.add(fact);if(fact.fields?.line_file?.source_id)return fact.fields.line_file;if(!fact.fields?.["0"])break;fact=resolveEvidence(fact.fields["0"]);}
          return null;
        }
        if(!fields["0"])return null;node=resolveEvidence(fields["0"]);
      }
      return null;
    }
    function sourceIssueLabel(issue){
      return issue.phase==="parse"?editText("本行无法解析","This line could not be parsed"):issue.obligation?editText("尚未证明：","Not established: ")+mathText(issue.obligation,issue.sourceId):editText("此语句尚未通过","This statement was not accepted");
    }
    function appendSourceIssue(target,issue,includeDefinition=true){
      if(!issue){target.append(element("p","lr-empty-note",t("unavailable")));return;}
      const statement=statements.get(issue.statementId);if(includeDefinition&&statement&&appendPredicateDefinition(target,{source_id:issue.sourceId,evidence:statement.evidence}))target.append(element("h4","lr-proof-section-title",editText("检查结果","Check result")));
      const formation=issue.phase==="well_defined"||issue.category==="well_defined";
      target.append(element("p","lr-failure-summary",issue.phase==="parse"?editText("本行尚未解析为 Litex 语句。","This line has not been parsed as a Litex statement."):formation?editText("这个表达式所需的条件尚未建立。","A condition required by this expression has not been established."):editText("当前证明尚未建立这个结论。","The current proof has not established this conclusion.")));
      if(issue.expression)target.append(formula(issue.expression,issue.sourceId));
      if(issue.obligation)target.append(formula(issue.obligation,issue.sourceId));
      if(issue.message){
        const message=element("p","lr-failure-message",issue.message);
        if(issue.phase!=="parse"&&issue.obligation){const details=element("details","lr-failure-details");details.append(element("summary",null,editText("检查说明","Check details")),message);target.append(details);}else target.append(message);
      }
      if(issue.phase!=="parse")target.append(element("p","lr-empty-note",t("notFalse")));
      if(issue.statementStart)target.append(element("small","lr-failure-location",editText("此标记位于所属语句起点；记录未提供更精确的位置。","This marker is at the enclosing statement's start; no more precise location is retained.")));
      const atomic=statement&&failedAtomicVerification(statement.evidence);
      if(atomic?.variant==="FailToSearchProof"&&atomic.fields?.well_defined_proof)appendAtomicWellDefinedness(target,{role:"rejected",source_id:issue.sourceId},atomic,0);
    }
    function selectSourceIssue(id){const issue=sourceIssues.get(id);if(!issue||pending())return false;return navigate({source:issue.sourceId,statement:statements.get(issue.statementId)?.source_id===issue.sourceId?issue.statementId:null,fact:null,symbol:null,wd:null,issue:id,focusLine:issue.line,explanationOpen:true});}
    function openSourceIssue(owner,ids){
      closeExplanation();openSourcePreview(owner,editText("这里为什么没有通过","Why this step was not accepted"),body=>{for(const id of ids)appendSourceIssue(body,sourceIssues.get(id),false);},{factPreview:true,select:ids.length===1?()=>selectSourceIssue(ids[0]):null});
    }
    function attachSourceIssue(token,issue){
      token.classList.add("lr-diagnostic-point");token.dataset.issue=issue.id;token.tabIndex=0;token.setAttribute("aria-label",sourceIssueLabel(issue));
      token.addEventListener("mouseenter",()=>hoverProofTarget(token));token.addEventListener("focus",()=>hoverProofTarget(token));token.addEventListener("pointerleave",leaveProof);
    }
    function equalityProofParts(fact){
      if(fact?.role!=="verified")return null;
      const result=proofResult(fact.evidence);
      if(["ExecByThmStmtSuccess","ExecReleaseThmStmtSuccess"].includes(result.type)){
        const outputs=result.type==="ExecByThmStmtSuccess"?[result.fields?.stored]:array(result.fields?.stored),output=outputs.map(theoremConclusion).find(value=>value?.id===fact.id);let subject=output?.subject;
        if(subject?.type==="AtomicFact")subject=resolveEvidence(subject.fields?.["0"]);
        if(subject?.type==="EqualFact")return {objects:[subject.fields.left,subject.fields.right],operators:["="],adjacent:[fact.evidence],theorem:true};
        return null;
      }
      const subject=resolveEvidence(result.fields?.fact);
      if(subject.fields?.fact_id?.fact_id!==fact.id)return null;
      if(result.type==="VerifyChainFactSuccess"&&subject.type==="ChainFact"){
        const objects=array(subject.fields.objs),operators=array(subject.fields.prop_names).map(resolveEvidence),adjacent=array(result.fields.adjacent);
        if(objects.length!==operators.length+1||adjacent.length!==operators.length||!operators.length)return null;
        return {objects,operators:operators.map(value=>value.name),adjacent};
      }
      if(result.type==="VerifyEqualitySuccess"&&subject.type==="EqualFact")return {objects:[subject.fields.left,subject.fields.right],operators:["="],adjacent:[fact.evidence]};
      return null;
    }
    function equalityStepEvidence(fact,index){
      if(!Number.isInteger(index)||index<0)return null;
      const parts=equalityProofParts(fact),evidence=parts?.adjacent[index];
      if(parts?.theorem&&index===0)return evidence;
      if(parts?.operators[index]!=="="||proofResult(evidence).type!=="VerifyEqualitySuccess")return null;
      const relation=resolveEvidence(proofResult(evidence).fields.fact);
      if(relation.type!=="EqualFact"||resolveEvidence(relation.fields.left)!==resolveEvidence(parts.objects[index])||resolveEvidence(relation.fields.right)!==resolveEvidence(parts.objects[index+1]))return null;
      return evidence;
    }
    function equalityTokenTargets(rowFacts,tokens){
      const targets=new Map();if(rowFacts.length!==1)return targets;
      const fact=rowFacts[0],parts=equalityProofParts(fact),relations=new Set(["=","<","<=",">",">=","!="]);
      if(!parts||parts.operators.some(name=>!relations.has(name)))return targets;
      const stack=[],operators=[],closing={"(":")","[":"]","{":"}"};
      for(const token of tokens){
        if(Object.prototype.hasOwnProperty.call(closing,token.text))stack.push(closing[token.text]);
        else if([")","]","}"].includes(token.text)){if(stack.pop()!==token.text)return targets;}
        else if(!stack.length&&relations.has(token.text))operators.push(token);
      }
      if(stack.length||operators.length!==parts.operators.length||operators.some((token,index)=>token.text!==parts.operators[index]))return targets;
      operators.forEach((token,index)=>{if(token.text==="="&&equalityStepEvidence(fact,index))targets.set(token.start_byte,{factId:fact.id,index});});
      return targets;
    }
    function attachEqualityProof(token,target){
      token.classList.add("lr-chain-equality");token.dataset.chainFact=target.factId;token.dataset.chainStep=String(target.index);token.tabIndex=0;token.setAttribute("role","button");
      token.title=editText("悬浮查看此等式的证明，点击固定说明","Hover for this equality's proof; click to keep it open");
      token.setAttribute("aria-label",editText("第 "+(target.index+1)+" 步的等式依据","Proof of equality at step "+(target.index+1)));
      token.setAttribute("aria-description",token.title);token.addEventListener("mouseenter",()=>hoverProofTarget(token));token.addEventListener("focus",()=>hoverProofTarget(token));
      if(state.fact===target.factId&&state.chainStep===target.index)token.classList.add("lr-equality-selected");
      const select=()=>selectFact(target.factId,target.index);
      token.addEventListener("click",event=>{event.stopPropagation();select();});token.addEventListener("pointerleave",leaveProof);
      token.addEventListener("keydown",event=>{
        if(["Enter"," "].includes(event.key)){event.preventDefault();select();}
        else if((event.key==="ArrowRight"||event.key==="Tab"&&!event.shiftKey)&&proofPopover?.owner===token){event.preventDefault();proofPopover.node.querySelector(".lr-proof-pin,.lr-fact-link,.lr-explanation-close")?.focus();}
      });
    }
    function closeProof(restoreFocus=false){
      clearTimeout(proofTimer);clearTimeout(proofCloseTimer);proofTimer=null;proofCandidate=null;proofHoverToken=null;
      const owner=proofPopover?.owner;
      if(proofPopover){proofPopover.owner.removeAttribute("aria-describedby");proofPopover.symbolOwner?.removeAttribute("aria-describedby");proofPopover.node.remove();proofPopover=null;}
      codePane?.querySelectorAll(".lr-proof-target,.lr-proof-premise,.lr-citation-peek").forEach(row=>row.classList.remove("lr-proof-target","lr-proof-premise","lr-citation-peek"));
      if(restoreFocus)restoreSourceFocus(owner);
    }
    function restoreSourceFocus(owner){
      const target=owner?.matches(".lr-code-row")?(root.querySelector(".lr-ide-input")||owner.querySelector(".lr-line-number")):owner;
      if(target?.isConnected){proofFocusSuppression=target;target.focus({preventScroll:true});Promise.resolve().then(()=>{if(proofFocusSuppression===target)proofFocusSuppression=null;});}
    }
    function leaveProof(){clearTimeout(proofTimer);proofTimer=null;proofCandidate=null;clearTimeout(proofCloseTimer);if(!proofPopover?.persistent)proofCloseTimer=setTimeout(closeProof,300);}
    function keepProofOpen(){clearTimeout(proofTimer);clearTimeout(proofCloseTimer);proofTimer=null;proofCandidate=null;}
    function hoverProofTarget(target){
      if(target===proofFocusSuppression)return false;
      if(proofPopover?.persistent)return false;
      const equality=target?.closest(".lr-chain-equality"),row=target?.closest(".lr-code-row"),token=target?.closest(".lr-token,[data-syntax]"),issueIds=row?.dataset.issues,ids=equality?JSON.stringify([equality.dataset.chainFact]):issueIds||row?.dataset.proofFacts,owner=equality||row;
      // Sentence evidence and symbol documentation are independent: a token
      // change must not replace the proof or restart the sentence dwell timer.
      if(pending()||state.explanationOpen&&!equality&&!issueIds||!ids||target?.closest(".lr-inference-toggle,.lr-reference-count")){
        if(proofPopover||proofCandidate)leaveProof();return false;
      }
      clearTimeout(proofCloseTimer);hideTokenHelp();
      proofHoverToken=tokenHelpRenderers.has(token)?token:null;
      if(proofPopover?.owner===owner){clearTimeout(proofTimer);proofTimer=null;proofCandidate=null;updateProofSymbol(proofHoverToken);return true;}
      if(proofCandidate===owner)return true;
      clearTimeout(proofTimer);proofCandidate=owner;
      proofTimer=setTimeout(()=>{
        proofTimer=null;if(destroyed||!owner.isConnected||proofCandidate!==owner)return;
        const hovered=proofHoverToken;
        if(issueIds)openSourceIssue(owner,JSON.parse(issueIds));else openProof(owner,JSON.parse(ids),equality?Number(equality.dataset.chainStep):null);
        updateProofSymbol(hovered);
      },450);
      return true;
    }
    function updateProofSymbol(token){
      const panel=proofPopover,render=token&&tokenHelpRenderers.get(token);if(!panel||!render||panel.symbolOwner===token||!panel.node.classList.contains("lr-fact-preview"))return;
      const info=panel.node.querySelector(".lr-proof-symbol");if(!info)return;
      panel.symbolOwner?.removeAttribute("aria-describedby");panel.symbolOwner=token;info.id=panel.node.id+"-symbol";token.setAttribute("aria-describedby",info.id);info.replaceChildren();info.hidden=false;panel.node.classList.add("lr-proof-has-symbol");render(info);
    }
    function proofResult(value){
      // Follow result wrappers only. Do not take a nested WD or premise proof
      // as the explanation of the conclusion we are inspecting.
      let node=resolveEvidence(value);const seen=new Set();
      while(node&&typeof node==="object"&&!seen.has(node)){
        seen.add(node);if(node.fields?.searched_proof)return node;
        if(node.type==="VerifyChainFactSuccess")return node;
        if(!node.fields?.["0"])return node;node=resolveEvidence(node.fields["0"]);
      }
      return {kind:"unavailable"};
    }
    function proofRecord(value){const result=proofResult(value);return result.fields?.searched_proof?resolveEvidence(result.fields.searched_proof):result;}
    function proofFrames(value){
      const frames=[],seen=new Set();let node=proofRecord(value);
      while(node&&typeof node==="object"&&!seen.has(node)){seen.add(node);frames.push(node);if(!node.fields?.["0"])break;node=resolveEvidence(node.fields["0"]);}
      return frames;
    }
    function proofSubject(fact){
      const result=proofResult(fact.evidence);let node=resolveEvidence(result.fields?.fact||result.fields?.goal),seen=new Set();
      while(node&&["Fact","AtomicFact"].includes(node.type)&&!seen.has(node)){seen.add(node);node=resolveEvidence(node.fields?.["0"]);}
      return node?.type?node:factSubjects.get(fact.id);
    }
    function appendPredicateDefinition(target,fact){
      const subject=proofSubject(fact),sourceId=factLocation(fact).sourceId;
      if(subject?.type==="NormalAtomicFact"){
        const predicate=resolveEvidence(subject.fields?.predicate),declaration=symbolDefinitions.get(predicate.symbol_id),model=declaration?.mathematics;
        if(model&&["predicate_definition","abstract_predicate"].includes(model.kind)){
          const section=element("section","lr-predicate-definition");section.append(element("h4","lr-proof-section-title",editText("定义","Definition")));
          if(model.kind==="predicate_definition")appendPredicateMeaning(section,model,declaration.source_id);
          else section.append(formula(model.subject,declaration.source_id),element("p","lr-empty-note",t("abstractMeaning")));
          target.append(section);return true;
        }
        if(loader&&declaration&&typeof sources.get(declaration.source_id)?.content!=="string"){
          const section=element("section","lr-predicate-definition"),epoch=generation;section.append(element("p","lr-empty-note",t("loading")));target.append(section);
          loader.loadSource(declaration.source_id).then(chunk=>{if(destroyed||epoch!==generation||!section.isConnected)return;mergeReadingChunk(bundle,chunk);index();section.replaceChildren();if(!appendPredicateDefinition(section,fact))section.append(element("p","lr-empty-note",t("meaningUnavailable")));positionOverlays();}).catch(()=>{if(section.isConnected)section.textContent=t("loadFailed");});return true;
        }
        const section=element("section","lr-predicate-definition");section.append(element("h4","lr-proof-section-title",editText("定义","Definition")),element("p","lr-empty-note",editText("当前阅读记录没有提供此谓词的定义。","The current reading records do not provide this predicate's definition.")));target.append(section);return true;
      }
      if(!["InFact","NotInFact"].includes(subject?.type))return false;
      const section=element("section","lr-predicate-definition"),set=resolveEvidence(subject.fields?.set),operation=set.type==="Obj"&&set.variant==="SetOperator"?resolveEvidence(set.fields?.["0"]):null;
      section.append(element("h4","lr-proof-section-title",editText("定义","Definition")),element("p","lr-proof-summary",editText("x ∈ A 表示 x 是集合 A 的元素。","x ∈ A means that x is an element of the set A.")));
      const definitions={Intersect:"x ∈ A ∩ B ⇔ (x ∈ A ∧ x ∈ B)",Union:"x ∈ A ∪ B ⇔ (x ∈ A ∨ x ∈ B)",SetMinus:"x ∈ A ∖ B ⇔ (x ∈ A ∧ x ∉ B)"};
      if(definitions[operation?.variant])section.append(formula(definitions[operation.variant],sourceId));
      if(subject.type==="NotInFact")section.append(element("p","lr-proof-summary",editText("x ∉ A 是 x ∈ A 的否定。","x ∉ A is the negation of x ∈ A.")));
      target.append(section);return true;
    }
    function appendProofRequirement(target,fact,requirement,evidence,depth){
      const text=resolveEvidence(requirement).text||proofRelation(evidence);if(!text){target.append(element("p","lr-empty-note",editText("此条件及其证明记录未完整导出。","This condition and its proof record were not fully exported.")));return;}
      const step=element("details","lr-proof-step"),summary=element("summary");summary.append(formula(text,factLocation(fact).sourceId));step.append(summary);let rendered=false;
      step.addEventListener("toggle",()=>{if(step.open&&!rendered){rendered=true;const expected=retainedFactId(requirement),actual=retainedFactId(proofResult(evidence).fields?.fact);if(!expected||expected!==actual)step.append(element("p","lr-empty-note",editText("没有可与此条件准确对应的证明记录。","No proof record can be matched exactly to this condition.")));else appendProofBody(step,{...fact,id:null,role:"verified",evidence},evidence,false,depth+1);positionOverlays();}});target.append(step);
    }
    function retainedFactId(value){let node=resolveEvidence(value),seen=new Set();while(node&&["Fact","AtomicFact"].includes(node.type)&&!seen.has(node)){seen.add(node);node=resolveEvidence(node.fields?.["0"]);}return node?.fields?.fact_id?.fact_id||null;}
    function forallApplication(record){
      if(record.variant!=="ByKnownForallFact")return null;
      let application=resolveEvidence(record.fields?.["0"]);
      // Current result detail wraps the retained instantiation. Legacy bundles
      // stored these fields directly; Normal/Compact intentionally omit args.
      if(application.type==="SearchProofByKnownForallFact"&&["Detailed","Normal"].includes(application.variant))application=resolveEvidence(application.fields?.["0"]);
      const cite=resolveEvidence(application.fields?.cite),id=cite.fields?.fact_id;
      // A typed citation still identifies its source when a lazy/older export
      // omits that source's AST. A known non-forall shape must never be relabeled.
      const sourceFact=id?.kind==="fact_reference"&&facts.has(id.fact_id)&&(quantifiedFacts.has(id.fact_id)||cite.type==="ForallConclusionCite"&&!factSubjects.has(id.fact_id))?id.fact_id:null,known=quantifiedFacts.get(sourceFact),groups=resolveEvidence(known?.fields?.typed_parameters),params=array(groups.fields?.groups).flatMap(value=>array(resolveEvidence(value).fields?.params)),args=array(application.fields?.forall_parameters_match_what_args).map(resolveEvidence);
      const complete=!!sourceFact&&Array.isArray(groups.fields?.groups)&&Array.isArray(application.fields?.forall_parameters_match_what_args)&&params.length===args.length&&params.every(param=>param.kind==="symbol_reference")&&args.every(arg=>typeof arg.text==="string");
      return {application,sourceFact,complete,substitutions:complete?params.map((param,index)=>({parameter:param.name,argument:args[index].text})):[]};
    }
    function appendProofResult(target,fact,evidence){
      const conclusion=proofRelation(evidence);if(!conclusion)return;
      const result=element("div","lr-proof-rule-result");result.append(element("span","lr-proof-section-title",editText("由此得到","Therefore")),formula(conclusion,factLocation(fact).sourceId));target.append(result);
    }
    function instantiationDetail(application){
      let requirements=resolveEvidence(application.fields?.instantiation_requirements);
      if(requirements.type==="ProveForallInstantiationRequirementsProof"&&requirements.variant==="Detailed")requirements=resolveEvidence(requirements.fields?.["0"]);
      return requirements;
    }
    function strategySubstitutions(application){
      const bound=new Map(),seen=new Set();
      function visit(value){let node=resolveEvidence(value);if(node.type==="ForallConclusionArgMatchProof"&&node.variant==="Detailed")node=resolveEvidence(node.fields?.["0"]);if(seen.has(node)||node.type!=="DetailedForallConclusionArgMatchProof")return;seen.add(node);
        const fields=node.fields;if(node.variant==="BoundParam"&&fields?.param_id?.kind==="identifier_id"){const pattern=resolveEvidence(fields.pattern),argument=resolveEvidence(fields.goal_arg);if(typeof pattern.text==="string"&&typeof argument.text==="string")bound.set(fields.param_id.id,{parameter:pattern.text,argument:argument.text,node:argument});}
        else if(node.variant==="ByStructure")array(fields?.child_matches).forEach(visit);
      }
      array(application.fields?.arg_match_proofs).forEach(visit);
      const parameters=instantiationDetail(application).fields?.param_type_requirements,args=application.fields?.forall_parameters_match_what_args;
      if(!Array.isArray(parameters)||!Array.isArray(args)||parameters.length!==args.length)return null;
      const pairs=[];for(let index=0;index<parameters.length;index++){const parameter=resolveEvidence(parameters[index]),pair=bound.get(parameter.fields?.param_id?.id);if(!pair||pair.node!==resolveEvidence(args[index]))return null;pairs.push(pair);}return pairs;
    }
    function appendSubstitutions(target,fact,pairs){
      const summary=element("p","lr-proof-summary lr-proof-substitutions");if(pairs.length)summary.append(document.createTextNode(editText("取 ","Take ")));pairs.forEach((pair,index)=>{if(index)summary.append(document.createTextNode(editText("，",", ")));summary.append(element("code","lr-proof-substitution",displayText(pair.parameter,factLocation(fact).sourceId)+" = "+mathText(pair.argument,factLocation(fact).sourceId)));});if(!pairs.length)summary.append(document.createTextNode(editText("此应用不需要代入参数。","No parameter substitution is required.")));target.append(summary);
    }
    function recordedParameters(value){
      const groups=resolveEvidence(value).fields?.groups;if(!Array.isArray(groups))return null;
      const parameters=[];for(const group of groups){const params=resolveEvidence(group).fields?.params;if(!Array.isArray(params))return null;for(const param of params){const symbol=resolveEvidence(param);if(symbol.kind!=="symbol_reference")return null;parameters.push(symbol);}}return parameters;
    }
    function appendDefinitionBindings(target,fact,parameters,args){
      if(!parameters||!Array.isArray(args)||parameters.length!==args.length||args.some(arg=>typeof resolveEvidence(arg).text!=="string")){
        target.append(element("p","lr-empty-note",editText("形参与实参的对应记录不完整。","The parameter-to-argument correspondence is incomplete.")));return false;
      }
      appendSubstitutions(target,fact,parameters.map((param,index)=>({parameter:param.name,argument:resolveEvidence(args[index]).text})));return true;
    }
    function theoremConclusion(value){
      const result=resolveEvidence(value);if(result.type!=="StoreFactAndInferResult")return null;
      const store=proofResult(result.fields?.store),id=resolveEvidence(store.fields?.fact_id||store.fields?.whole_fact_id),subject=resolveEvidence(store.fields?.fact);
      const text=typeof subject.text==="string"?subject.text:facts.get(id.fact_id)?.text;
      return id.kind==="fact_reference"&&typeof text==="string"?{id:id.fact_id,subject:{...subject,text}}:null;
    }
    function appendTheoremApplication(target,fact,evidence,record,depth){
      if(!["ExecByThmStmtSuccess","ExecReleaseThmStmtSuccess"].includes(record.type))return false;
      const fields=record.fields||{},selected=record.type==="ExecByThmStmtSuccess",outputs=selected?[fields.stored]:array(fields.stored),output=outputs.map(theoremConclusion).find(value=>value?.id===fact.id);
      const part=element("section","lr-proof-application lr-theorem-application");part.dataset.route="theorem";target.append(part);
      if(!output){part.append(element("p","lr-empty-note",editText("此事实与定理输出的对应记录不完整。","The correspondence between this fact and the theorem output is incomplete.")));return true;}
      const call=resolveEvidence(fields.call),name=resolveEvidence(call.fields?.name),callee=resolveEvidence(fields.callee),source=element("div","lr-proof-grounds lr-theorem-source");
      source.append(element("h4","lr-proof-section-title",callee.variant==="Builtin"?editText("使用内置定理","Builtin theorem applied"):callee.variant==="UserAxiom"?editText("使用公理","Axiom applied"):editText("使用定理","Theorem applied")));part.append(source);
      if(name.kind==="symbol_reference")source.append(element("code","lr-proof-rule-name",name.name));else source.append(element("p","lr-empty-note",editText("定理名称未完整导出。","The theorem name was not fully exported.")));
      if(callee.variant==="Builtin"){const application=resolveEvidence(fields.builtin),theorem=resolveEvidence(application.fields?.theorem),message=theorem.rule_id&&ruleMessage(theorem.rule_id),reference=name.kind==="symbol_reference"&&theoremReference(name.symbol_id);if(message||reference?.summary)source.append(element("p","lr-proof-rule-message",message||reference.summary));}
      const declaration=resolveEvidence(callee.fields?.["0"]),declaredName=resolveEvidence(declaration.fields?.name),sameCallee=name.kind==="symbol_reference"&&declaredName.kind==="symbol_reference"&&name.symbol_id===declaredName.symbol_id;
      const statementId=sameCallee&&declaration.declaration?.statement_id;
      if(statementId&&statements.has(statementId))source.append(button(editText("查看定理","View theorem"),"lr-definition-link",()=>selectStatement(statementId)));
      const argumentsRecord=resolveEvidence(call.fields?.arguments),args=argumentsRecord.type==="TheoremCallArguments"&&argumentsRecord.variant==="Parenthesized"?argumentsRecord.fields?.["0"]:null;
      if(sameCallee&&["UserTheorem","UserAxiom"].includes(callee.variant)&&Array.isArray(args)){
        const universal=proofResult(declaration.fields?.fact);appendDefinitionBindings(part,fact,universal.type==="ForallFact"?recordedParameters(universal.fields?.typed_parameters):null,args);
      }else if(callee.variant==="Builtin"&&Array.isArray(args)&&args.every(value=>typeof resolveEvidence(value).text==="string")){
        // Builtin contracts retain actual arguments, not named formal binders.
        // Show the call rather than inventing a parameter correspondence.
        if(name.kind==="symbol_reference")part.append(formula(name.name+"("+args.map(value=>resolveEvidence(value).text).join(", ")+")",factLocation(fact).sourceId));
      }else if(argumentsRecord.type==="TheoremCallArguments"&&argumentsRecord.variant==="Bare")part.append(element("p","lr-proof-summary",editText("直接应用此定理；本句未给出显式实参。","Apply this theorem directly; this statement supplies no explicit arguments.")));
      else part.append(element("p","lr-empty-note",editText("形参与实参的对应记录不完整。","The parameter-to-argument correspondence is incomplete.")));
      const premises=element("div","lr-proof-requirements");premises.append(element("h4","lr-proof-section-title",editText("验证的前提","Verified premises")));part.append(premises);
      if(!Array.isArray(fields.dom_proofs))premises.append(element("p","lr-empty-note",editText("实例化前提的证明记录未完整导出。","The instantiated premise proofs were not fully exported.")));
      else if(!fields.dom_proofs.length)premises.append(element("p","lr-proof-summary",editText("此定理应用没有额外的命题前提。","This theorem application has no additional propositional premises.")));
      else for(const proof of fields.dom_proofs)appendProofRequirement(premises,fact,proofResult(proof).fields?.fact,proof,depth);
      const conclusions=element("div","lr-theorem-conclusions");conclusions.append(element("h4","lr-proof-section-title",selected?editText("选取本句结论","Selected conclusion"):editText("本次引入的结论","Conclusions introduced")));
      if(selected)conclusions.append(formula(output.subject.text,factLocation(fact).sourceId));
      else for(const value of outputs){const conclusion=theoremConclusion(value);if(conclusion)conclusions.append(conclusion.id===fact.id?factFormula(fact):factButton(conclusion.id));else conclusions.append(element("p","lr-empty-note",editText("一项结论的记录未完整导出。","One conclusion record was not fully exported.")));}
      part.append(conclusions);
      if(selected){const proof=element("details","lr-theorem-selection");proof.append(element("summary",null,editText("与定理返回结论的对应","Correspondence with the returned conclusion")));let shown=false;proof.addEventListener("toggle",()=>{if(proof.open&&!shown){shown=true;appendProofBody(proof,{...fact,id:null,evidence:fields.selected_proof},fields.selected_proof,false,depth+1);positionOverlays();}});part.append(proof);}
      return true;
    }
    function anonymousFunction(value){
      let node=resolveEvidence(value);
      if(node.type==="Obj"&&node.variant==="FunctionSpace")node=resolveEvidence(node.fields?.["0"]);
      if(node.type==="FunctionSpace"&&node.variant==="AnonymousFn")node=resolveEvidence(node.fields?.["0"]);
      return node.type==="AnonymousFn"?node:null;
    }
    function recordedFunctionApplication(value){
      let node=resolveEvidence(value);if(node.type==="Obj"&&node.variant==="FnObj")node=resolveEvidence(node.fields?.["0"]);
      return node.type==="FnObj"?node:null;
    }
    function appendDefinitionSource(target,fact,path){
      const proof=resolveEvidence(path),edges=proof.type==="KnownEqualityPathProof"?proof.fields?.path:null;
      if(!Array.isArray(edges))return null;
      const source=element("div","lr-proof-definition-source"),cited=new Set();
      for(const edge of edges){const id=resolveEvidence(edge?.[2]).fact_id;if(facts.has(id)&&!cited.has(id)){cited.add(id);source.append(factButton(id));}}
      if(cited.size)target.append(source);
      return edges.length?resolveEvidence(edges.at(-1)?.[1]):null;
    }
    function appendBodyExpansion(target,fact,value){
      const wrapper=resolveEvidence(value),step=resolveEvidence(wrapper.fields?.["0"]),application=resolveEvidence(step.fields?.application),body=resolveEvidence(step.fields?.expanded_body),part=element("div","lr-definition-expansion");target.append(part);
      if(wrapper.type!=="FunctionBodyExpansionProof"||!application.text||!body.text){part.append(element("p","lr-empty-note",editText("此步定义展开记录不完整。","This definition-expansion record is incomplete.")));return;}
      if(wrapper.variant==="Anonymous"){
        const source=resolveEvidence(step.fields.function_body),path=source.variant==="KnownEquality"?source.fields?.["0"]:source.fields?.function_equal,endpoint=appendDefinitionSource(part,fact,path),call=recordedFunctionApplication(step.fields.application),head=resolveEvidence(call?.fields?.head);
        const fn=source.variant==="Template"?anonymousFunction(source.fields?.instantiated_function):anonymousFunction(endpoint)||anonymousFunction(head.type==="FnObjHead"&&head.variant==="AnonymousFnLiteral"?head.fields?.["0"]:null),signature=resolveEvidence(fn?.fields?.body);
        // The function value is the retained equality endpoint (or literal),
        // not a same-named declaration found elsewhere in the source.
        if(fn)appendDefinitionBindings(part,fact,recordedParameters(signature.fields?.set_bound_parameters),call?.fields?.body?.[0]);
        else part.append(element("p","lr-empty-note",editText("此记录未提供被代入的函数体及其形参。","The applied function body and its parameters were not exported here.")));
      }else if(wrapper.variant==="Composition"){
        appendDefinitionSource(part,fact,step.fields.function_equal);part.append(element("p","lr-proof-summary",editText("按复合函数的定义，先应用内层函数，再应用外层函数。","By the definition of composition, apply the inner function and then the outer function.")));
      }else if(wrapper.variant==="FiniteCoordinate")part.append(element("p","lr-proof-summary",editText("取有限函数中指定坐标的值。","Select the specified coordinate of the finite function.")));
      else{part.append(element("p","lr-empty-note",editText("此种定义展开尚无专门解说。","This definition-expansion form has no dedicated explanation yet.")));return;}
      part.append(formula(application.text+" = "+body.text,factLocation(fact).sourceId));
    }
    function appendObjectDefinitionApplication(target,fact,evidence,depth){
      const frames=proofFrames(evidence);if(!frames.some(node=>node.variant==="ByObjectDefinition"))return false;
      const detail=frames.find(node=>["ByUnfoldNamedHaveFnEqualApplicationObjectDefinitionProof","ByBothFunctionBodiesObjectDefinitionProof","ByHaveObjEqualObjectDefinitionProof","ByLetObjObjectDefinitionProof","ByUnfoldHaveFnEqualCaseByCaseApplicationObjectDefinitionProof","ByUnfoldHaveFnByInducApplicationObjectDefinitionProof"].includes(node.type));if(!detail)return false;
      const part=element("section","lr-definition-application"),fields=detail.fields;part.append(element("h4","lr-proof-section-title",editText("按定义展开","Unfold the definition")));target.append(part);
      const normalizations=[fields.normalization,fields.left_normalization,fields.right_normalization].filter(Boolean);
      for(const value of normalizations){const normalization=resolveEvidence(value);if(!Array.isArray(normalization.fields?.expansions)||!normalization.fields.expansions.length)part.append(element("p","lr-empty-note",editText("定义展开步骤未完整导出。","The definition-expansion steps were not fully exported.")));else normalization.fields.expansions.forEach(step=>appendBodyExpansion(part,fact,step));}
      if(!normalizations.length){
        const body=resolveEvidence(fields.expanded_rhs||fields.expanded_body);if(body.text)part.append(formula(body.text,factLocation(fact).sourceId));
        if(fields.guard){part.append(element("p","lr-proof-summary",editText("所选分支的条件：","Condition of the selected branch:")));appendProofRequirement(part,fact,proofResult(fields.guard).fields?.fact,fields.guard,depth);}
        for(const selection of array(fields.selected_case_path)){const guard=resolveEvidence(selection).fields?.guard;appendProofRequirement(part,fact,proofResult(guard).fields?.fact,guard,depth);}
      }
      const residual=fields.residual_equal,record=proofRecord(residual);
      if(proofRelation(residual)&&record.variant==="ByTheyAreTheSame")part.append(element("p","lr-proof-summary",editText("代入后，两边是同一表达式，等式成立。","After substitution, both sides are the same expression, establishing the equality.")));
      else if(proofRelation(residual)){
        part.append(element("p","lr-proof-summary",editText("展开后还需验证：","It remains to verify:")));appendProofRequirement(part,fact,proofResult(residual).fields?.fact,residual,depth);
      }else part.append(element("p","lr-empty-note",editText("展开后的等式证明未完整导出。","The proof of the equality after expansion was not fully exported.")));
      return true;
    }
    function appendPredicateApplication(target,fact,evidence){
      if(!proofFrames(evidence).some(node=>node.type==="AtomicExceptEqualityFactSearchProofByDefinition"&&node.variant==="UserDefinedProp"))return;
      const subject=proofSubject({...fact,evidence}),predicate=resolveEvidence(subject?.fields?.predicate),declaration=symbolDefinitions.get(predicate.symbol_id),part=element("section","lr-predicate-application");target.append(part);
      if(declaration)part.append(button(editText("使用 ","Use ")+predicate.name+editText(" 的定义","'s definition"),"lr-text-link lr-definition-link",()=>selectStatement(declaration.id,declaration.line)));
      let definition=null;if(declaration)walkEvidence(declaration.evidence,node=>{if(node.type==="DefPropStmt"&&resolveEvidence(node.fields?.name).symbol_id===predicate.symbol_id)definition=node;});
      appendDefinitionBindings(part,fact,definition&&recordedParameters(definition.fields.typed_parameters),subject?.fields?.body);
    }
    function appendSpecialPropertyApplication(target,fact,evidence,depth){
      const frames=proofFrames(evidence);if(!frames.some(node=>node.variant==="ByKnownSpecialProperty"))return false;
      const tuple=frames.find(node=>["TupleProjectionKnownProof","FnTupleProjectionKnownProof","TupleReconstructionKnownProof"].includes(node.type)),codomain=frames.find(node=>node.type==="FnApplicationInCodomainKnownSpecialPropertyProof");if(!tuple&&!codomain)return false;
      const part=element("section","lr-special-application");target.append(part);
      if(tuple){
        const fields=tuple.fields,goal=resolveEvidence(proofResult(evidence).fields?.fact),subject=resolveEvidence(fields.reversed?goal.fields?.right:goal.fields?.left),call=recordedFunctionApplication(subject),functionValue=resolveEvidence(fields.function),value=resolveEvidence(resolveEvidence(fields.tuple||fields.function).fields?.value),components=value.fields?.args;
        part.append(element("h4","lr-proof-section-title",editText("使用已知的元组性质","Use the known tuple structure")));appendProofReferences(part,fact,evidence);
        if(tuple.type==="TupleReconstructionKnownProof"){
          part.append(element("p","lr-proof-summary",editText("已知此对象为元组；依次取出它的各个分量，即得原元组。","The object is a tuple; collecting its coordinates in order reconstructs the original tuple.")));return true;
        }
        if(fields.function){
          const endpoint=appendDefinitionSource(part,fact,functionValue.fields?.function_equal),fn=anonymousFunction(endpoint),signature=resolveEvidence(fn?.fields?.body);
          if(fn)appendDefinitionBindings(part,fact,recordedParameters(signature.fields?.set_bound_parameters),call?.fields?.body?.[0]);
        }
        const index=Number(fields.index),component=Array.isArray(components)&&Number.isInteger(index)&&index>=1?resolveEvidence(components[index-1]):null;
        if(component?.text){part.append(element("p","lr-proof-summary",editText("取第 "+index+" 个分量：","Select coordinate "+index+":")),formula(component.text,factLocation(fact).sourceId));
          const certificate=fields.component_equal,other=resolveEvidence(fields.reversed?goal.fields?.left:goal.fields?.right);
          if(certificate&&proofRecord(certificate).variant!=="ByTheyAreTheSame"&&other.text){const step=element("details","lr-proof-step");step.append(element("summary",null,editText("验证分量相等","Verify coordinate equality")),formula(component.text+" = "+other.text,factLocation(fact).sourceId));let shown=false;step.addEventListener("toggle",()=>{if(step.open&&!shown){shown=true;appendProofMain(step,{...fact,id:null},certificate,false,depth+1);positionOverlays();}});part.append(step);}
        }
        else part.append(element("p","lr-empty-note",editText("元组的具体分量未完整导出。","The tuple's individual coordinates were not fully exported.")));
      }else{
        part.append(element("h4","lr-proof-section-title",editText("使用函数的陪域声明","Use the declared function codomain")));
        const id=resolveEvidence(codomain.fields.cite_property_fact_id).fact_id;
        if(facts.has(id))part.append(factButton(id));
        const membership=factSubjects.get(id),set=resolveEvidence(membership?.fields?.set),space=set.type==="Obj"&&set.variant==="FunctionSpace"?resolveEvidence(set.fields?.["0"]):null,signature=space?.type==="FunctionSpace"&&space.variant==="FnSet"?resolveEvidence(space.fields?.["0"]):null,goal=proofSubject({...fact,evidence}),call=recordedFunctionApplication(goal?.fields?.element);
        if(signature)appendDefinitionBindings(part,fact,recordedParameters(signature.fields?.set_bound_parameters),call?.fields?.body?.[0]);
        part.append(element("p","lr-proof-summary",editText("实参满足函数的定义域条件，因此函数值属于声明的返回集合。","The arguments satisfy the function's domain conditions, so the value belongs to its declared return set.")));
        appendProofReferences(part,fact,evidence);appendProofResult(part,fact,evidence);
      }
      return true;
    }
    function appendEqualityTransport(target,fact,evidence,depth){
      const frames=proofFrames(evidence);if(!frames.some(node=>node.variant==="ByEquivalenceClass"))return false;
      const route=frames.find(node=>node.type==="EqualFactSearchedProofByEquivalenceClass"),detail=resolveEvidence(route?.fields?.["0"]);if(!["KnownPath","ViaPeers","AlphaEndpoints"].includes(route?.variant))return false;
      const part=element("section","lr-equality-transport");part.append(element("h4","lr-proof-section-title",editText("利用已知等式","Use established equalities")));target.append(part);
      if(route.variant==="AlphaEndpoints"){
        const cited=resolveEvidence(detail.fields?.cited),id=cited.type==="EqualFact"&&cited.fields?.fact_id?.fact_id;
        if(detail.type!=="KnownEqualityAlphaEndpointsProof"||!facts.has(id)||!detail.fields?.left_identity||!detail.fields?.right_identity){part.append(element("p","lr-empty-note",editText("已知等式及其两端对应的记录未完整导出。","The known equality and endpoint correspondence were not fully exported.")));return true;}
        part.append(factButton(id),element("p","lr-proof-summary",detail.fields.reversed?editText("反向使用此等式；两端按绑定变量的对应关系与当前目标相同。","Use this equality in reverse; its endpoints match the goal up to bound-variable correspondence."):editText("此等式的两端按绑定变量的对应关系与当前目标相同。","This equality's endpoints match the goal up to bound-variable correspondence.")));return true;
      }
      function path(value){const node=resolveEvidence(value);if(node.type!=="KnownEqualityPathProof"||!Array.isArray(node.fields?.path)){part.append(element("p","lr-empty-note",editText("等式引用链未完整导出。","The cited equality path was not fully exported.")));return;}for(const edge of node.fields.path){const left=resolveEvidence(edge?.[0]),right=resolveEvidence(edge?.[1]),id=resolveEvidence(edge?.[2]).fact_id;if(left.text&&right.text)part.append(formula(left.text+" = "+right.text,factLocation(fact).sourceId));if(facts.has(id))part.append(factButton(id));}}
      if(route.variant==="KnownPath")path(detail);
      else{
        path(detail.fields?.left_path);const bridge=detail.fields?.bridge;
        if(proofRelation(bridge)){part.append(element("p","lr-proof-summary",editText("中间还需验证：","Verify the connecting equality:")));appendProofRequirement(part,fact,proofResult(bridge).fields?.fact,bridge,depth);}
        else part.append(element("p","lr-empty-note",editText("中间等式的证明未完整导出。","The connecting equality proof was not fully exported.")));
        path(detail.fields?.right_path);
      }
      return true;
    }
    function appendInstantiationRequirements(target,fact,application,depth){
      const requirements=instantiationDetail(application);
      const fields=requirements.fields,group=element("div","lr-instantiated-premises");group.append(element("h4","lr-proof-section-title",editText("实例化后的前提","Instantiated premises")));target.append(group);
      if(!Array.isArray(fields?.dom_facts)||!Array.isArray(fields?.proof_of_dom_facts))group.append(element("p","lr-empty-note",editText("本次实例化的前提记录未完整导出。","The premise records for this application are incomplete.")));
      else if(fields.dom_facts.length!==fields.proof_of_dom_facts.length){fields.dom_facts.forEach(value=>{const text=resolveEvidence(value).text;if(text)group.append(formula(text,factLocation(fact).sourceId));});group.append(element("p","lr-empty-note",editText("前提与证明记录不完整，无法逐项对应。","The premise and proof records are incomplete and cannot be paired.")));}
      else if(!fields.dom_facts.length)group.append(element("p","lr-empty-note",editText("此应用没有额外前提。","This application has no additional premises.")));
      else fields.dom_facts.forEach((value,index)=>appendProofRequirement(group,fact,value,fields.proof_of_dom_facts[index],depth));
      if(Array.isArray(fields?.param_type_requirements)&&fields.param_type_requirements.length){
        const domains=element("details","lr-proof-formation");domains.append(element("summary",null,editText("参数的范围","Parameter domains")));
        for(const value of fields.param_type_requirements){const entry=resolveEvidence(value);if(entry.type==="ForallParamTypeRequirementProof")appendProofRequirement(domains,fact,entry.fields?.type_fact,entry.fields?.proof,depth);}
        target.append(domains);
      }
    }
    function appendRecordedMatch(target,value,fact,depth){
      let match=resolveEvidence(value);if(match.type==="ForallConclusionArgMatchProof"&&match.variant==="Detailed")match=resolveEvidence(match.fields?.["0"]);
      const fields=match.fields,left=resolveEvidence(fields?.pattern||fields?.previous),right=resolveEvidence(fields?.goal_arg);
      if(match.type!=="DetailedForallConclusionArgMatchProof"||!left.text||!right.text){target.append(element("p","lr-empty-note",editText("此参数的对应记录未完整导出。","The correspondence record for this argument is incomplete.")));return;}
      const item=element("details","lr-proof-match"),summary=element("summary");summary.append(formula(left.text+" ↦ "+right.text,factLocation(fact).sourceId));item.append(summary);target.append(item);let shown=false;
      item.addEventListener("toggle",()=>{
        if(!item.open||shown)return;shown=true;const body=element("div","lr-proof-match-evidence");item.append(body);
        if(match.variant==="BoundParam")body.append(element("p","lr-empty-note",editText("将该形参绑定到当前对象。","Bind this parameter to the current object.")));
        else if(match.variant==="ByStructure")array(fields.child_matches).forEach(child=>appendRecordedMatch(body,child,fact,depth+1));
        else if(["ReboundParamEqual","NonParamEqual"].includes(match.variant)){
          body.append(element("p","lr-empty-note",match.variant==="ReboundParamEqual"?editText("同一变量再次出现，检查对象与先前绑定的对象相等。","The parameter occurs again; check equality with its earlier binding."):editText("代入已绑定的变量，再与目标参数作严格相等检查。","Substitute the bound parameters, then check strict equality with the goal argument.")));
          const certificate=resolveEvidence(fields.equal),relation=resolveEvidence(certificate.fields?.equal_fact),a=resolveEvidence(relation.fields?.left),b=resolveEvidence(relation.fields?.right);
          if(certificate.type==="StrictEqualWithFact"&&a.text&&b.text){body.append(formula(a.text+" = "+b.text,factLocation(fact).sourceId));appendProofReferences(body,{...fact,id:null},fields.equal);}else body.append(element("p","lr-empty-note",t("unavailable")));
        }else body.append(element("p","lr-empty-note",t("unavailable")));
        positionOverlays();
      });
    }
    function appendArgumentMatches(target,fact,application,depth){
      const group=element("details","lr-proof-matches");group.append(element("summary",null,editText("结论参数如何对应","Conclusion argument correspondence")));
      const matches=application.fields?.arg_match_proofs;
      if(!Array.isArray(matches))group.append(element("p","lr-empty-note",editText("结论参数的对应记录未完整导出。","The conclusion argument records are incomplete.")));
      else matches.forEach(value=>appendRecordedMatch(group,value,fact,depth));target.append(group);
    }
    function appendUniversalApplication(target,fact,evidence,record,depth){
      const universal=forallApplication(record),named=record.variant==="ByKnownStrategy";if(!universal&&!named)return false;
      let application=universal?.application||resolveEvidence(record.fields?.["0"]);
      if(named&&application.type==="SearchProofByKnownStrategy"&&["Detailed","Normal"].includes(application.variant))application=resolveEvidence(application.fields?.["0"]);
      const part=element("section","lr-proof-application "+(named?"lr-strategy-application":"lr-forall-application"));part.dataset.route=named?"strategy":"forall";target.append(part);
      const source=element("div","lr-proof-grounds lr-forall-source");source.append(element("h4","lr-proof-section-title",named?editText("使用的策略","Strategy applied"):editText("使用的全称命题","Universal statement applied")));
      if(named){const name=application.fields?.strategy_name;if(typeof name==="string")source.append(element("code","lr-proof-rule-name",name));else source.append(element("p","lr-empty-note",editText("策略名称未完整导出。","The strategy name is incomplete.")));}
      else if(universal.sourceFact)source.append(factButton(universal.sourceFact));else source.append(element("p","lr-empty-note",editText("当前记录没有可准确定位的全称命题。","The universal statement cannot be identified exactly in these records.")));
      part.append(source);
      if(universal){
        if(universal.complete)appendSubstitutions(part,fact,universal.substitutions);
        else part.append(element("p","lr-empty-note",editText("形参或实参记录不完整，无法逐项展示代入。","The parameter or argument records are incomplete; substitutions cannot be paired.")));
      }else{const pairs=strategySubstitutions(application);if(pairs)appendSubstitutions(part,fact,pairs);else part.append(element("p","lr-empty-note",editText("策略形参与实参的完整对应未随此记录导出。","The full strategy parameter correspondence was not exported in these records.")));}
      appendArgumentMatches(part,fact,application,depth);appendInstantiationRequirements(part,fact,application,depth);
      appendProofReferences(part,fact,evidence,new Set(universal?.sourceFact?[universal.sourceFact]:[]));appendProofResult(part,fact,evidence);return true;
    }
    function atomicArguments(subject){
      const fields=subject?.fields;if(!fields)return null;
      if(["NormalAtomicFact","NotNormalAtomicFact"].includes(subject.type))return Array.isArray(fields.body)?fields.body:null;
      if(["InFact","NotInFact"].includes(subject.type))return [fields.element,fields.set];
      if(["EqualFact","NotEqualFact","LessFact","NotLessFact","GreaterFact","NotGreaterFact","LessEqualFact","NotLessEqualFact","GreaterEqualFact","NotGreaterEqualFact","DvdFact","NotDvdFact","SubsetFact","NotSubsetFact","SupersetFact","NotSupersetFact","ProperSubsetFact","NotProperSubsetFact","ProperSupersetFact","NotProperSupersetFact"].includes(subject.type))return [fields.left,fields.right];
      if(["IsSetFact","NotIsSetFact","IsNonemptySetFact","NotIsNonemptySetFact","IsFiniteSetFact","NotIsFiniteSetFact"].includes(subject.type))return [fields.set];
      return null;
    }
    function appendKnownApplication(target,fact,evidence,record,depth){
      let application=record.variant==="ByKnownAtomicFact"?resolveEvidence(record.fields?.["0"]):null;
      if(record.variant==="ByStructuralMembership"){const membership=resolveEvidence(record.fields?.["0"]),reason=resolveEvidence(membership.fields?.reason);if(membership.type==="StructuralMembershipProof"&&reason.type==="StructuralMembershipReason"&&reason.variant==="Known")application=resolveEvidence(reason.fields?.["0"]);}
      if(application?.type!=="AtomicExceptEqualityFactSearchProofByKnownAtomicFact")return false;
      const cite=application.fields?.cite_fact_id,id=cite?.kind==="fact_reference"?cite.fact_id:null,sourceFact=facts.get(id),part=element("section","lr-proof-application lr-known-application");part.dataset.route="known";target.append(part);
      const source=element("div","lr-proof-grounds lr-known-source");source.append(element("h4","lr-proof-section-title",editText("引用已知事实","Known fact reused")));if(sourceFact)source.append(factButton(id));else source.append(element("p","lr-empty-note",editText("被引用事实的记录未完整导出。","The cited fact record is incomplete.")));part.append(source);
      const knownSubject=sourceFact&&proofSubject(sourceFact),goalSubject=proofSubject({...fact,evidence}),knownArgs=atomicArguments(knownSubject),goalArgs=atomicArguments(goalSubject),proofs=application.fields?.why_parameters_of_known_fact_are_equal_to_givens,group=element("details","lr-proof-matches");group.append(element("summary",null,editText("已知参数与当前参数","Known and current arguments")));part.append(group);
      if(knownSubject?.type&&!knownArgs||goalSubject?.type&&!goalArgs)group.append(element("p","lr-empty-note",editText("此类事实的逐项参数排版尚未提供；仍可查看所引用的事实与结论。","Argument-by-argument layout is not available for this fact form; its cited fact and conclusion remain accessible.")));
      else if(!knownArgs||!goalArgs||!Array.isArray(proofs)||knownArgs.length!==goalArgs.length||goalArgs.length!==proofs.length||knownArgs.concat(goalArgs).some(value=>typeof resolveEvidence(value).text!=="string"))group.append(element("p","lr-empty-note",editText("参数或相等证明记录不完整，无法逐项对应。","The argument or equality proof records are incomplete and cannot be paired.")));
      else{group.open=knownArgs.some((value,index)=>resolveEvidence(value).text!==resolveEvidence(goalArgs[index]).text||proofRecord(proofs[index]).variant!=="ByTheyAreTheSame");knownArgs.forEach((value,index)=>{const left=resolveEvidence(value),right=resolveEvidence(goalArgs[index]),item=element("details","lr-proof-match"),summary=element("summary");summary.append(formula(left.text+" = "+right.text,factLocation(fact).sourceId));item.append(summary);group.append(item);let shown=false;item.addEventListener("toggle",()=>{if(item.open&&!shown){shown=true;const body=element("div","lr-proof-match-evidence");item.append(body);appendProofBody(body,{...fact,id:null,role:"verified",evidence:proofs[index]},proofs[index],false,depth+1);positionOverlays();}});});}
      appendProofReferences(part,fact,evidence,new Set(id?[id]:[]));appendProofResult(part,fact,evidence);return true;
    }
    function appendProofContext(target,fact){
      if(!fact.scope_id||String(fact.scope_id).startsWith("file:"))return;
      const context=element("div","lr-proof-context"),scope=scopes.get(fact.scope_id),owner=statements.get(scope?.statement_id);
      if(fact.role!=="hypothesis")context.append(element("span",null,editText("在本段假设下成立","Established under this proof's assumptions")));
      // The scope record identifies its owning proof. It does not promise an
      // exact nested lexical range; never infer one from indentation.
      if(owner)context.append(button(editText("所在证明","Enclosing proof"),"lr-math-link",()=>selectStatement(owner.id,owner.line)));
      if(context.childNodes.length)target.append(context);
    }
    function inspectorTitle(){
      if(state.issue)return editText("这里为什么没有通过","Why this step was not accepted");
      if(state.keyword)return editText("参考说明","Reference");
      if(state.symbol)return editText("定义与用法","Definition and use");
      if(state.wd)return editText("表达式的条件","Expression requirements");
      const fact=facts.get(state.fact);
      if(fact&&Number.isInteger(state.chainStep))return editText("这个等式为何成立","Why this equality holds");
      if(fact)return fact.role==="hypothesis"?editText("本段的假设","Local hypothesis"):factInferences(fact.id).length?editText("推导依据","Inference grounds"):fact.role==="verified"?editText("这一步怎样得到","How this step follows"):editText("对象的条件","Object requirements");
      return t("mathematicalMeaning");
    }
    function proofRelation(value){
      const result=proofResult(value);
      if(result.type==="ExecByThmStmtSuccess")return theoremConclusion(result.fields?.stored)?.subject.text||null;
      if(result.type==="ExecReleaseThmStmtSuccess"&&array(result.fields?.stored).length===1)return theoremConclusion(result.fields.stored[0])?.subject.text||null;
      const fact=resolveEvidence(result.fields?.fact);
      if(fact.text)return fact.text;
      if(fact.type==="EqualFact"){
        const left=resolveEvidence(fact.fields.left),right=resolveEvidence(fact.fields.right);
        if(left.text&&right.text)return left.text+" = "+right.text;
      }
      return null;
    }
    function proofGrounds(evidence){
      const cited=new Set(),seen=new Set();
      function visit(value){
        const node=resolveEvidence(value);if(!node||typeof node!=="object"||seen.has(node))return;seen.add(node);
        if(node.kind==="fact_reference"&&facts.has(node.fact_id))cited.add(node.fact_id);
        if(node.kind==="statement_reference"){visit(statements.get(node.statement_id)?.evidence);return;}
        for(const [key,child] of Object.entries(node)){
          // Parameter domains and formation are genuine dependencies, retained
          // separately below rather than mixed with the mathematical premises.
          if(["well_defined_proof","well_defined","application_well_defined","body_application_well_defined","param_type_requirements"].includes(key))continue;
          if(Array.isArray(child))child.forEach(visit);else if(child&&typeof child==="object")visit(child);
        }
      }
      visit(evidence);return [...cited];
    }
    function appendProofReferences(target,fact,evidence,omitted=new Set()){
      const cited=proofGrounds(evidence).filter(id=>id!==fact.id),main=cited.filter(id=>!omitted.has(id));
      if(main.length){const premises=element("div","lr-proof-grounds");premises.append(element("h4","lr-proof-section-title",editText("上下文","Context")));main.forEach(id=>premises.append(factButton(id)));target.append(premises);}
      return appendProofApplication(target,fact,evidence)||main.length;
    }
    function appendProofApplication(target,fact,evidence){
      // Only the current result's wrapper chain owns its application. Searching
      // premise trees or earlier cited statements would misattribute their rules.
      const frames=proofFrames(evidence),direct=frames.find(node=>typeof node.rule_id==="string"),membership=frames.find(node=>node.type==="StructuralMembershipProof"),reason=membership&&resolveEvidence(membership.fields?.reason);
      const structural=reason?.type==="StructuralMembershipReason"&&!["Known","Closed"].includes(reason.variant)?reason:null,method=frames.find(node=>["EqualitySearchProofByBuiltinStrategy","AtomicExceptEqualityFactSearchProofByBuiltinStrategy"].includes(node.type));
      if(!direct&&!structural&&!method)return false;
      const node=direct||structural||method,rule=direct&&rules.get(direct.rule_id),name=node.variant||rule?.variant||direct?.rule_id;
      if(!name)return false;
      const application=element("section","lr-proof-application");application.dataset.rule=direct?.rule_id||node.type+"::"+name;
      application.dataset.route=structural?"structural":method?"strategy":"builtin";
      const title=structural?editText("内置推导","Builtin derivation"):!direct&&method?editText("证明策略","Proof strategy"):rule?.category==="builtin_theorem"?editText("使用内置定理","Builtin theorem applied"):editText("使用规则","Rule applied");
      application.append(element("h4","lr-proof-section-title",title),element("code","lr-proof-rule-name",name));
      const comment=node.comment?.[lang()],message=comment?.message||(direct&&ruleMessage(direct.rule_id)),friendly=comment?.name||(rule&&ruleTitle(direct.rule_id));
      if(friendly&&friendly!==name)application.append(element("span","lr-proof-rule-title",friendly));
      if(message)application.append(element("p","lr-proof-rule-message",message));
      if(structural?.variant==="ExactIntegerDiv"){
        if(!comment)application.append(element("p","lr-proof-rule-message",editText("整数被非零整数整除时，其商仍是整数。","The quotient of an integer by a nonzero integer that divides it is an integer.")));
        application.append(formula("a ∈ ℤ, b ∈ ℤ, b ≠ 0, dvd(a, b) ⇒ a / b ∈ ℤ",factLocation(fact).sourceId));
        const numerator=resolveEvidence(resolveEvidence(structural.fields?.numerator).fields?.element),denominator=resolveEvidence(resolveEvidence(structural.fields?.denominator).fields?.element);
        if(numerator.text&&denominator.text)application.append(element("p","lr-proof-substitution",editText("本句取 ","Here take ")+"a = "+mathText(numerator.text,factLocation(fact).sourceId)+", b = "+mathText(denominator.text,factLocation(fact).sourceId)));
      }
      if(proofResult(evidence).type!=="VerifyEqualitySuccess")appendProofResult(application,fact,evidence);
      target.append(application);return true;
    }
    function appendAtomicWellDefinedness(target,fact,evidence,depth){
      const result=proofResult(evidence);
      const theorem=["ExecByThmStmtSuccess","ExecReleaseThmStmtSuccess"].includes(result.type),outputs=result.type==="ExecByThmStmtSuccess"?[result.fields?.stored]:array(result.fields?.stored),output=theorem?outputs.findIndex(value=>theoremConclusion(value)?.id===fact.id):-1;
      if(fact.role==="hypothesis"||!(theorem&&output>=0||["VerifyEqualitySuccess","VerifyAtomicExceptEqualityFactSuccess","PeerEqualitySuccess"].includes(result.type)||["VerifyEqualityFailed","VerifyAtomicExceptEqualityFactFailed"].includes(result.type)&&result.variant==="FailToSearchProof"))return;
      const proof=theorem?(result.type==="ExecByThmStmtSuccess"?result.fields?.selected_wd:result.fields?.stored_wd?.[output]):result.fields?.well_defined_proof,tail=element("details","lr-proof-formation lr-atomic-wd"),summary=element("summary",null,editText("表达式有定义","Well-defined expressions"));tail.append(summary);target.append(tail);let rendered=false;
      tail.addEventListener("toggle",()=>{
        if(!tail.open||rendered)return;rendered=true;
        const conditions=[],objects=[],cited=new Set(),seen=new Set();let unavailable=!proof;
        // Visit only the current atomic WD certificate. Stop at each verified
        // requirement: its own proof and WD belong to its nested disclosure.
        function visit(value){
          const node=resolveEvidence(value);if(!node||typeof node!=="object"||seen.has(node))return;seen.add(node);
          if(Array.isArray(node)){node.forEach(visit);return;}
          if(node.kind==="unavailable"||["Compact","Normal"].includes(node.variant)&&["AtomicFactWellDefinedProof","EqualFactWellDefinedProof","ObjWellDefinedProof"].includes(node.type)){unavailable=true;return;}
          if(["VerifyEqualitySuccess","VerifyAtomicExceptEqualityFactSuccess"].includes(node.type)){conditions.push({requirement:node.fields.fact,evidence:value});return;}
          if(node.type==="PredicateDomainArgumentMembershipProof"){conditions.push({requirement:node.fields.requirement,evidence:node.fields.membership,structural:true});return;}
          if(node.kind==="fact_reference"&&facts.has(node.fact_id))cited.add(node.fact_id);
          if(node.type==="DetailedAtomicFactWellDefinedProof"&&(!Array.isArray(node.fields?.well_defined_of_each_parameter)||!node.fields?.predicate_signature||!node.fields?.predicate_domain))unavailable=true;
          if(node.type==="DetailedEqualFactWellDefinedProof"&&(!node.fields?.left||!node.fields?.right))unavailable=true;
          if(node.type==="DetailedObjWellDefinedProof"){
            const object=resolveEvidence(node.fields?.obj),reference=resolveEvidence(node.fields?.wd_id);
            if(object.text)objects.push({text:object.text,reference:reference.id});
          }
          for(const [key,child] of Object.entries(node.fields||{})){if(!["obj","fact","requirement"].includes(key))visit(child);}
        }
        visit(proof);
        if(theorem){for(const typeProof of array(result.fields?.type_proofs)){const condition=proofResult(typeProof).fields?.fact;if(condition)conditions.push({requirement:condition,evidence:typeProof});else unavailable=true;}if(!Array.isArray(result.fields?.type_proofs))unavailable=true;
          if(result.fields?.function_domain){const domain=element("details","lr-proof-step");domain.append(element("summary",null,editText("函数参数的完整定义域已核验","Complete function-argument domains checked")),element("p","lr-empty-note",editText("本次应用保留了函数定义域核验记录；此类记录的逐步解说尚未提供。","This application retains function-domain checks; a step-by-step explanation of this record is not available yet.")));tail.append(domain);}
        }
        // Definition expansion can select a narrower body domain than the
        // callable's outer signature. Keep those retained checks in this same
        // final disclosure, rather than presenting them as truth-search steps.
        for(const frame of proofFrames(evidence))for(const key of ["normalization","left_normalization","right_normalization"]){const normalization=resolveEvidence(frame.fields?.[key]);if(normalization.type==="FunctionBodyNormalizationProof")for(const value of array(normalization.fields?.expansions)){const expansion=resolveEvidence(resolveEvidence(value).fields?.["0"]);if(expansion.fields?.application_well_defined)visit(expansion.fields.application_well_defined);if(expansion.fields?.body_application_well_defined)visit(expansion.fields.body_application_well_defined);}}
        if(objects.length){const list=element("div","lr-wd-objects");list.append(element("p","lr-empty-note",editText("本句中的对象与运算：","Objects and operations in this statement:")));for(const object of objects){const item=element("div","lr-wd-object");item.append(formula(object.text,factLocation(fact).sourceId));if(object.reference&&wellDefinedness.has(object.reference))item.append(button(editText("已有定义","Previously established"),"lr-text-link",()=>selectWellDefinedness(object.reference)));list.append(item);}tail.append(list);}
        if(conditions.length){tail.append(element("p","lr-empty-note",editText("定义域条件及其证明：","Domain conditions and their proofs:")));for(const condition of conditions){
          if(!condition.structural){appendProofRequirement(tail,fact,condition.requirement,condition.evidence,depth);continue;}
          const text=resolveEvidence(condition.requirement).text,step=element("details","lr-proof-step");step.append(element("summary",null,text?mathText(text,factLocation(fact).sourceId):editText("参数属于声明域","Argument in its declared domain")));let shown=false;step.addEventListener("toggle",()=>{if(step.open&&!shown){shown=true;appendProofBody(step,{...fact,id:null,role:"verified",evidence:condition.evidence},condition.evidence,false,depth+1);positionOverlays();}});tail.append(step);
        }}else if(!unavailable)tail.append(element("p","lr-empty-note",editText("本句的对象及谓词签名已检查；此记录没有额外的定义域条件。","The objects and predicate signature were checked; this record contains no additional domain conditions.")));
        if(cited.size){const context=element("div","lr-proof-grounds");context.append(element("p","lr-empty-note",editText("引用的定义域依据：","Cited domain evidence:")));for(const id of cited)context.append(factButton(id));tail.append(context);}
        if(unavailable)tail.append(element("p","lr-empty-note",editText("此处未完整导出表达式有定义的证明。","The well-definedness proof was not fully exported here.")));positionOverlays();
      });
    }
    function appendProofBody(target,fact,evidence=fact.evidence,steps=true,depth=0){
      appendProofMain(target,fact,evidence,steps,depth);
      appendAtomicWellDefinedness(target,fact,evidence,depth);
    }
    function appendProofMain(target,fact,evidence=fact.evidence,steps=true,depth=0){
      if(steps)appendProofContext(target,fact);
      if(fact.role==="hypothesis"){
        target.append(element("p","lr-proof-summary",editText("在当前证明中假定此条件成立。","This condition is assumed in the current proof.")));return;
      }
      const producer=statements.get(fact.producer_statement_id),record=proofRecord(evidence);
      if(producer?.origin&&producer.origin!=="checked")target.append(element("p","lr-origin-note",t(producer.origin)));
      if(array(producer?.trust_dependencies).length)target.append(element("p","lr-origin-note",t("trustUsed")));
      if(!evidence||record.kind==="unavailable"){
        target.append(element("p","lr-empty-note",editText("这条事实已验证，但此处没有导出它的逐步证明记录。","This fact was verified, but its proof steps were not exported here.")));return;
      }
      if(appendTheoremApplication(target,fact,evidence,record,depth))return;
      if(appendUniversalApplication(target,fact,evidence,record,depth)||appendKnownApplication(target,fact,evidence,record,depth)||appendObjectDefinitionApplication(target,fact,evidence,depth)||appendSpecialPropertyApplication(target,fact,evidence,depth)||appendEqualityTransport(target,fact,evidence,depth))return;
      if(record.type==="ExecByContraStmtSuccess"){
        target.append(element("p","lr-proof-summary",editText("反证法：假设目标的否定，在此假设下推出矛盾，从而得到原目标。","Proof by contradiction: assume the negation of the goal and derive a contradiction, establishing the original goal.")));
        const assumption=resolveEvidence(record.fields.reverse_assumption_fact_id),closing=resolveEvidence(record.fields.closing);
        if(facts.has(assumption.fact_id)){const context=element("div","lr-proof-grounds");context.append(element("span","lr-empty-note",editText("反证假设","Contradiction assumption")),factButton(assumption.fact_id));target.append(context);}
        if(closing.type==="ByContradictionClosingSuccess"){
          target.append(element("p","lr-proof-summary",editText("在此假设下，同时得到下面两条互相矛盾的事实：","Under this assumption, the following two incompatible facts are established:")));
          appendProofRequirement(target,fact,closing.fields.impossible_fact,closing.fields.impossible,depth);
          const opposite=closing.fields.negated_impossible;appendProofRequirement(target,fact,proofResult(opposite).fields?.fact,opposite,depth);
        }else target.append(element("p","lr-empty-note",editText("此处没有导出产生矛盾的结束步骤。","The contradiction's closing step was not exported here.")));
        return;
      }
      if(steps&&record.type==="VerifyChainFactSuccess"&&array(record.fields.adjacent).length){
        target.append(element("p","lr-proof-summary",editText("分别验证每个相邻关系；整条链表示这些关系同时成立。","Verify each adjacent relation; the complete chain asserts all of these relations together.")));
        array(record.fields.adjacent).forEach((part,index)=>{
          const step=element("details","lr-proof-step"),summary=element("summary",null,editText("第 "+(index+1)+" 步","Step "+(index+1)));step.append(summary);
          const relation=proofRelation(part);
          if(relation)summary.append(formula(relation,fact.source_id));
          appendProofBody(step,fact,part,false,depth+1);target.append(step);
        });return;
      }
      const frames=proofFrames(evidence);let requirements=frames.find(node=>Array.isArray(node.fields?.requirement_facts)&&Array.isArray(node.fields?.proof_of_requirement_facts));
      if(!requirements){
        const children={IntersectMembershipBuiltinRuleProof:["left_membership_proof","right_membership_proof"],UnionMembershipFromLeftBuiltinRuleProof:["left_membership_proof"],UnionMembershipFromRightBuiltinRuleProof:["right_membership_proof"],SetMinusMembershipBuiltinRuleProof:["left_membership_proof","right_non_membership_proof"]};
        const rule=frames.find(node=>children[node.type]);if(rule){const proofs=children[rule.type].map(key=>rule.fields?.[key]);requirements={fields:{requirement_facts:proofs.map(proof=>proofResult(proof).fields?.fact),proof_of_requirement_facts:proofs}};}
      }
      if(requirements){
        appendPredicateApplication(target,fact,evidence);
        const descriptions={IntersectMembership:["按交集的定义，分别证明该元素属于两个集合。","By the definition of intersection, establish membership in both sets."],UnionMembershipFromLeft:["该元素属于左边的集合，因此属于并集。","Membership in the left set establishes membership in the union."],UnionMembershipFromRight:["该元素属于右边的集合，因此属于并集。","Membership in the right set establishes membership in the union."],ByDefinition:["将实参代入谓词定义，验证参数类型要求及全部定义条件。","Substitute the arguments into the predicate definition and verify its parameter requirements and all defining conditions."],ArithmeticCongruence:["在算式中使用已知等式，验证替换后的结果相等。","Use known equalities inside the arithmetic expression to verify equal results."]};
        const name=frames.map(node=>node.variant).find(name=>descriptions[name]),description=descriptions[name]||["验证下面的条件后，应用记录中的规则得到本句结论。","The recorded rule establishes this conclusion from the following verified conditions."];
        target.append(element("p","lr-proof-summary",description[lang()==="zh"?0:1]));
        const fields=requirements.fields,conditions=fields.requirement_facts,proofs=fields.proof_of_requirement_facts;
        if(conditions.length!==proofs.length){conditions.forEach(condition=>{const text=resolveEvidence(condition).text;if(text)target.append(formula(text,factLocation(fact).sourceId));});target.append(element("p","lr-empty-note",editText("条件与证明记录不完整，无法逐项对应。","The conditions and proof records are incomplete and cannot be paired.")));return;}
        const context=element("div","lr-proof-requirements");context.append(element("h4","lr-proof-section-title",editText("验证的前提","Verified premises")));conditions.forEach((condition,index)=>appendProofRequirement(context,fact,condition,proofs[index],depth));target.append(context);appendProofReferences(target,fact,evidence);return;
      }
      const listed=frames.find(node=>node.type==="ListSetElementMembershipBuiltinRuleProof"),excluded=frames.find(node=>node.type==="ListSetExhaustiveDisequalityBuiltinRuleProof");
      if(listed){target.append(element("p","lr-proof-summary",editText("在这个有限集合列出的元素中，找到了与它相等的一项，因此它属于该集合。","One of the listed elements of this finite set is equal to the given object, establishing membership.")));const proof=listed.fields.equality_proof;appendProofRequirement(target,fact,proofResult(proof).fields?.fact,proof,depth);appendProofApplication(target,fact,evidence);return;}
      if(excluded){target.append(element("p","lr-proof-summary",editText("它与这个有限集合中列出的每个元素都不相等，因此不属于该集合。","It differs from every listed element of this finite set, establishing non-membership.")));for(const proof of array(excluded.fields.disequality_proofs))appendProofRequirement(target,fact,proofResult(proof).fields?.fact,proof,depth);appendProofApplication(target,fact,evidence);return;}
      const descriptions={
        ByKnownForallFact:["把全称命题用于当前对象，并验证它所要求的前提。","Apply the universal statement to the current objects and verify its premises."],
        ByKnownAtomicFact:["引用已建立的事实。","Use an already established fact."],
        ByTheyAreTheSame:["两边表示同一对象。","Both sides denote the same object."],
        ByClosedCalculation:["通过精确计算验证本句的关系。","Exact calculation verifies the stated relation."],
        ByMatchingOneArgByOne:["同一运算的对应参数分别相等，因此运算结果相等。","Corresponding arguments of the same operation are equal, so the results are equal."]
      },description=descriptions[record.variant];
      const builtin=resolveEvidence(record.fields?.["0"]),builtinDescription=builtin.type==="EqualitySearchProofByBuiltinRule"&&builtin.variant==="Calculation"?["按内置运算规则验证这个等式。","Verify this equality using the builtin calculation rules."]:builtin.type==="EqualitySearchProofByBuiltinStrategy"&&builtin.variant==="ArithmeticCongruence"?["在算式中使用已知等式，验证替换后的结果相等。","Use known equalities inside the arithmetic expression to verify equal results."]:null;
      const explanation=description||builtinDescription||(record.type==="VerifyKnownForallFactProof"?["引用同一个全称命题，绑定变量的名称按记录对应。","Use the same universal statement with the recorded correspondence between bound variables."]:null);
      if(explanation)target.append(element("p","lr-proof-summary",explanation[lang()==="zh"?0:1]));
      if(record.variant==="ByMatchingOneArgByOne"&&depth<2){
        for(const part of array(resolveEvidence(record.fields?.["0"]).fields?.corresponding_arg_equal_proofs)){
          const relation=proofRelation(part);if(!relation||proofRecord(part).variant==="ByTheyAreTheSame")continue;
          const child=element("details","lr-proof-step"),summary=element("summary",null,editText("代入相等关系","Substitute an equality"));summary.append(formula(relation,factLocation(fact).sourceId));child.append(summary);appendProofBody(child,fact,part,false,depth+1);target.append(child);
        }
      }
      if(!appendProofReferences(target,fact,evidence)&&!explanation)target.append(element("p","lr-proof-summary",editText("这一步已验证；此类证明的逐步解说尚未提供。","This step was verified; a step-by-step explanation of this proof form is not available yet.")));
    }
    function appendEqualityStep(target,fact,index){
      const evidence=equalityStepEvidence(fact,index),relation=evidence&&proofRelation(evidence);
      if(!evidence||!relation){target.append(element("p","lr-empty-note",editText("此处没有可单独展示的相邻等式证明。","No separate proof of this adjacent equality is available here.")));return;}
      target.append(formula(relation,factLocation(fact).sourceId));appendProofContext(target,fact);appendProofBody(target,fact,evidence,false);
    }
    function openSourcePreview(owner,title,renderBody,settings={}){
      const {select,selection=null,persistent=false}=settings;
      closeProof();hideTokenHelp();
      const node=element("section","lr-proof-popover"),header=element("div","lr-proof-header"),body=element("div","lr-proof-body");
      node.id="lr-proof-"+Math.random().toString(36).slice(2);node.setAttribute("role","region");node.setAttribute("aria-label",title);
      header.append(element("strong",null,title));
      if(select){const pin=button(editText("固定","Keep open"),"lr-proof-pin",async()=>{if(await select()){detailPane.tabIndex=-1;detailPane.focus({preventScroll:true});}});header.append(pin);}
      const close=button("×","lr-explanation-close",()=>closeProof(true));close.setAttribute("aria-label",editText("关闭源码说明","Close source explanation"));header.append(close);node.append(header,body);
      body.addEventListener("toggle",positionProof,true);
      if(settings.factPreview){
        node.classList.add("lr-fact-preview");const proof=element("div","lr-proof-evidence"),symbol=element("aside","lr-proof-symbol");symbol.hidden=true;symbol.setAttribute("aria-label",editText("符号说明","Symbol information"));body.append(proof,symbol);renderBody(proof);
      }else renderBody(body);
      node.addEventListener("pointerenter",keepProofOpen);node.addEventListener("pointerleave",leaveProof);
      node.addEventListener("focusin",keepProofOpen);node.addEventListener("focusout",event=>{if(!node.contains(event.relatedTarget))leaveProof();});
      root.append(node);owner.setAttribute("aria-describedby",node.id);proofPopover={node,owner,selection,persistent};owner.classList.add("lr-proof-target");
      positionProof();return node;
    }
    function openProof(owner,ids,chainStep=null){
      if(chainStep!==null)closeExplanation();
      const title=chainStep!==null?editText("这个等式为何成立","Why this equality holds"):ids.every(id=>facts.get(id)?.role==="hypothesis")?editText("本段的假设","Local hypothesis"):editText("这一步怎样得到","How this step follows");
      openSourcePreview(owner,title,body=>{
        for(const id of ids){const fact=facts.get(id);if(!fact)continue;const part=element("div","lr-proof-part");part.dataset.fact=id;if(chainStep!==null)appendEqualityStep(part,fact,chainStep);else{if(ids.length>1)part.append(factFormula(fact));appendProofBody(part,fact);}body.append(part);}
      },{factPreview:true,select:ids.length===1?()=>selectFact(ids[0],chainStep):null,selection:ids.length===1?factSelection(ids[0],chainStep):null});
      const premises=new Set(ids.flatMap(id=>proofGrounds(chainStep!==null?equalityStepEvidence(facts.get(id),chainStep):facts.get(id)?.evidence)).map(id=>facts.get(id)).filter(fact=>fact?.source_id===state.source&&fact.line).map(fact=>fact.line));
      codePane.querySelectorAll(".lr-code-row").forEach(row=>row.classList.toggle("lr-proof-premise",premises.has(Number(row.dataset.line))&&row!==(owner.closest(".lr-code-row")||owner)));
    }
    function positionProof(){
      if(!proofPopover)return;const {node,owner}=proofPopover,box=owner.getBoundingClientRect();
      if(!sourceAnchorVisible(owner,box)){closeProof();return;}
      placeAtSource(node,box,owner.matches(".lr-code-row")?48:0);
    }
    function sourceAnchorVisible(owner,box){
      if(!owner?.isConnected)return false;
      const view=document.documentElement,pane=(owner.closest(".lr-ide")||codePane).getBoundingClientRect();
      return box.bottom>Math.max(0,pane.top)&&box.top<Math.min(view.clientHeight,pane.bottom)&&box.right>Math.max(0,pane.left)&&box.left<Math.min(view.clientWidth,pane.right);
    }
    function placeAtSource(node,box,inset=0){
      // Every explanation shares source anchoring; no viewport-edge inspector.
      const view=document.documentElement,rect=node.getBoundingClientRect();
      node.style.left=Math.max(8,Math.min(box.left+inset,view.clientWidth-rect.width-8))+"px";
      node.style.top=Math.max(8,box.bottom+8+rect.height<=view.clientHeight?box.bottom+8:Math.min(box.top-rect.height-8,view.clientHeight-rect.height-8))+"px";
    }
    function hideTokenHelp(){if(tokenHelp){tokenHelp.node.remove();tokenHelp.owner.removeAttribute("aria-describedby");tokenHelp=null;}}
    function closeExplanation(restoreFocus=false){
      const panel=root.querySelector(".lr-context-explanation"),focused=panel?.contains(document.activeElement);
      state.explanationOpen=false;peekCitation(null);if(panel)panel.hidden=true;root.querySelectorAll("[data-keyword]").forEach(token=>token.setAttribute("aria-expanded","false"));
      if(restoreFocus&&focused){
        const input=root.querySelector(".lr-ide-input");
        if(input)input.focus({preventScroll:true});
        else{
          const row=root.querySelector('.lr-code-row[data-line="'+state.focusLine+'"]')||root.querySelector(".lr-code-row.lr-selected"),keyword=state.keyword&&[...row?.querySelectorAll("[data-keyword]")||[]].find(token=>token.dataset.keyword===state.keyword);
          restoreSourceFocus(row?.querySelector(".lr-equality-selected,.lr-symbol-selected")||keyword||row?.querySelector(".lr-line-number"));
        }
      }
    }
    function showExplanation(){const panel=root.querySelector(".lr-context-explanation");if(!panel)return;panel.hidden=!state.explanationOpen;root.querySelectorAll("[data-keyword]").forEach(token=>token.setAttribute("aria-expanded",String(!!state.explanationOpen&&token.dataset.keyword===state.keyword&&Number(token.closest(".lr-code-row")?.dataset.line)===state.focusLine)));if(state.explanationOpen)positionExplanation();}
    function positionExplanation(){
      const panel=root.querySelector(".lr-context-explanation");if(!panel||panel.hidden||!codePane)return;
      const row=[...codePane.querySelectorAll(".lr-code-row")].find(node=>Number(node.dataset.line)===state.focusLine)||codePane.querySelector(".lr-code-row.lr-selected");
      const keyword=state.keyword&&[...row?.querySelectorAll("[data-keyword]")||[]].find(node=>node.dataset.keyword===state.keyword);
      const anchor=(state.chainStep!=null&&row?.querySelector(".lr-equality-selected"))||(state.symbol&&row?.querySelector(".lr-symbol-selected"))||keyword||row||codePane;
      const box=anchor.getBoundingClientRect();
      if(!sourceAnchorVisible(anchor,box)){closeExplanation();return;}
      placeAtSource(panel,box,anchor===row?40:0);
    }
    function positionOverlays(){positionTokenHelp();positionInferences();positionExplanation();positionProof();}
    function positionTokenHelp(){
      if(!tokenHelp)return;const box=tokenHelp.owner.getBoundingClientRect(),tip=tokenHelp.node;
      if(!sourceAnchorVisible(tokenHelp.owner,box)){hideTokenHelp();return;}
      placeAtSource(tip,box);
    }
    function attachTokenHelp(token,heading,meaning,symbolId,builtin,referenceKey=heading){
      token.setAttribute("aria-label",heading+" · "+meaning);
      function render(tip){
        tip.append(element("strong",null,heading),element("span",null,meaning));
        const reference=symbolId?theoremReference(symbolId)||(symbolId.startsWith("builtin:set:")?referenceCard(symbolId.slice("builtin:set:".length)):null):referenceCard(referenceKey);if(reference){tip.replaceChildren(element("strong",null,heading));appendReference(tip,reference,true);}
        if(symbolId&&!builtinTheoremSymbols.has(symbolId)){
          const declaration=symbolDefinitions.get(symbolId),info=element("div","lr-symbol-info");tip.append(info);
          const appendDefinition=()=>{
            info.replaceChildren();const data=definitionSource(symbolId),parameter=symbolParameters.get(symbolId);
            const model=symbolDefinitions.get(symbolId)?.mathematics;
            if(model&&["predicate_definition","abstract_predicate"].includes(model.kind)){
              const section=element("section","lr-predicate-definition");if(model.kind==="predicate_definition")appendPredicateMeaning(section,model,declaration.source_id);else section.append(formula(model.subject,declaration.source_id),element("p","lr-empty-note",t("abstractMeaning")));info.append(section);
            }
            if(data){info.append(element("small",null,data.location));if(parameter)info.append(element("div","lr-symbol-domain",parameterText(parameter,data.sourceId)));info.append(element("pre","lr-definition-source",data.code));}
            info.append(element("small",null,t("currentFileReferences").replace("{count}",referenceUses(symbolId,state.source).length)));
            positionTokenHelp();
          };
          appendDefinition();
          if(loader&&declaration&&typeof sources.get(declaration.source_id)?.content!=="string"){
            const epoch=generation,loading=element("small",null,t("loading"));tip.append(loading);
            loader.loadSource(declaration.source_id).then(chunk=>{if(destroyed||epoch!==generation||!info.isConnected||!token.isConnected)return;mergeReadingChunk(bundle,chunk);index();loading.remove();appendDefinition();}).catch(()=>{if(info.isConnected)loading.textContent=t("loadFailed");});
          }
        }
      }
      tokenHelpRenderers.set(token,render);
      function show(){
        if(proofFocusSuppression===token)return;
        if(hoverProofTarget(token))return;
        if(tokenHelp?.owner===token)return;hideTokenHelp();
        const tip=element("div","lr-token-help"),id="lr-token-help-"+Math.random().toString(36).slice(2);tip.id=id;tip.setAttribute("role","tooltip");
        root.append(tip);token.setAttribute("aria-describedby",id);tokenHelp={node:tip,owner:token};render(tip);
        positionTokenHelp();
      }
      tokenHelpOpeners.set(token,show);
      token.addEventListener("mouseenter",show);token.addEventListener("focus",show);
      token.addEventListener("mouseleave",hideTokenHelp);token.addEventListener("blur",()=>{hideTokenHelp();leaveProof();});
      token.addEventListener("keydown",event=>{if(event.key==="Escape")hideTokenHelp();});
    }
    function symbolHelp(id){
      if(builtinTheoremSymbols.has(id))return lang()==="zh"?"内置定理":"Builtin theorem";
      const kind=symbols.get(id)?.kind,names={DefThmStmt:["定理","Theorem"],AxiomStmt:["公理","Axiom"],DefStrategyStmt:["证明策略","Proof strategy"]};if(names[kind])return names[kind][lang()==="zh"?0:1];
      if(!id.startsWith("builtin:set:"))return null;
      return standardSetHelp[id.slice("builtin:set:".length)]?.[lang()==="zh"?0:1]||null;
    }

    function renderCode(){
      const source=sources.get(state.source);if(!source)return;
      const content=source.content||"";const offsets=bytePositions(content);
      const sourceStatements=statementsBySource.get(source.id)||[];
      const expressionHints=sourceStatements.flatMap(statement=>array(statement.expression_hints)).filter(hint=>{
        if(!hint||typeof hint!=="object")return false;
        const start=offsets.get(hint.start_byte),end=offsets.get(hint.end_byte);
        return Number.isInteger(hint.start_byte)&&Number.isInteger(hint.end_byte)&&hint.start_byte<hint.end_byte&&start!==undefined&&end!==undefined&&typeof hint.source_text==="string"&&content.slice(start,end)===hint.source_text&&!!referenceCard(hint.reference_key);
      });
      function expressionReference(occurrence){
        const candidates=expressionHints.filter(hint=>hint.start_byte<=occurrence.start_byte&&hint.end_byte>=occurrence.end_byte).sort((a,b)=>(a.end_byte-a.start_byte)-(b.end_byte-b.start_byte));
        const first=candidates[0];if(!first)return null;
        return candidates.some(hint=>hint.start_byte===first.start_byte&&hint.end_byte===first.end_byte&&hint.reference_key!==first.reference_key)?null:first.reference_key;
      }
      const selected=statements.get(state.statement);
      const selectedFact=facts.get(state.fact),stepEvidence=equalityStepEvidence(selectedFact,state.chainStep);
      const citations=state.wd?wdCitations(wellDefinedness.get(state.wd)):stepEvidence?factCitations({evidence:stepEvidence}):state.fact?factCitations(selectedFact):array(selected?.cited_fact_ids);
      const premiseLines=new Set(citations.map(id=>factLocation(facts.get(id))).filter(value=>value.sourceId===source.id).map(value=>value.line));
      function selectLine(owning,line){const issues=issuesByLine.get(source.id+":"+line)||[];if(issues.length){selectSourceIssue((issues.find(issue=>issue.statementId===owning?.id)||issues[0]).id);return;}const matches=lineProofFacts(source.id,line);if(matches.length===1)selectFact(matches[0].id);else if(owning)selectStatement(owning.id,line);}
      const mentions=occurrences.filter(value=>value.source_id===source.id).map(value=>({...value,start:offsets.get(value.start_byte),end:offsets.get(value.end_byte)})).filter(value=>value.start!==undefined&&value.end!==undefined).sort((a,b)=>a.start-b.start);
      let mentionIndex=0;
      const lexical=array(source.tokens).map(value=>({...value,start:offsets.get(value.start_byte),end:offsets.get(value.end_byte)})).filter(value=>value.start!==undefined&&value.end!==undefined).sort((a,b)=>a.start-b.start).filter(value=>{while(mentionIndex<mentions.length&&mentions[mentionIndex].end<=value.start)mentionIndex++;return !mentions[mentionIndex]||mentions[mentionIndex].start>=value.end;});
      const declarationsAt=new Map();
      for(const declaration of declarationsBySource.get(source.id)||[]){const start=offsets.get(declaration.start_byte);if(start===undefined)continue;const line=content.slice(0,start).split("\n").length;if(!declarationsAt.has(line))declarationsAt.set(line,[]);declarationsAt.get(line).push(declaration);}
      const inferredAt=new Map();
      for(const statement of sourceStatements){
        const line=statement.line;
        for(const id of statementInferredFacts(statement))if(facts.has(id)&&factInferences(id).length){if(!inferredAt.has(line))inferredAt.set(line,[]);inferredAt.get(line).push(id);}
      }
      const hasTokens=array(source.tokens).length>0;
      function appendTrivia(target,text){if(hasTokens&&text.trim())target.append(element("span","lr-syntax-comment",text));else target.append(document.createTextNode(text));}
      let lineStart=0,lineByteStart=0,proofTokenIndex=0;const encoder=new TextEncoder(),proofTokens=array(source.tokens).slice().sort((a,b)=>a.start_byte-b.start_byte);
      const lines=content.split("\n");
      for(let i=0;i<lines.length;i++){
        const lineNumber=i+1,line=lines[i],lineEnd=lineStart+line.length,lineByteEnd=lineByteStart+encoder.encode(line).length;
        const owning=owningStatement(source.id,lineNumber,lineByteStart);
        const lineIssues=issuesByLine.get(source.id+":"+lineNumber)||[],issuePoints=lineIssues.filter(issue=>Number.isInteger(issue.column)&&issue.column>0&&issue.column<=Array.from(line).length+1).map(issue=>({issue,offset:lineStart+Array.from(line).slice(0,issue.column-1).join("").length}));
        const row=element("div","lr-code-row");row.dataset.line=String(lineNumber);if(owning)row.dataset.statement=owning.id;if(lineIssues.length){row.classList.add("lr-rejected");row.dataset.issues=JSON.stringify(lineIssues.map(issue=>issue.id));row.addEventListener("pointermove",event=>hoverProofTarget(event.target));row.addEventListener("pointerleave",leaveProof);}
        while(proofTokenIndex<proofTokens.length&&proofTokens[proofTokenIndex].end_byte<=lineByteStart)proofTokenIndex++;
        const proofLineTokens=[];for(let j=proofTokenIndex;j<proofTokens.length&&proofTokens[j].start_byte<lineByteEnd;j++)if(proofTokens[j].start_byte>=lineByteStart&&proofTokens[j].end_byte<=lineByteEnd)proofLineTokens.push(proofTokens[j]);
        const rowFacts=lineProofFacts(source.id,lineNumber),equalityTargets=equalityTokenTargets(rowFacts,proofLineTokens);if(rowFacts.length){row.dataset.proofFacts=JSON.stringify(rowFacts.map(fact=>fact.id));row.addEventListener("pointermove",event=>hoverProofTarget(event.target));row.addEventListener("pointerleave",leaveProof);}
        if(state.focusLine?lineNumber===state.focusLine:owning?.id===state.statement)row.classList.add("lr-selected");else if(premiseLines.has(lineNumber))row.classList.add("lr-premise");
        const number=button(String(lineNumber),"lr-line-number",()=>selectLine(owning,lineNumber));number.disabled=!owning&&!lineIssues.length;number.setAttribute("aria-label",t("sourceLine")+" "+lineNumber);row.append(number);
        if(lineIssues.length){number.classList.add("lr-error-line");number.title=lineIssues.map(sourceIssueLabel).join("\n");number.addEventListener("focus",()=>hoverProofTarget(number));number.addEventListener("blur",leaveProof);}
        if(rowFacts.length){
          number.title=editText("悬浮查看依据，点击固定说明","Hover for proof; click to keep it open");number.setAttribute("aria-description",number.title);
          number.addEventListener("focus",()=>hoverProofTarget(number));number.addEventListener("blur",leaveProof);
          number.addEventListener("keydown",event=>{if((event.key==="ArrowRight"||event.key==="Tab"&&!event.shiftKey)&&proofPopover?.owner===row){event.preventDefault();proofPopover.node.querySelector(".lr-proof-pin,.lr-fact-link,.lr-explanation-close")?.focus();}});
        }
        const lineContent=element("div","lr-code-content"),code=element("code","lr-source-code");let cursor=lineStart;
        const appendToken=(token,occurrence)=>{
          if(token.textContent==="="&&!token.dataset.symbol&&equalityTargets.has(occurrence.start_byte))attachEqualityProof(token,equalityTargets.get(occurrence.start_byte));
          const point=issuePoints.find(point=>point.offset>=occurrence.start&&point.offset<occurrence.end);if(point)attachSourceIssue(token,point.issue);
          code.append(token);
        };
        const lineTokens=[...mentions.filter(value=>value.start>=lineStart&&value.end<=lineEnd),...lexical.filter(value=>value.start>=lineStart&&value.end<=lineEnd)].sort((a,b)=>a.start-b.start||Number(!!b.symbol_id)-Number(!!a.symbol_id)||Number(a.text==="$")-Number(b.text==="$"));
        const grouped=[];
        for(let j=0;j<lineTokens.length;j++){
          const first=lineTokens[j],next=lineTokens[j+1];
          if(!first.symbol_id&&next&&!next.symbol_id&&first.text==="exist"&&next.text==="!"&&/^[ \t]*$/.test(content.slice(first.end,next.start))){grouped.push({...first,text:"exist!",end:next.end});j++;continue;}
          // Longest documented phrase over actual adjacent lexer spans. Never
          // join resolved symbols, cross comments/newlines, or parse an AST.
          let phrase=first.text,best=null;
          if(!first.symbol_id)for(let end=j+1;end<Math.min(j+4,lineTokens.length);end++){
            const previous=lineTokens[end-1],part=lineTokens[end];if(part.symbol_id||!/^[ \t]+$/.test(content.slice(previous.end,part.start)))break;
            phrase+=" "+part.text;if(syntaxPhrases[phrase]||Object.prototype.hasOwnProperty.call(languageReference.entries,phrase))best={text:phrase,end:part.end,index:end};
          }
          if(best){grouped.push({...first,text:best.text,end:best.end});j=best.index;}else grouped.push(first);
        }
        for(const occurrence of grouped){
          if(occurrence.start<cursor)continue;
          appendTrivia(code,content.slice(cursor,occurrence.start));
          const spelling=content.slice(occurrence.start,occurrence.end);
          const tokenText=occurrence.text||spelling;
          if(!occurrence.symbol_id||(["operator","punctuation"].includes(lexicalKinds.get(tokenText))&&!symbolDefinitions.has(occurrence.symbol_id))){
            const phrase=tokenText.includes(" ")&&Object.prototype.hasOwnProperty.call(languageReference.entries,tokenText),role=languageReference.entries[tokenText]?.role||(setOperatorHelp[tokenText]?"operator":syntaxPhrases[tokenText]||phrase?"keyword":lexicalKinds.get(tokenText))||(/^\d+(?:\.\d+)?$/.test(tokenText)?"number":"identifier"),token=element("span","lr-syntax-"+role,spelling);token.dataset.syntax=role;
            const kind=String(owning?.statement_kind||"").split(".").at(-1),typed=kind!=="Fact"&&role==="keyword"&&owning?.line===lineNumber&&occurrence.start===lineStart+line.search(/\S/)&&Object.prototype.hasOwnProperty.call(languageReference.statements,kind),contextKey=expressionReference(occurrence),contextual=(["punctuation","identifier"].includes(role)||tokenText==="&"&&contextKey==="obj:struct_type"||["<",">"].includes(tokenText)&&["obj:struct_type","obj:template"].includes(contextKey))&&contextKey,referenceKey=contextual||(typed?"stmt:"+kind:role==="number"?"literal:number":tokenText);
            const builtin=builtinObjectHelp[tokenText],reference=referenceCard(referenceKey),help=reference?.summary||builtin?.[lang()==="zh"?2:3]||(syntaxPhrases[tokenText]|| (Object.prototype.hasOwnProperty.call(syntaxHelp,tokenText)?syntaxHelp[tokenText]:syntaxRoleHelp[role]))?.[lang()==="zh"?0:1];
            if(help){token.tabIndex=0;if(contextual)token.dataset.expressionReference=contextual;attachTokenHelp(token,spelling,help,null,builtin,referenceKey);if(!contextual&&(reference||syntaxPhrases[tokenText]||(role==="keyword"&&syntaxHelp[tokenText]))&&!(tokenText==="="&&equalityTargets.has(occurrence.start_byte))){token.setAttribute("role","button");token.dataset.keyword=tokenText;token.dataset.referenceKey=referenceKey;token.setAttribute("aria-expanded",String(state.keyword===tokenText&&state.focusLine===lineNumber));const open=async()=>{if(state.keyword===tokenText&&state.focusLine===lineNumber){await selectStatement(owning?.id,lineNumber);root.querySelector('.lr-code-row[data-line="'+lineNumber+'"] [data-keyword="'+tokenText+'"]')?.focus();}else{await navigate({keyword:tokenText,statement:owning?.id||null,symbol:null,fact:null,wd:null,focusLine:lineNumber,explanationOpen:true});detailPane.tabIndex=-1;detailPane.focus({preventScroll:true});}};token.addEventListener("click",event=>{event.stopPropagation();open();});token.addEventListener("keydown",event=>{if(["Enter"," "].includes(event.key)){event.preventDefault();open();}});}}appendToken(token,occurrence);cursor=occurrence.end;continue;
          }
          const role=symbolRoles.get(occurrence.symbol_id)||"object",token=button(spelling,"lr-token lr-syntax-"+role,event=>{event.stopPropagation();selectSymbol(occurrence.symbol_id,owning?.id,lineNumber);});token.dataset.symbol=occurrence.symbol_id;token.dataset.syntax=role;
          const builtinMeaning=symbolHelp(occurrence.symbol_id),meaning=builtinMeaning||syntaxRoleHelp[role]?.[lang()==="zh"?0:1];if(builtinMeaning)token.classList.add("lr-builtin-symbol");if(meaning)attachTokenHelp(token,spelling,meaning,occurrence.symbol_id);
          if(occurrence.symbol_id===state.symbol)token.classList.add("lr-symbol-selected");
          if(state.reference&&occurrence.symbol_id===state.reference.symbol_id&&occurrence.source_id===state.reference.source_id&&occurrence.start_byte===state.reference.start_byte&&occurrence.end_byte===state.reference.end_byte)token.classList.add("lr-reference-selected");
          appendToken(token,occurrence);cursor=occurrence.end;
        }
        appendTrivia(code,content.slice(cursor,lineEnd)||(!line?" ":""));
        lineContent.append(code);code.addEventListener("click",()=>selectLine(owning,lineNumber));
        if(lineIssues.length){const issue=lineIssues[0],note=button("↳ "+sourceIssueLabel(issue),"lr-inline-failure",event=>{event.stopPropagation();selectSourceIssue(issue.id);});note.dataset.issue=issue.id;note.addEventListener("mouseenter",()=>hoverProofTarget(note));note.addEventListener("focus",()=>hoverProofTarget(note));note.addEventListener("pointerleave",leaveProof);lineContent.append(note);}
        const declarations=declarationsAt.get(lineNumber)||[];
        if(declarations.length){const counts=element("span","lr-definition-references");for(const declaration of declarations){const uses=referenceUses(declaration.symbol_id,source.id),name=symbols.get(declaration.symbol_id)?.name||"",label=t("referenceCount").replace("{count}",uses.length);const count=button((declarations.length>1?name+" · ":"")+label,"lr-reference-count",()=>openReferences(declaration.symbol_id,source.id,count));count.dataset.symbol=declaration.symbol_id;count.setAttribute("aria-label",t("referenceFor").replace("{name}",name)+" · "+label);counts.append(count);}lineContent.append(counts);}
        const inferredIds=[...new Set(inferredAt.get(lineNumber)||[])];
        if(inferredIds.length){
          const results=element("span","lr-inline-inferences");results.setAttribute("role","group");results.setAttribute("aria-label",t("inferredFacts"));
          const previews=inferredIds.map(id=>({id,text:factDisplayText(facts.get(id))})),preview=previews.find(value=>!value.text.includes("\n"))||previews[0];
          const toggle=button("","lr-inference-toggle",()=>openInferences(inferredIds,source.id,toggle));toggle.append(element("span","lr-inference-preview","→ "+preview.text));
          if(inferredIds.length>1)toggle.append(element("small","lr-inference-extra",editText("另 "+(inferredIds.length-1)+" 条",(inferredIds.length-1)+" more")));
          toggle.setAttribute("aria-label",t("inferredFacts")+": "+preview.text+(inferredIds.length>1?editText("；另 "+(inferredIds.length-1)+" 条","; "+(inferredIds.length-1)+" more"):""));toggle.title=editText("查看本行的全部推导结果","View all inferred results for this line");
          toggle.dataset.facts=JSON.stringify(inferredIds);toggle.setAttribute("aria-expanded","false");toggle.setAttribute("aria-haspopup","dialog");
          toggle.addEventListener("mouseenter",()=>hoverInferences(toggle));toggle.addEventListener("focus",()=>hoverInferences(toggle));toggle.addEventListener("pointerleave",leaveInferences);
          toggle.addEventListener("keydown",event=>{if((event.key==="ArrowRight"||event.key==="Tab"&&!event.shiftKey)&&inferencePopover?.owner===toggle){event.preventDefault();inferencePopover.transient=false;inferencePopover.node.querySelector("summary")?.focus();}});
          if(inferredIds.includes(state.fact))toggle.classList.add("lr-inferred-selected");else if(inferredIds.some(id=>citations.includes(id)))toggle.classList.add("lr-inferred-premise");
          results.append(toggle);
          lineContent.append(results);
        }
        row.append(lineContent);codePane.append(row);lineStart=lineEnd+1;lineByteStart=lineByteEnd+1;
      }
      const selectedInference=codePane.querySelector(".lr-inferred-selected"),selectedMarker=selectedInference||codePane.querySelector(".lr-reference-selected"),selectedRow=selectedMarker||codePane.querySelector(".lr-selected");if(selectedRow){const rowBounds=selectedRow.getBoundingClientRect(),paneBounds=codePane.getBoundingClientRect();if(rowBounds.bottom>paneBounds.bottom||rowBounds.top<paneBounds.top)codePane.scrollTop+=rowBounds.top-paneBounds.top-codePane.clientHeight/3;if(selectedMarker&&(rowBounds.right>paneBounds.right||rowBounds.left<paneBounds.left))codePane.scrollLeft+=rowBounds.left-paneBounds.left-64;}
    }

    function factButton(id){
      const fact=facts.get(id),node=button("","lr-fact-link"+(factInferences(id).length?" lr-inferred-link":""),()=>selectFact(id));node.append(fact?factFormula(fact):formula(id));
      node.dataset.fact=id;
      if(fact){
        const location=factLocation(fact),source=sources.get(location.sourceId);if(source&&location.line)node.title=sourceTitle(source)+" · "+t("referenceLine").replace("{line}",location.line);
        const show=()=>peekCitation(id),clear=()=>peekCitation(null);node.addEventListener("mouseenter",show);node.addEventListener("focus",show);node.addEventListener("mouseleave",clear);node.addEventListener("blur",clear);
      }
      if(fact?.role==="hypothesis")node.append(element("small",null,t("hypothesis")));if(!fact)node.disabled=true;return node;
    }
    function peekCitation(id){
      if(!codePane)return;const fact=facts.get(id),location=fact&&factLocation(fact);
      for(const row of codePane.querySelectorAll(".lr-code-row"))row.classList.toggle("lr-citation-peek",!!location&&location.sourceId===state.source&&Number(row.dataset.line)===location.line);
      for(const result of codePane.querySelectorAll(".lr-inference-toggle"))result.classList.toggle("lr-citation-peek",!!id&&array(JSON.parse(result.dataset.facts||"[]")).includes(id));
    }

    function renderStatement(){
      const statement=statements.get(state.statement);if(!statement){detailPane.append(element("p","lr-empty-note",t("meaningUnavailable")));return;}
      const parent=statements.get(statement.parent_statement_id);if(parent)detailPane.append(button(t("outerProof"),"lr-math-link",()=>selectStatement(parent.id)));
      const instances=[...statements.values()].filter(value=>(value.source_statement_id||value.id)===(statement.source_statement_id||statement.id));if(instances.length>1){const contexts=element("div","lr-contexts");instances.forEach((instance,index)=>{const pick=button(t("context")+" "+(index+1),"lr-chip",()=>selectStatement(instance.id));pick.setAttribute("aria-pressed",String(instance.id===statement.id));contexts.append(pick);});detailPane.append(contexts);}
      const model=statementEquivalence(statement)||statement.mathematics;
      if(!renderMath(model)){
        const outputs=array(statement.produced_fact_ids).filter(id=>facts.has(id));if(outputs.length)outputs.forEach(id=>detailPane.append(factButton(id)));else detailPane.append(element("p","lr-empty-note",t("meaningUnavailable")));
      }
      if(statement.scope_id&&!String(statement.scope_id).startsWith("file:"))detailPane.append(element("p","lr-empty-note",t("underHypotheses")));
      renderStatus(statement);
      if(!["predicate_definition","predicate_equivalence","objects","binding","function","abstract_predicate"].includes(model?.kind)){
        const citations=array(statement.cited_fact_ids);if(citations.length){section(t("mathGrounds"));citations.forEach(id=>detailPane.append(factButton(id)));}
      }
      definitionLinks(array(statement.declaration_dependencies).filter(id=>id!==statement.id));
    }

    function renderFact(){
      const fact=facts.get(state.fact);if(!fact)return;if(Number.isInteger(state.chainStep)){appendEqualityStep(detailPane,fact,state.chainStep);return;}
      if(["verified","hypothesis"].includes(fact.role)){if(appendPredicateDefinition(detailPane,fact))detailPane.append(element("h4","lr-proof-section-title",editText("证明","Proof")));appendProofBody(detailPane,fact);return;}
      if(factInferences(fact.id).length){renderInferredFact();return;}
      const producer=statements.get(fact.producer_statement_id),model=producer?.mathematics?.subject===fact.text?statementEquivalence(producer):null;
      if(!renderMath(model))detailPane.append(factFormula(fact));
      if(fact.role==="hypothesis")detailPane.append(element("p","lr-empty-note",t("underHypotheses")));else if(fact.scope_id&&!String(fact.scope_id).startsWith("file:"))detailPane.append(element("p","lr-empty-note",t("local")));
      if(producer)renderOrigin(producer);
      const citations=factCitations(fact);if(!model&&citations.length){section(t("mathGrounds"));citations.forEach(id=>detailPane.append(factButton(id)));}
      if(producer)definitionLinks(array(producer.declaration_dependencies));
    }

    function renderInferredFact(){
      const fact=facts.get(state.fact),producer=statements.get(fact.producer_statement_id),batches=factInferences(fact.id),model=batches.map(batch=>batch.mathematics).find(value=>value?.kind==="predicate_equivalence");
      if(!renderMath(model)){detailPane.append(factFormula(fact));const seeds=[...new Set(batches.map(batch=>batch.source_fact_id))];if(seeds.length){section(t("mathGrounds"));seeds.forEach(id=>detailPane.append(factButton(id)));}}
      if(fact.scope_id&&!String(fact.scope_id).startsWith("file:"))detailPane.append(element("p","lr-empty-note",t("underHypotheses")));if(producer)renderOrigin(producer);
      definitionLinks(inferenceOrigins(fact.id).map(origin=>origin.definition_statement_id));
    }

    function renderWellDefinedness(){
      const record=wellDefinedness.get(state.wd);if(!record)return;detailPane.append(formula(record.object),element("p","lr-empty-note",t("wellDefined")));
      const citations=wdCitations(record);if(citations.length){section(t("mathGrounds"));citations.forEach(id=>detailPane.append(factButton(id)));}
      const producer=statements.get(record.producer_statement_id);if(producer)renderOrigin(producer);
    }

    function renderOrigin(statement){
      if(statement.origin&&statement.origin!=="checked")detailPane.append(element("p","lr-origin-note",t(statement.origin)));
      const dependencies=array(statement.trust_dependencies);if(dependencies.length&&statement.origin==="checked"){const notice=element("div","lr-origin-note",t("trustUsed"));for(const id of dependencies){const target=statements.get(id);if(target)notice.append(button(t(target.origin),"lr-chip",()=>selectStatement(id)));}detailPane.append(notice);}
    }

    function definitionSource(id){
      const binding=symbolBindings.get(id),declaration=symbolDefinitions.get(id),source=sources.get(binding?.source_id||declaration?.source_id);
      if(typeof source?.content!=="string")return null;
      const offsets=bytePositions(source.content),local=!!symbolParameters.get(id)&&!(declarationsBySource.get(source.id)||[]).some(value=>value.symbol_id===id),record=local?binding:declaration;
      if(!record)return null;
      const start=offsets.get(record.start_byte),end=offsets.get(record.end_byte);
      if(start===undefined||end===undefined||end<=start)return null;
      const line=source.content.slice(0,start).split("\n").length;
      const code=local?source.content.split("\n")[line-1].trim():source.content.slice(start,end).trimEnd();
      return {location:sourceTitle(source)+" · "+t("referenceLine").replace("{line}",line),code,sourceId:source.id};
    }
    function renderSymbol(){
      const theorem=theoremReference(state.symbol);if(theorem){appendReference(detailPane,theorem);return;}
      const definition=definitionSource(state.symbol);
      if(definition){section(t("definition")+" · "+definition.location);detailPane.append(element("pre","lr-definition-source",definition.code));}
      const parameter=symbolParameters.get(state.symbol);if(parameter)detailPane.append(formula(parameterText(parameter,definition?.sourceId),definition?.sourceId));
      const mentions=occurrences.filter(value=>value.symbol_id===state.symbol),definitions=[...new Set(mentions.filter(value=>value.definition).map(value=>value.statement_id))];
      if(!definitions.length&&symbolDefinitions.has(state.symbol))definitions.push(symbolDefinitions.get(state.symbol).id);
      let shown=false;for(const id of definitions.filter(()=>!parameter||(declarationsBySource.get(definition?.sourceId)||[]).some(value=>value.symbol_id===state.symbol)))shown=renderMath(statements.get(id)?.mathematics,statements.get(id)?.source_id)||shown;
      if(!shown&&!parameter)detailPane.append(element("p","lr-empty-note",t("meaningUnavailable")));
      if(mentions.length){
        const disclosure=element("details","lr-occurrences"),body=element("div"),seen=new Set();
        for(const occurrence of mentions){const key=[occurrence.source_id,occurrence.start_byte,occurrence.end_byte].join("|");if(!seen.has(key)){seen.add(key);occurrenceButton(occurrence,body);}}
        disclosure.append(element("summary",null,t("references")+" · "+seen.size),body);detailPane.append(disclosure);
      }
    }

    function occurrenceButton(occurrence,target=detailPane){
      const source=sources.get(occurrence.source_id);if(!source)return;
      const statement=statements.get(occurrence.statement_id),location=occurrenceLocation(occurrence);
      const node=button("","lr-fact-link lr-occurrence-link",()=>navigate({source:occurrence.source_id,statement:occurrence.statement_id,symbol:null,fact:null,wd:null,focusLine:location?.line||statement?.line,reference:occurrence}));
      // Occurrences describe authored source, not execution-resolved subjects.
      // Keep explicit qualifications as written; never strip internal-looking names.
      const snippet=element("code");if(location)snippet.append(document.createTextNode(location.before.trimStart()),element("mark",null,location.token),document.createTextNode(location.after));
      else snippet.textContent=symbols.get(occurrence.symbol_id)?.name||t("unavailable");
      node.append(snippet,element("small",null,[sourceTitle(source),location?t("referenceLine").replace("{line}",location.line):null].filter(Boolean).join(" · ")));target.append(node);
    }

    function evidenceNode(value,title){
      value=resolveEvidence(value);
      if(value===null||value===undefined)return element("span","lr-empty-note","—");
      if(typeof value!=="object")return element("span","lr-evidence-subject",String(value));
      if(value.kind==="fact_reference")return factButton(value.fact_id);
      if(value.kind==="fact_identity")return element("span","lr-empty-note",value.fact_id);
      if(value.kind==="well_definedness_reference"||value.kind==="well_definedness_identity"){const record=wellDefinedness.get(value.id);const link=button(t("wellDefined")+" · "+(record?.object||value.id),"lr-fact-link",()=>selectWellDefinedness(value.id));link.disabled=!record;return link;}
      if(value.kind==="statement_reference"){const target=statements.get(value.statement_id);return button((target?.text||value.statement_id)+" · "+t("sourceLine")+" "+(target?.line||""),"lr-fact-link",()=>selectStatement(value.statement_id));}
      if(value.kind==="declaration_reference"){const target=statements.get(value.statement_id);const link=button((target?.text||t("definition"))+" · "+t("sourceLine")+" "+value.line,"lr-fact-link",()=>selectStatement(value.statement_id));link.disabled=!target;return link;}
      if(value.kind==="symbol_reference")return button(value.name||value.symbol_id,"lr-chip lr-concept-chip",()=>selectSymbol(value.symbol_id));
      if(value.kind==="scope")return element("span","lr-empty-note",t("local"));
      if(value.kind==="unavailable")return element("span","lr-empty-note",t("unavailable"));
      const details=element("details","lr-evidence");
      const route=routeNames[value.variant]?.[lang()==="zh"?1:0];
      const summary=element("summary",null,value.rule_id?ruleTitle(value.rule_id):(route||title||humanize(value.variant)||t("proof")));details.append(summary);
      details.addEventListener("toggle",()=>{
        if(!details.open||details.childElementCount>1)return;
        const body=element("div");if(value.text)body.append(element("code","lr-evidence-subject",value.text));
        if(value.rule_id){body.append(button(t("rulebook")+" ↗","lr-chip",()=>showRule(value.rule_id)));const message=ruleMessage(value.rule_id);if(message)body.append(element("p","lr-empty-note",message));}
        const entries=Array.isArray(value)?value.map((item,index)=>[String(index+1),item]):Object.entries(value.fields||value).filter(([key])=>!["text","type","variant","rule_id"].includes(key));
        for(const [key,item] of entries){if(item===null||(Array.isArray(item)&&!item.length))continue;body.append(element("div","lr-evidence-label",label(key)),evidenceNode(item,label(key)));}details.append(body);
      });
      return details;
    }

    function renderRulebook(){
      rulebook=element("details","lr-rulebook");rulebook.open=rulebookState.open;rulebook.addEventListener("toggle",()=>{rulebookState.open=rulebook.open;});rulebook.append(element("summary",null,t("rulebook")));
      const tools=element("div","lr-rulebook-tools");ruleSearch=element("input");ruleSearch.type="search";ruleSearch.placeholder=t("search");ruleSearch.setAttribute("aria-label",t("search"));
      ruleSearch.value=rulebookState.query;const usedLabel=element("label");usedOnly=element("input");usedOnly.type="checkbox";usedOnly.checked=rulebookState.usedOnly;usedLabel.append(usedOnly,document.createTextNode(" "+t("usedOnly")));tools.append(ruleSearch,usedLabel);rulebook.append(tools);
      const categories=element("select");categories.setAttribute("aria-label",t("category"));for(const category of ["all",...new Set([...rules.values()].map(rule=>rule.category).filter(Boolean))]){const option=element("option",null,category==="all"?t("allCategories"):t(category));option.value=category;option.selected=category===rulebookState.category;categories.append(option);}tools.insertBefore(categories,usedLabel);categories.addEventListener("change",()=>{rulebookState.category=categories.value;rulePage=0;renderRules();});
      ruleGrid=element("div","lr-rule-grid");paging=element("div","lr-rule-paging");rulebook.append(ruleGrid,paging);root.append(rulebook);
      ruleSearch.addEventListener("input",()=>{rulebookState.query=ruleSearch.value;rulePage=0;renderRules();});usedOnly.addEventListener("change",()=>{rulebookState.usedOnly=usedOnly.checked;rulePage=0;renderRules();});renderRules();
    }
    function renderRules(){
      const query=ruleSearch.value.trim().toLowerCase();const list=[...rules.values()].filter(rule=>(!usedOnly.checked||usedRules.has(rule.id))&&(rulebookState.category==="all"||rule.category===rulebookState.category)&&[rule.id,ruleTitle(rule.id),rule.variant,ruleMessage(rule.id)].join(" ").toLowerCase().includes(query));
      const pageSize=18;const pages=Math.max(1,Math.ceil(list.length/pageSize));rulePage=Math.min(rulePage,pages-1);ruleGrid.replaceChildren();paging.replaceChildren();
      for(const rule of list.slice(rulePage*pageSize,(rulePage+1)*pageSize)){
        const card=element("article","lr-rule-card"+(rule.id===activeRule?" lr-active-rule":""));card.dataset.rule=rule.id;card.append(element("h3",null,ruleTitle(rule.id)),element("p",null,ruleMessage(rule.id)||t("catalogueOnly")));
        for(const id of usedRules.get(rule.id)||[]){const statement=statements.get(id);card.append(button(t("sourceLine")+" "+statement.line,"lr-chip",()=>selectStatement(id)));}ruleGrid.append(card);
      }
      const previous=button("← "+t("previous"),"lr-button",()=>{rulePage--;renderRules();});previous.disabled=rulePage===0;
      const next=button(t("next")+" →","lr-button",()=>{rulePage++;renderRules();});next.disabled=rulePage+1>=pages;paging.append(previous,element("span",null,(rulePage+1)+" / "+pages+" · "+list.length),next);
    }
    function showRule(id){activeRule=id;rulebookState={query:id,usedOnly:false,open:true,category:"all"};rulebook.open=true;ruleSearch.value=id;usedOnly.checked=false;rulebook.querySelector("select").value="all";rulePage=0;renderRules();rulebook.scrollIntoView({block:"nearest",behavior:"smooth"});}

    const dismissPanels=event=>{if(proofPopover&&!proofPopover.node.contains(event.target))closeProof();const explanation=root.querySelector(".lr-context-explanation");if(explanation&&!explanation.hidden&&!explanation.contains(event.target)&&!codePane?.contains(event.target)&&!event.target.closest?.(".lr-ide-input"))closeExplanation();if(inferencePopover&&!inferencePopover.node.contains(event.target)&&!inferencePopover.owner.contains(event.target))closeInferences();const records=root.querySelector(".lr-records");if(records?.open&&!records.contains(event.target))records.open=false;const menu=root.querySelector(".lr-book-nav");if(menu?.open&&!menu.contains(event.target))menu.open=false;};
    const dismissInferences=event=>{if(event.key==="Escape"){closeProof(!!proofPopover?.node.contains(document.activeElement));closeExplanation(true);}if(event.key==="Escape"&&inferencePopover){event.preventDefault();event.stopPropagation();closeInferences(true);}};
    document.addEventListener("pointerdown",dismissPanels);
    root.addEventListener("keydown",dismissInferences);
    window.addEventListener("scroll",positionOverlays,true);
    window.addEventListener("resize",positionOverlays);
    index();render();
    const api = {
      update(document,settings={}){if(destroyed)return;checkSerial++;checking=false;if(!settings.preserveDrafts){drafts.clear();originals.clear();revision=0;checkedRevision=0;idePositions.clear();editError="";}if(document.kind==="reading_manifest")throw new Error("Use LitexReading.open for a manifest");generation++;navigationSerial++;bookSerial++;loader=null;allOccurrencesLoaded=true;bookIndex=null;bookQuery="";bookOpen=null;operationStatus="";bundle=document;history=[];state={source:null,statement:null,symbol:null,fact:null,wd:null,focusLine:null};activeRule=null;rulePage=0;rulebookState={query:"",usedOnly:true,open:false,category:"all"};index();render();if(options.onNavigate)options.onNavigate({...state},{bundle_id:bundle.bundle_id||null});},
      setLanguage(value){if(destroyed)return;locale=value;render();},
      selectStatement(id){return !pending()&&statements.has(id)?selectStatement(id):false;},
      selectFact(id){return facts.has(id)?selectFact(id):false;},
      selectWellDefinedness(id){return wellDefinedness.has(id)?selectWellDefinedness(id):false;},
      getSelection(){return {...state};},
      getBundleId(){return bundle.bundle_id||null;},
      hasLocalEdits(){return [...drafts].some(([path,content])=>content!==originals.get(path));},
      async getProjectSnapshot(){
        if(destroyed)throw new Error(editText("阅读器已关闭。","The reader is closed."));
        const snapshotSources=[],epoch=generation,configuration=bundle.configurations||[],strict=bundle.execution_policy?.strict===true;
        for(const source of [...sources.values()]){
          if(typeof source.content==="string")snapshotSources.push({...source});
          else{
            let content;
            if(loader?.loadSourceText)content=await loader.loadSourceText(source.id);
            else if(loader){const chunk=await loader.loadSource(source.id);content=chunk.sources.find(item=>item.id===source.id)?.content;}
            if(destroyed||epoch!==generation)throw new Error(editText("准备源码时打开的文档已改变，请重新检查。","The opened document changed while preparing its source. Check again."));
            if(typeof content!=="string")throw new Error(editText("源码暂不可用。","Source text is unavailable."));
            snapshotSources.push({...source,content});
          }
        }
        return {sources:snapshotSources,configurations:configuration,strict};
      },
      destroy(){checkSerial++;checking=false;closeInferences();hideTokenHelp();closeProof();window.removeEventListener("scroll",positionOverlays,true);window.removeEventListener("resize",positionOverlays);destroyed=true;generation++;navigationSerial++;bookSerial++;document.removeEventListener("pointerdown",dismissPanels);root.removeEventListener("keydown",dismissInferences);root.replaceChildren();}
    };
    return api;
  }
  function mergeReadingChunk(bundle,part){
    for(const key of ["sources","statements","facts","inferences","well_definedness","evidence_nodes","occurrences"]){
      if(!Array.isArray(part[key]))continue;
      const identity=value=>key==="occurrences"?[value.source_id,value.start_byte,value.end_byte,value.symbol_id,value.statement_id,value.definition].join("|"):value.id;
      const records=new Map(array(bundle[key]).map(value=>[identity(value),value]));
      for(const value of part[key]){const id=identity(value),existing=records.get(id);if(key==="evidence_nodes"&&existing&&JSON.stringify(existing.node)!==JSON.stringify(value.node))throw new Error("Conflicting reading evidence: "+id);records.set(id,{...existing,...value});}
      bundle[key]=[...records.values()];
    }
  }

  async function openReadingReader(root,source,options){
    options=options||{};
    const base=new URL(typeof source==="string"?source:options.baseUrl||location.href,document.baseURI);
    const fetchJSON=async(url,cache="default")=>{const response=await fetch(url,{cache});if(!response.ok)throw new Error("Reading HTTP "+response.status);return response.json();};
    const manifest=typeof source==="string"?await fetchJSON(base.href,"no-store"):source;
    if(manifest?.kind==="reading")return mountReadingReader(root,{...options,document:manifest});
    if(manifest?.kind!=="reading_manifest"||!["1","2"].includes(manifest.schema_version)||typeof manifest.manifest_id!=="string")throw new Error("Unsupported reading manifest");
    const localURL=path=>{const url=new URL(path,base);if(url.origin!==base.origin)throw new Error("Reading parts must share the manifest origin");return url.href;};
    const part=async(path,kind)=>{const value=await fetchJSON(localURL(path));if(value.kind!==kind||value.manifest_id!==manifest.manifest_id)throw new Error((options.locale||manifest.language||"").startsWith("zh")?copy.zh.changedBuild:copy.en.changedBuild);return value;};
    const sources=new Map(array(manifest.sources).map(value=>[value.id,value]));
    const pending=new Map(),sourcePending=new Map();let occurrencePromise,searchPromise;
    const loader={
      loadSource(id){if(!pending.has(id)){const source=sources.get(id);if(!source)throw new Error("Unknown reading source");pending.set(id,part(source.chunk_url,"reading_chunk").then(value=>{if(value.source_id!==id||value.sources?.length!==1||value.sources[0].id!==id)throw new Error("Mismatched reading source");return value;}).catch(error=>{pending.delete(id);throw error;}));}return pending.get(id);},
      loadSourceText(id){
        if(!sourcePending.has(id)){
          const source=sources.get(id);if(!source)throw new Error("Unknown reading source");
          if(source.source_url!==undefined&&(typeof source.source_url!=="string"||!source.source_url))throw new Error("Invalid reading source URL");
          const request=source.source_url?part(source.source_url,"reading_source").then(value=>value.source):loader.loadSource(id).then(value=>value.sources?.[0]);
          sourcePending.set(id,request.then(value=>{if(value?.id!==id||value.path!==source.path||typeof value.content!=="string")throw new Error("Mismatched reading source text");return value.content;}).catch(error=>{sourcePending.delete(id);throw error;}));
        }
        return sourcePending.get(id);
      },
      loadOccurrences(){return occurrencePromise||(occurrencePromise=part(manifest.occurrences_url,"reading_occurrences").catch(error=>{occurrencePromise=null;throw error;}));},
      loadSearch(){return searchPromise||(searchPromise=part(manifest.search_url,"reading_search").catch(error=>{searchPromise=null;throw error;}));},
      downloadUrl:localURL(manifest.full_document_url)
    };
    const bundle={...manifest,kind:"reading",sources:array(manifest.sources).map(value=>({...value})),evidence_nodes:[],occurrences:[]};
    const first=sources.has(manifest.entry_source_id)?manifest.entry_source_id:sources.keys().next().value;
    if(first){root.replaceChildren(element("p","lr-loading",(options.locale||manifest.language||"").startsWith("zh")?copy.zh.loading:copy.en.loading));mergeReadingChunk(bundle,await loader.loadSource(first));}
    return mountReadingReader(root,{...options,document:bundle,loader});
  }

  global.LitexReading=Object.freeze({mount:mountReadingReader,open:openReadingReader,schemaVersion:"2",supportedSchemaVersions:Object.freeze(["1","2"])});
})(window);
