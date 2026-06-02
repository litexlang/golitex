# How to Contribute to Litex

Jiachen Shen and The Litex Team, 2026-06-02. Email: litexlang@outlook.com

Markdown source: https://github.com/litexlang/golitex/blob/main/docs/How_To_Contribute.md

Litex is still experimental. The most useful early contributions are not only
kernel patches or large theorem proofs. The project needs mathematically
curious readers to try real proof-writing tasks, report where the feedback loop
breaks, and turn those breaks into small examples, translations, and blockers.

This guide is for a specific contributor profile:

- You know undergraduate mathematics, such as calculus, linear algebra,
  discrete mathematics, elementary number theory, or introductory analysis.
- You have read the first few chapters of The Mechanics of Litex Proof, or you
  are willing to read them while trying small examples.
- You do not yet know the Litex kernel, parser, verifier, or standard library.
- You want a useful first contribution before committing to deeper work.

## What Litex Needs

Litex is being developed through a pressure-test loop: translate real
mathematics, run the verifier, and use failures to discover missing language,
standard-library, inference, automation, and diagnostic support.

Good first contributions therefore look like this:

- read a short document section and report exactly where it becomes confusing;
- run a small example and explain where the output is helpful or confusing;
- reduce a confusing failure into a minimal runnable example;
- later, translate a small problem into a natural Litex statement;
- list missing theorem statements for a small mathematical topic.

The goal is not to prove a famous theorem on day one. The goal is to produce
clear evidence about what a mathematically trained new reader can understand,
where the documentation loses them, and what still blocks ordinary mathematical
work.

## Contribution Priorities

If you are not sure what to pick, start with a `P0` task. These tasks are the
lowest-friction way to help: read, run, and report where Litex is confusing.
Textbook and problem translation is valuable, but it is harder and appears
later in this list.

### P0: Highest Priority

These are the most useful first contributions.

#### Documentation Confusion Reports

Read a small part of the documentation and report concrete confusion. Especially
useful targets are the first chapters of The Mechanics of Litex Proof, the
README, the Manual, and any page that feels duplicated or outdated.

Good reports include:

- the first sentence or example that was unclear;
- a concept that appeared before it was explained;
- two pages that seem to say the same thing differently;
- a code block that was hard to modify;
- an output message that did not explain the next step.

This is high priority because Litex has many documents, and the project needs
fresh-reader feedback from people who know mathematics but are still new to
Litex.

#### Example Runner Pass

Pick a small examples folder, run its `.lit` files, and report:

- which examples pass;
- which examples are slow or noisy;
- which successful verifier outputs are hard to understand;
- which comments or names are misleading;
- one suggested documentation or example improvement.

This is high priority because it does not require proving new mathematics. It
only requires careful reading and honest reporting from a new user's point of
view.

#### Documentation Map and Cleanup

Review a small part of the documentation tree and report:

- which page a new reader should read first;
- which pages overlap;
- which links are missing;
- which concepts are named inconsistently;
- which claims appear outdated.

Do not start with broad rewrites. The most useful first version is a short,
specific map of where the documentation is confusing.

### P1: High Priority

These tasks are useful once you have read a few documents or run a few examples.

#### Minimal Blocker Reproductions

If a proof step feels mathematically obvious but Litex cannot verify it, reduce
the problem. A good blocker reproduction is usually 10-30 lines.

Include:

- what you expected Litex to verify;
- what Litex actually reported;
- the smallest context needed to reproduce the issue;
- the blocker label you think fits best.

Minimal blockers are often more useful than large unfinished proofs because
they give kernel and stdlib contributors a precise target.

Useful blocker labels are:

- `blocked_by_language`
- `blocked_by_stdlib`
- `blocked_by_infer_rule`
- `blocked_by_kernel`
- `blocked_by_syntax`
- `blocked_by_diagnostics`
- `blocked_by_formulation`

#### Diagnostics and Output Review

Collect examples where Litex's output is technically correct but hard to use.
Good reports identify:

- a successful `verified_by` explanation that is too vague;
- an `unknown` result that gives no next step;
- an error that points at the wrong concept or line;
- output that makes `know` look more proved than it is;
- repeated output that hides the important reason.

This is high priority because Litex depends on a tight verifier feedback loop.
If readers cannot understand why a line succeeded or failed, they cannot repair
proofs efficiently.

#### Small Checkable Examples

Turn one theorem, feature, or proof pattern into a small runnable `.lit` file.
Good examples are usually 10-30 lines and show one idea clearly.

Useful topics include:

- rational density in `Real`;
- basic function equality;
- finite set counting;
- simple use of `by thm`;
- simple use of `by axiom_of_choice`;
- a short set or order argument.

### P2: Medium Priority

These tasks are valuable, but they are harder than first-pass documentation
feedback and are better after you have tried the feedback loop.

#### Textbook and Problem Translation

Translate small slices of real mathematical material. Good sources include:

- high-school textbooks and exercises;
- undergraduate textbooks;
- contest problems;
- high-school algebra and inequalities;
- simple MATH500 items;
- low-dependency miniF2F-style problems;
- selected Tao Analysis, Weil number theory, or Mechanics exercises.

For each translated item, submit:

- the natural-language proof idea;
- a natural Litex statement;
- the best proof attempt you can write;
- a status: `checkable`, `translated`, or `blocked`;
- if blocked, one primary blocker label.

This is important because real translations reveal whether Litex can express
ordinary mathematics naturally. It is not the easiest first task, so new
contributors should usually try documentation feedback first.

#### Standard-Library Gap Inventory

Pick one small topic and list theorem statements Litex should eventually have.
Good topics include:

- basic real sequence facts;
- elementary set operations;
- finite sets and counting;
- integer divisibility;
- rational approximation;
- function equality;
- order and inequalities.

For this task, a theorem statement can be useful even without a proof. The
important part is that the statement is natural Litex, consistently named, and
motivated by examples or translation work.

### P3: Ongoing Maintenance

These tasks are useful, but they are best paired with a concrete translation or
documentation effort.

#### Translation Status Bookkeeping

For a source folder or dataset slice, keep a local status list:

- how many items are translated;
- how many are checkable;
- how many are blocked;
- the main blocker labels;
- which blockers were later fixed.

This helps the project track whether a source is becoming more checkable over
time.

#### Typos, Links, and Small Polish

Small cleanup is welcome when it is obviously correct. Prefer edits that remove
confusion or support a real example. Avoid broad style rewrites unless a page is
already being reorganized.

## What Not to Start With

Avoid these tasks until you have more local context:

- changing the Rust verifier or parser;
- adding builtin rules;
- changing soundness-critical storage or inference logic;
- rewriting standard-library organization;
- attempting long Tao Analysis proofs without first isolating the blockers;
- hiding hard proof gaps by adding broad `know` facts without explanation.

These tasks are important, but they require a clearer picture of the current
trusted base and verification model.

## First Contribution Shape

A strong first contribution can be small. For example:

- one `P0` documentation confusion report with five concrete points;
- one examples-folder report tied to a specific confusion or output issue;
- one minimal blocker reproduction from a failed proof step;
- ten proposed theorem statements for a focused standard-library topic;
- later, three translated textbook or contest problems, with one fully
  checkable proof.

When a proof is unfinished, say so directly. A clear blocked result is useful if
it records the mathematical idea, the attempted Litex shape, the exact failure,
and the likely missing support.

## Definition of Done

For a first contribution, aim for one of these outcomes:

- `checkable`: the `.lit` file runs successfully;
- `translated`: the mathematical statement is naturally expressed, but proof
  work remains;
- `blocked`: the failure reason is understood and recorded with a minimal
  reproduction or a concise note.

Do not treat `blocked` as failure. In this stage of Litex, well-labeled
blockers are part of the development process.

## A Useful First Week

1. Read Mechanics chapters 1-3 with a notebook open.
2. Run a few examples locally.
3. Write down five concrete documentation confusion points.
4. Modify one example and observe the verifier output.
5. Turn the first serious failure into a minimal blocker reproduction.
6. If you still have time, translate one very small problem.

That path teaches the Litex proof style and gives the project actionable data.

---

# Litex 贡献指南

Jiachen Shen and The Litex Team, 2026-06-02. Email: litexlang@outlook.com

Markdown source: https://github.com/litexlang/golitex/blob/main/docs/How_To_Contribute.md

Litex 还处在实验阶段。现在最有价值的早期贡献，不只是 kernel patch
或者大型定理证明。项目需要懂数学、愿意动手的读者，去尝试真实的证明
写作任务，报告反馈循环在哪里断掉，并把这些问题整理成小例子、翻译尝试
和 blocker。

这份指南面向一种具体的贡献者画像：

- 你懂本科数学，比如微积分、线性代数、离散数学、初等数论或初等分析。
- 你已经读过 The Mechanics of Litex Proof 的前几章，或者愿意一边读一边
  尝试小例子。
- 你还不熟悉 Litex 的 kernel、parser、verifier 或标准库。
- 你想先做一个有用的小贡献，再决定是否深入参与。

## Litex 现在需要什么

Litex 当前的开发方式是一种压力测试循环：翻译真实数学，运行 verifier，
再用失败结果发现语言、标准库、推理规则、自动化和诊断信息的缺口。

好的第一类贡献通常长这样：

- 读一小段文档，并准确报告从哪里开始困惑；
- 跑一个小例子，并说明输出哪里有帮助、哪里让人困惑；
- 把一个 confusing failure 压缩成最小可运行例子；
- 之后再把一个小数学题翻译成自然的 Litex statement；
- 为一个小数学主题整理缺失的 theorem statement。

第一天的目标不是证明一个著名定理。目标是产出清晰证据：哪些地方能被一个
懂数学的新读者理解，文档又在哪里让他们掉队，以及普通数学工作流在哪里被
卡住。

## 贡献任务优先级

如果你不知道该选什么任务，先选 `P0`。这些任务门槛最低，也最直接有用：
阅读、运行，然后报告 Litex 在哪里让人困惑。教材和题库翻译仍然很有价值，
但难度更高，所以放在后面。

### P0：最高优先级

这些是最有用的第一批贡献。

#### 文档困惑报告

阅读一小段文档，并报告具体困惑。特别有用的目标包括 The Mechanics of
Litex Proof 的前几章、README、Manual，以及任何你觉得重复、冲突或过时
的页面。

好的报告包括：

- 第一句让你困惑的话或第一个不清楚的例子；
- 某个概念在解释之前就突然出现；
- 两个页面好像在用不同方式说同一件事；
- 某个 code block 很难修改或尝试；
- 某个输出信息没有说明下一步该怎么做。

这是最高优先级，因为 Litex 的文档已经很多，而项目需要来自新读者的真实
反馈：这些读者懂数学，但还没有被 Litex 的内部习惯训练过。

#### Example 运行报告

选择一个小 examples 文件夹，运行其中的 `.lit` 文件，并报告：

- 哪些例子通过；
- 哪些例子很慢或输出噪声很大；
- 哪些成功输出仍然难懂；
- 哪些注释或命名具有误导性；
- 一个文档或例子改进建议。

这是最高优先级，因为它不要求证明新数学，只要求从新用户视角认真阅读和
诚实报告。

#### 文档地图和清理

检查文档树的一小部分，并报告：

- 新读者应该先读哪一页；
- 哪些页面内容重叠；
- 哪些链接缺失；
- 哪些概念命名不一致；
- 哪些说法看起来过时。

不要一开始就大范围重写。最有用的第一版，是一个短而具体的“文档哪里让人
困惑”的地图。

### P1：高优先级

这些任务适合已经读过几份文档，或者已经跑过几个例子的人。

#### 最小 blocker 复现

如果某个证明步骤在数学上显然成立，但 Litex 不能验证，请把问题压缩。
一个好的 blocker reproduction 通常只有 10-30 行。

请包含：

- 你期望 Litex 验证什么；
- Litex 实际报告了什么；
- 复现问题所需的最小上下文；
- 你认为最合适的 blocker label。

最小 blocker 往往比大型未完成证明更有用，因为它给 kernel 和 stdlib
贡献者一个清晰目标。

常用 blocker labels：

- `blocked_by_language`
- `blocked_by_stdlib`
- `blocked_by_infer_rule`
- `blocked_by_kernel`
- `blocked_by_syntax`
- `blocked_by_diagnostics`
- `blocked_by_formulation`

#### 诊断信息和输出评审

收集那些“技术上正确，但对用户不够有用”的 Litex 输出。好的报告会指出：

- 某个成功的 `verified_by` 解释太模糊；
- 某个 `unknown` 没有给出下一步线索；
- 某个 error 指向了错误的概念或行；
- 某段输出让 `know` 看起来像是真的被证明了；
- 重复输出遮住了真正重要的原因。

这是高优先级，因为 Litex 依赖一个紧密的 verifier feedback loop。如果读者
看不懂一行为什么成功或失败，他们就无法高效修复证明。

#### 小型可检查例子

把一个 theorem、feature 或 proof pattern 写成一个小型可运行 `.lit` 文件。
好的例子通常只有 10-30 行，并且只清楚展示一个想法。

有用主题包括：

- `Real` 里的有理数稠密性；
- 基本函数相等；
- 有限集计数；
- `by thm` 的简单用法；
- `by axiom_of_choice` 的简单用法；
- 一个短的集合或序关系论证。

### P2：中优先级

这些任务很有价值，但比第一轮文档反馈更难，适合已经尝试过反馈循环之后再做。

#### 教科书和题库翻译

翻译真实数学材料的小切片。合适的来源包括：

- 高中教材和习题；
- 大学本科教材；
- 竞赛题；
- 高中代数和不等式；
- 简单的 MATH500 题目；
- 低依赖的 miniF2F-style 问题；
- Tao Analysis、Weil number theory 或 Mechanics 里的精选练习。

每个翻译条目应提交：

- 自然语言证明思路；
- 一个自然的 Litex statement；
- 你能写出的最好 proof attempt；
- 状态：`checkable`、`translated` 或 `blocked`；
- 如果 blocked，标一个主要 blocker label。

这很重要，因为真实翻译会直接暴露 Litex 是否能自然表达普通数学。但它不是
最容易的第一任务，所以新贡献者通常应该先做文档反馈。

#### 标准库缺口清单

选择一个小主题，列出 Litex 最终应该拥有的 theorem statements。合适主题
包括：

- 基本实数列事实；
- 初等集合运算；
- 有限集和计数；
- 整数整除；
- 有理数逼近；
- 函数相等；
- 序关系和不等式。

这个任务里，theorem statement 即使还没有 proof 也有价值。重点是 statement
要符合 Litex 风格，命名一致，并且来自真实例子或翻译需求。

### P3：持续维护

这些任务有用，但最好和某个具体翻译或文档工作搭配。

#### 翻译状态 bookkeeping

为某个 source folder 或 dataset slice 维护本地状态列表：

- 已翻译多少条；
- 多少条是 checkable；
- 多少条 blocked；
- 主要 blocker labels 是什么；
- 哪些 blocker 后来被修掉了。

这能帮助项目跟踪某个 source 是否随着时间变得更可检查。

#### Typo、链接和小 polish

明显正确的小清理是欢迎的。优先做能减少困惑、支持真实例子的修改。除非某个
页面已经需要重组，否则避免大范围风格重写。

## 不建议一开始做什么

在你有更多本地上下文之前，先避免这些任务：

- 修改 Rust verifier 或 parser；
- 添加 builtin rules；
- 修改 soundness-critical 的 storage 或 inference 逻辑；
- 重写标准库组织；
- 在还没有隔离 blocker 之前，直接尝试 Tao Analysis 的长证明；
- 用很宽泛的 `know` facts 隐藏困难证明缺口，而且不解释原因。

这些任务都很重要，但它们需要你先理解当前 trusted base 和 verification model。

## 第一份贡献可以长什么样

一份强的第一贡献可以很小。例如：

- 一份 `P0` 文档困惑报告，包含五个具体困惑点；
- 一份 examples-folder report，和某个具体困惑或输出问题绑定；
- 一个失败证明步骤的最小 blocker reproduction；
- 某个聚焦标准库主题的十个 theorem statements；
- 之后再做三个教材或竞赛题翻译，其中一个 proof fully checkable。

如果 proof 没有完成，请直接说明。一个清楚的 blocked result 是有价值的，
前提是它记录了数学思路、尝试过的 Litex 形状、精确失败信息，以及可能缺失
的支持。

## 完成标准

第一份贡献可以追求以下三种结果之一：

- `checkable`：`.lit` 文件可以成功运行；
- `translated`：数学 statement 已经自然表达，但 proof 还需要继续工作；
- `blocked`：失败原因已经理解，并用最小复现或简短说明记录下来。

不要把 `blocked` 当成失败。在 Litex 当前阶段，标注清楚的 blocker 本身就是
开发流程的一部分。

## 一个有用的第一周

1. 读 Mechanics 第 1-3 章，并打开笔记。
2. 本地运行几个 examples。
3. 写下五个具体的文档困惑点。
4. 修改一个 example，观察 verifier 输出。
5. 把第一个真正卡住的问题压缩成最小 blocker reproduction。
6. 如果还有时间，再翻译一个非常小的问题。

这条路线能让你学到 Litex 的证明风格，同时给项目留下可操作的数据。
