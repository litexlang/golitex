# Litex Math23K 中文代表集 / Chinese Representative Set

## 中文

这是一个刻意保持很小的 Math23K 中文交付集，共 30 道代表题。它适合展示、快速回归测试和 Litex 示例，不追求刷完 2.3 万道高度重复的小学应用题。

### 文件

| 文件 | 数量 | 用途 |
| --- | ---: | --- |
| `data/math23k.jsonl` | 30 | 唯一的数据文件 |
| `LICENSE.md` | — | 中文许可说明 |
| `APACHE-2.0.txt` | — | Litex 形式化代码与本项目内容的许可证原文 |
| `MATH23K-MIT.txt` | — | 中文原题来源仓库的许可证原文 |

每行只有四个必要字段：

- `编号`：稳定的 Math23K 派生编号；
- `题目`：按编号对应的原始中文题目；
- `解题思路`：由原始标注方程和答案写成的简短中文计算思路；
- `形式化代码`：完整 Litex 源码。Litex 关键字属于语言语法，定理名、变量名和注释均已中文化。

中文原题来自 [SCNU203/Math23k](https://github.com/SCNU203/Math23k) 的提交 `b1135a5dddc77bcc30b4e8b021b25c68d6e15dea`，并按原始 `id` 与本项目的 `Math23k_<id>` 精确对应。该来源仓库声明采用 MIT 许可证；本项目不对更早来源网站材料的权利归属另作保证。

这里的 Litex 代码是根据 Math23K 标注方程构造的可检查计算模型，不等于对题目全部自然语言语义的完整形式化。代表集也不用于报告全量 Math23K 准确率。

## English

This is an intentionally small Chinese Math23K delivery set containing 30 representative problems. It is intended for demos, fast regression checks, and Litex examples—not for exhaustively processing 23,000 highly repetitive elementary-school word problems.

### Files

| File | Rows | Purpose |
| --- | ---: | --- |
| `data/math23k.jsonl` | 30 | The only data file |
| `LICENSE.md` | — | Chinese licensing explanation |
| `APACHE-2.0.txt` | — | Original license text for the Litex artifacts and project-authored material |
| `MATH23K-MIT.txt` | — | Original license text from the Chinese-question source repository |

Each JSONL row contains exactly four necessary fields:

- `编号`: stable Math23K-derived identifier;
- `题目`: original Chinese problem matched by identifier;
- `解题思路`: short Chinese calculation plan based on the annotated equation and answer; and
- `形式化代码`: complete Litex source. Litex keywords remain language syntax, while theorem names, variable names, and comments are in Chinese.

The Chinese questions come from commit `b1135a5dddc77bcc30b4e8b021b25c68d6e15dea` of [SCNU203/Math23k](https://github.com/SCNU203/Math23k), whose records were matched exactly from source `id` to this package's `Math23k_<id>`. That source repository declares the MIT License; this project makes no separate representation about rights in material from earlier source websites.

The Litex artifacts are checkable calculation models derived from Math23K annotated equations; they are not complete formalizations of every natural-language semantic detail. This representative set must not be used to report full-corpus Math23K accuracy.
