<a id="codesource"></a>

# CodeSource

`CodeSource` 用一个值同时承载代码路径与发布身份。`Runtime.current_file` 是新输入的权威来源。token 块、AST 的 `SourceLine.origin`、解析错误和文件环境快照都使用同一类型。AST 位置从自己的 token 块复制来源，而不再读取第二个实时来源参数。

整合之前，打开一个导出需要两次相互独立的更新：

```rust
// runtime.set_code_source(CodeSource::RootExport { export_file_id });
// runtime.begin_source(RealOrVirtualPath::Real(path));
```

当前接口用一个来源值打开它：

```rust
runtime.begin_source(CodeSource::RootExport { path, export_file_id });
```

`Eval`、`Repl` 和 `Real(PathBuf)` 让文件根符号保持无限定形式。`RootExport` 增加导出文件 ID；`ImportedExport` 同时增加全局模块 ID 和导出文件 ID。两种导出变体也都携带错误报告所用的真实路径。文件运行器从来源中取得路径和模块上下文，而不再把它们作为额外参数接收。

续接的 `-session` 会把 `runtime.current_file` 改为 `CodeSource::Repl`，但不会打开新环境，也不会清除已接受的绑定。新 token 块、AST 位置和错误引用 `<repl>`。先前解析的位置与文件环境的入口快照保留原来的来源。语句软失败仍会保留此前成功的语句。

CLI 回归检查从一个包含以下内容的独立文件开始：

```litex
have k N
k >= 0
```

随后在同一个会话中依次输入 `k >= 0`、会被拒绝的 `1 = 2`，再输入 `k >= 0`。两次引用 `k` 都成功，错误的等式仍被拒绝。格式错误的交互输入分别在独立文件会话、已注册文件会话和额外文件会话中检查：它报告 `<repl>`，而最终批量输出封装保留原始文件路径和结果。

验证时发现的边界：包含 `have k N` 的已注册导出，在续接 REPL 中检查 `k >= 0` 可能失败。已存储的符号出现带有导出限定，而新的 REPL 符号出现没有限定。本次重构中，两种来源变体都保留了这些既有的限定规则。尚未解决的符号身份转换记录在 `src/runtime/todo.md`；来源整合并不能证明导出绑定可作为无限定的 REPL 事实复用。

知识库 ABI 9 将来源路径及其 ID 一同序列化。旧缓存会回退到源码构建。热导入会同时重映射来源模块 ID 与符号引用，并使用当前配置的导出路径构造环境快照。既有的按路径匹配缓存规则没有改变：移动后的模块会重建缓存，而不会复用过时路径。非 UTF-8 来源路径不会进行有损编码；可选的缓存写入会被跳过。

针对性验证：

```sh
cargo test --release --lib code_source_tests
cargo test --release --lib mount_remaps_imported_source_identity_and_preserves_its_path
cargo test --release --lib run_project_kb_cache_write_then_hit_cross_mod
cargo test --release --test cli_feedback file_session
```

完整 Rust/CLI 内核检查是 `cargo test --release`。验收运行使用 `CARGO_TARGET_DIR=tmp/2026-10-09/unify-code-source/target`，避免与共享 target 目录中的其他构建发生争用。这次重构不改变 Litex 语法、证明规则、符号限定或语句事务。

2026-10-09 的验收结果：

- Release 构建、三项针对性来源测试、来源 ID 重映射、冷/热导入，以及全部七项携带来源的 JSON golden 测试通过。
- 独立 release CLI 的干净文件检查通过。两次 `k >= 0` 断言都在中间拒绝 `1 = 2` 后保持可用；格式错误的交互输入报告 `<repl>`。
- 全部 27 项 CLI/集成测试通过。二进制和 Rust 文档检查也通过（两者都包含零项测试）。
- 完整库检查运行了 1360 项测试：1354 项通过，六项 Lean 编译器测试失败。这**不是**完整内核检查通过的结果。来源/知识库/运行时测试集通过。失败的编译器不使用 `CodeSource`、`Runtime.current_file` 或 `SourceLine.origin`；由于初始工作树不能编译，没有可执行的变更前测试基线。

六项失败位于 `src/compile_to_lean/tests.rs`：

```text
phase2_all_verified_problem_profiles_emit_replayed_artifacts
phase2_computed_value_equality_replays_the_selected_subterm_rewrite
phase2_half_substitution_rejects_deleted_duplicate_wrong_and_unused_citations
phase2_two_closed_aliases_preserve_source_substitution_order
phase2_typed_half_uses_the_actual_closed_substitution_and_closed_child
simplification_alias_equality_uses_its_stored_id_in_the_selected_rewrite
```

例如，Litex 接受 `let half = 1 / 2` 及随后的 `half + half = 1`，但 Lean 输出报告 `WD/Producer: No preceding original constructor or certified parameter supplies this object.`，即没有先前的原始构造器或已认证参数提供该对象。这些失败不属于来源整合的范围。一个过时的编译器测试字段访问被改为 `cite_fact_id()`，以恢复测试编译；本任务没有修复编译器实现。
