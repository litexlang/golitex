//! Why-text for non-builtin searched-proof routes (Normal JSON).
//! Call sites pass a stable English kind; this module owns EN/ZH copy including
//! the emitted `type` value (no English tokens under Chinese).

use crate::launch_command::OutputLanguage;

pub struct SearchedProofWhyText {
    pub type_tag: &'static str,
    pub rule_name: String,
    pub message: String,
}

pub fn explain_searched_proof_why(kind: &str, lang: OutputLanguage) -> SearchedProofWhyText {
    let (type_tag, rule_name, message) = match (kind, lang) {
        ("builtin_strategy", OutputLanguage::English) => (
            "builtin_strategy",
            "Builtin strategy",
            "Verified by a builtin multi-step strategy",
        ),
        ("builtin_strategy", OutputLanguage::Chinese) => {
            ("内置策略", "内置策略", "由内置多步策略验证")
        }
        ("by_definition", OutputLanguage::English) => (
            "by_definition",
            "By definition",
            "Verified by unfolding a definition",
        ),
        ("by_definition", OutputLanguage::Chinese) => ("按定义", "按定义", "通过展开定义验证"),
        ("known_strategy", OutputLanguage::English) => (
            "known_strategy",
            "Known strategy",
            "Verified by applying a known strategy fact",
        ),
        ("known_strategy", OutputLanguage::Chinese) => {
            ("已知策略", "已知策略", "应用已知策略事实验证")
        }
        ("builtin_rewrite", OutputLanguage::English) => (
            "builtin_rewrite",
            "Builtin rewrite",
            "Verified by a builtin equality rewrite",
        ),
        ("builtin_rewrite", OutputLanguage::Chinese) => {
            ("内置改写", "内置改写", "由内置等式改写验证")
        }
        ("known_rewrite", OutputLanguage::English) => (
            "known_rewrite",
            "Known rewrite",
            "Verified by rewriting with a known equality",
        ),
        ("known_rewrite", OutputLanguage::Chinese) => {
            ("已知改写", "已知改写", "用已知等式改写验证")
        }
        ("they_are_the_same", OutputLanguage::English) => (
            "they_are_the_same",
            "Same object",
            "Both sides have identical IR or alpha-equivalent binder structure",
        ),
        ("they_are_the_same", OutputLanguage::Chinese) => (
            "同一对象",
            "同一对象",
            "两边内部表示相同，或绑定参数改名后结构相同",
        ),
        ("equivalence_class", OutputLanguage::English) => (
            "equivalence_class",
            "Equivalence class",
            "Equality follows from stored paths, possibly joined by a checked peer proof",
        ),
        ("equivalence_class", OutputLanguage::Chinese) => {
            ("等价类", "等价类", "由已知等式链证明，必要时用已验证的类成员比较连接两条链")
        }
        ("object_definition", OutputLanguage::English) => (
            "object_definition",
            "Object definition",
            "Equality follows from an object definition",
        ),
        ("object_definition", OutputLanguage::Chinese) => {
            ("对象定义", "对象定义", "等式由对象定义得出")
        }
        ("matching_one_arg_by_one", OutputLanguage::English) => (
            "matching_one_arg_by_one",
            "Match arguments one-by-one",
            "Function / constructor arguments match pairwise",
        ),
        ("matching_one_arg_by_one", OutputLanguage::Chinese) => {
            ("逐个匹配参数", "逐个匹配参数", "函数或构造子参数逐一匹配")
        }
        ("known_forall_via_symmetry", OutputLanguage::English) => (
            "known_forall_via_symmetry",
            "Forall via symmetry",
            "Verified by a known forall fact after symmetry",
        ),
        ("known_forall_via_symmetry", OutputLanguage::Chinese) => (
            "对称后的全称",
            "对称后的全称",
            "对已知全称事实取对称后验证",
        ),
        ("failed", OutputLanguage::English) => ("failed", "Failed", "Verification did not succeed"),
        ("failed", OutputLanguage::Chinese) => ("失败", "失败", "验证未成功"),
        (_, OutputLanguage::English) => (
            "searched_proof",
            "Searched proof",
            "Verified by a searched proof route",
        ),
        (_, OutputLanguage::Chinese) => ("搜索证明", "搜索证明", "由搜索到的证明路径验证"),
    };
    SearchedProofWhyText {
        type_tag,
        rule_name: rule_name.to_string(),
        message: message.to_string(),
    }
}
