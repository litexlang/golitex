//! Why-text for non-builtin searched-proof routes (Normal JSON).
//! Call sites pass a stable kind tag; this module owns EN/ZH copy.

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
            ("builtin_strategy", "内置策略", "由内置多步策略验证")
        }
        ("by_definition", OutputLanguage::English) => (
            "by_definition",
            "By definition",
            "Verified by unfolding a definition",
        ),
        ("by_definition", OutputLanguage::Chinese) => {
            ("by_definition", "按定义", "通过展开定义验证")
        }
        ("known_strategy", OutputLanguage::English) => (
            "known_strategy",
            "Known strategy",
            "Verified by applying a known strategy fact",
        ),
        ("known_strategy", OutputLanguage::Chinese) => {
            ("known_strategy", "已知策略", "应用已知策略事实验证")
        }
        ("builtin_rewrite", OutputLanguage::English) => (
            "builtin_rewrite",
            "Builtin rewrite",
            "Verified by a builtin equality rewrite",
        ),
        ("builtin_rewrite", OutputLanguage::Chinese) => {
            ("builtin_rewrite", "内置改写", "由内置等式改写验证")
        }
        ("known_rewrite", OutputLanguage::English) => (
            "known_rewrite",
            "Known rewrite",
            "Verified by rewriting with a known equality",
        ),
        ("known_rewrite", OutputLanguage::Chinese) => {
            ("known_rewrite", "已知改写", "用已知等式改写验证")
        }
        ("equivalence_class", OutputLanguage::English) => (
            "equivalence_class",
            "Equivalence class",
            "Both sides are in the same equality class",
        ),
        ("equivalence_class", OutputLanguage::Chinese) => {
            ("equivalence_class", "等价类", "两边属于同一个相等类")
        }
        ("object_definition", OutputLanguage::English) => (
            "object_definition",
            "Object definition",
            "Equality follows from an object definition",
        ),
        ("object_definition", OutputLanguage::Chinese) => {
            ("object_definition", "对象定义", "等式由对象定义得出")
        }
        ("matching_one_arg_by_one", OutputLanguage::English) => (
            "matching_one_arg_by_one",
            "Match arguments one-by-one",
            "Function / constructor arguments match pairwise",
        ),
        ("matching_one_arg_by_one", OutputLanguage::Chinese) => {
            ("matching_one_arg_by_one", "逐个匹配参数", "函数或构造子参数逐一匹配")
        }
        ("known_forall_via_symmetry", OutputLanguage::English) => (
            "known_forall_via_symmetry",
            "Forall via symmetry",
            "Verified by a known forall fact after symmetry",
        ),
        ("known_forall_via_symmetry", OutputLanguage::Chinese) => (
            "known_forall_via_symmetry",
            "对称后的全称",
            "对已知全称事实取对称后验证",
        ),
        ("failed", OutputLanguage::English) => ("failed", "Failed", "Verification did not succeed"),
        ("failed", OutputLanguage::Chinese) => ("failed", "失败", "验证未成功"),
        (_, OutputLanguage::English) => (
            "searched_proof",
            "Searched proof",
            "Verified by a searched proof route",
        ),
        (_, OutputLanguage::Chinese) => ("searched_proof", "搜索证明", "由搜索到的证明路径验证"),
    };
    SearchedProofWhyText {
        type_tag,
        rule_name: rule_name.to_string(),
        message: message.to_string(),
    }
}
