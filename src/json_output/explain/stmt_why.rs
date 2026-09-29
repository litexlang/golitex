//! Localized why-text for define-obj statements and coarse compound facts.

use crate::launch_command::OutputLanguage;

pub struct StmtWhyText {
    pub type_tag: &'static str,
    pub rule_name: String,
    pub message: String,
}

pub fn explain_define_obj_why(kind: &str, lang: OutputLanguage) -> StmtWhyText {
    let (rule_name, message) = match (kind, lang) {
        ("let", OutputLanguage::English) => (
            "Let binding",
            "Bind a name to a well-defined value",
        ),
        ("let", OutputLanguage::Chinese) => ("赋值定义", "把名字绑定到一个良定的值"),
        ("have_in_nonempty", OutputLanguage::English) => (
            "Have from nonempty set",
            "Introduce an object from a nonempty carrier / parameter type",
        ),
        ("have_in_nonempty", OutputLanguage::Chinese) => {
            ("从非空集合引入", "从非空载体或参数类型引入对象")
        }
        ("have_equal", OutputLanguage::English) => (
            "Have with equality",
            "Introduce an object equal to a given well-defined value",
        ),
        ("have_equal", OutputLanguage::Chinese) => {
            ("带等式的 have", "引入与给定良定值相等的对象")
        }
        ("have_by_exist", OutputLanguage::English) => (
            "Have by existence",
            "Introduce objects from a proved existential fact",
        ),
        ("have_by_exist", OutputLanguage::Chinese) => {
            ("由存在性引入", "由已证明的存在事实引入对象")
        }
        (_, OutputLanguage::English) => ("Define object", "Define an object in the environment"),
        (_, OutputLanguage::Chinese) => ("定义对象", "在环境中定义一个对象"),
    };
    StmtWhyText {
        type_tag: "define_obj",
        rule_name: rule_name.to_string(),
        message: message.to_string(),
    }
}

pub fn explain_compound_fact_why(kind: &str, lang: OutputLanguage) -> StmtWhyText {
    let (rule_name, message) = match (kind, lang) {
        ("and", OutputLanguage::English) => (
            "Conjunction",
            "Verified as a compound and-fact (details omitted in Normal)",
        ),
        ("and", OutputLanguage::Chinese) => {
            ("合取", "作为合取事实验证（Normal 省略细节）")
        }
        ("or", OutputLanguage::English) => (
            "Disjunction",
            "Verified as a compound or-fact (details omitted in Normal)",
        ),
        ("or", OutputLanguage::Chinese) => {
            ("析取", "作为析取事实验证（Normal 省略细节）")
        }
        ("forall", OutputLanguage::English) => (
            "Universal",
            "Verified as a forall fact (details omitted in Normal)",
        ),
        ("forall", OutputLanguage::Chinese) => {
            ("全称", "作为全称事实验证（Normal 省略细节）")
        }
        ("exist", OutputLanguage::English) => (
            "Existential",
            "Verified as an exist fact (details omitted in Normal)",
        ),
        ("exist", OutputLanguage::Chinese) => {
            ("存在", "作为存在事实验证（Normal 省略细节）")
        }
        ("chain", OutputLanguage::English) => (
            "Chain",
            "Verified as a chain fact (details omitted in Normal)",
        ),
        ("chain", OutputLanguage::Chinese) => {
            ("链式", "作为链式事实验证（Normal 省略细节）")
        }
        (_, OutputLanguage::English) => (
            "Compound fact",
            "Verified as a compound fact (details omitted in Normal)",
        ),
        (_, OutputLanguage::Chinese) => {
            ("复合事实", "作为复合事实验证（Normal 省略细节）")
        }
    };
    StmtWhyText {
        type_tag: "compound_fact",
        rule_name: rule_name.to_string(),
        message: message.to_string(),
    }
}
