use super::keywords::{
    AND, EQUAL, EXIST, EXIST_BANG, FACT_PREFIX, FORALL, IN, is_comparison_op, NOT, OR,
    RIGHT_ARROW,
};
use super::object::parse_obj;
use crate::new_pipeline::ast::fact::{
    AndChainAtomicFact, AndFact, AtomicFact, ChainAtomicFact, ChainFact, EqualFact, ExistFact,
    ExistOrAndChainAtomicFact, Fact, ForallFact, GreaterEqualFact, GreaterFact, InFact, LessEqualFact,
    LessFact, NotEqualFact, NotForallFact, NotGreaterEqualFact, NotGreaterFact, NotInFact,
    NotLessEqualFact, NotLessFact, OrFact, PlainExistFact, QuantifierFreeFact,
};
use crate::new_pipeline::ast::names::AtomicName;
use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::ast::source_span::SourceSpan;
use crate::new_pipeline::ast::stmt::Stmt;
use crate::new_pipeline::runtime::{Runtime, RuntimeParseError, RuntimeResult};
use crate::new_pipeline::tokenize::TokenBlock;

impl Runtime {
    pub(super) fn parse_fact_stmt(&mut self, block: &TokenBlock) -> RuntimeResult<Stmt> {
        let mut tb = block.clone();
        Ok(Stmt::Fact(self.parse_fact(&mut tb)?))
    }

    pub(super) fn parse_fact(&mut self, tb: &mut TokenBlock) -> RuntimeResult<Fact> {
        match tb.peek() {
            Some(FORALL) => self.parse_forall_fact(tb),
            Some(EXIST) | Some(EXIST_BANG) => Ok(Fact::ExistFact(self.parse_exist_fact(tb)?)),
            Some(NOT) => self.parse_not_fact(tb),
            _ => Ok(self.parse_quantifier_free_fact_top(tb)?.into_fact()),
        }
    }

    fn parse_not_fact(&mut self, tb: &mut TokenBlock) -> RuntimeResult<Fact> {
        tb.expect(NOT)?;
        match tb.peek() {
            Some(FORALL) => {
                let Fact::ForallFact(inner) = self.parse_forall_fact(tb)? else {
                    return Err(RuntimeParseError::new(
                        "`not forall` expects a forall fact",
                        tb.line,
                        tb.source_path.clone(),
                    )
                    .into());
                };
                Ok(Fact::NotForall(NotForallFact {
                    fact_id: self.ids.allocate_fact_id(),
                    forall_fact: inner,
                }))
            }
            Some(EXIST) | Some(EXIST_BANG) => {
                if tb.peek() == Some(EXIST_BANG)
                    || (tb.peek() == Some(EXIST) && tb.peek_at(1) == Some(super::keywords::BANG))
                {
                    return Err(RuntimeParseError::new(
                        "`not exist!` is not supported",
                        tb.line,
                        tb.source_path.clone(),
                    )
                    .into());
                }
                let ExistFact::PlainExistFact(body) = self.parse_exist_fact(tb)? else {
                    return Err(RuntimeParseError::new(
                        "`not exist` expects a plain exist fact",
                        tb.line,
                        tb.source_path.clone(),
                    )
                    .into());
                };
                Ok(Fact::ExistFact(ExistFact::NotExistFact(body)))
            }
            _ => {
                // `not` already consumed; parse a single atomic with negative polarity.
                let atomic = self.parse_chain_or_atomic(tb, false)?;
                match atomic {
                    ChainAtomicFact::AtomicFact(a) => Ok(Fact::AtomicFact(a)),
                    ChainAtomicFact::ChainFact(_) => Err(RuntimeParseError::new(
                        "negated fact must be a single atomic (one operator)",
                        tb.line,
                        tb.source_path.clone(),
                    )
                    .into()),
                }
            }
        }
    }

    fn parse_forall_fact(&mut self, tb: &mut TokenBlock) -> RuntimeResult<Fact> {
        self.push_parse_scope();
        let result = (|| {
            tb.expect(FORALL)?;
            let params = self.parse_typed_param_list_until_colon(tb)?;
            if !tb.exceed_end_of_head() {
                return Err(RuntimeParseError::new(
                    "trailing tokens after forall header",
                    tb.line,
                    tb.source_path.clone(),
                )
                .into());
            }
            if tb.body.is_empty() {
                return Err(RuntimeParseError::new(
                    "forall expects an indented body",
                    tb.line,
                    tb.source_path.clone(),
                )
                .into());
            }

            let last_is_arrow = tb
                .body
                .last()
                .and_then(|b| b.header.first())
                .map(String::as_str)
                == Some(RIGHT_ARROW);

            let mut dom_facts = Vec::new();
            let mut then_facts = Vec::new();

            if last_is_arrow {
                let n = tb.body.len();
                for block in tb.body.iter().take(n - 1) {
                    let mut child = block.clone();
                    dom_facts.push(self.parse_fact(&mut child)?);
                }
                let mut then_block = tb.body[n - 1].clone();
                then_block.expect(RIGHT_ARROW)?;
                then_block.expect(super::keywords::COLON)?;
                if !then_block.exceed_end_of_head() {
                    return Err(RuntimeParseError::new(
                        "trailing tokens after `=>:`",
                        then_block.line,
                        then_block.source_path.clone(),
                    )
                    .into());
                }
                for block in &then_block.body {
                    let mut child = block.clone();
                    then_facts.push(self.parse_exist_or_and_chain_atomic_fact(&mut child)?);
                }
            } else {
                for block in &tb.body {
                    let mut child = block.clone();
                    then_facts.push(self.parse_exist_or_and_chain_atomic_fact(&mut child)?);
                }
            }

            if then_facts.is_empty() {
                return Err(RuntimeParseError::new(
                    "forall expects at least one conclusion fact",
                    tb.line,
                    tb.source_path.clone(),
                )
                .into());
            }

            Ok(Fact::ForallFact(ForallFact {
                fact_id: self.ids.allocate_fact_id(),
                typed_parameters: params,
                dom_facts,
                then_facts,
                span: tb.span(),
            }))
        })();
        self.pop_parse_scope();
        result
    }

    fn parse_exist_fact(&mut self, tb: &mut TokenBlock) -> RuntimeResult<ExistFact> {
        self.push_parse_scope();
        let result = (|| {
            let unique = match tb.peek() {
                Some(EXIST_BANG) => {
                    tb.advance()?;
                    true
                }
                Some(EXIST) => {
                    tb.advance()?;
                    if tb.peek() == Some(super::keywords::BANG) {
                        tb.advance()?;
                        true
                    } else {
                        false
                    }
                }
                _ => {
                    return Err(RuntimeParseError::new(
                        "expected `exist` or `exist!`",
                        tb.line,
                        tb.source_path.clone(),
                    )
                    .into());
                }
            };

            let params = self.parse_typed_param_list_until_st(tb)?;
            tb.expect(super::keywords::ST)?;
            tb.expect(super::keywords::LEFT_CURLY)?;

            let mut facts = Vec::new();
            loop {
                facts.push(self.parse_quantifier_free_fact_inline(tb)?);
                if tb.peek() == Some(super::keywords::RIGHT_CURLY) {
                    break;
                }
                tb.expect(super::keywords::COMMA)?;
            }
            tb.expect(super::keywords::RIGHT_CURLY)?;
            if !tb.exceed_end_of_head() {
                return Err(RuntimeParseError::new(
                    "trailing tokens after exist fact",
                    tb.line,
                    tb.source_path.clone(),
                )
                .into());
            }
            if !tb.body.is_empty() {
                return Err(RuntimeParseError::new(
                    "inline `exist … st {…}` cannot have an indented body",
                    tb.line,
                    tb.source_path.clone(),
                )
                .into());
            }
            if facts.is_empty() {
                return Err(RuntimeParseError::new(
                    "exist body cannot be empty",
                    tb.line,
                    tb.source_path.clone(),
                )
                .into());
            }

            let body = PlainExistFact {
                fact_id: self.ids.allocate_fact_id(),
                typed_parameters: params,
                facts,
                span: tb.span(),
            };
            Ok(if unique {
                ExistFact::ExistUniqueFact(body)
            } else {
                ExistFact::PlainExistFact(body)
            })
        })();
        self.pop_parse_scope();
        result
    }

    fn parse_exist_or_and_chain_atomic_fact(
        &mut self,
        tb: &mut TokenBlock,
    ) -> RuntimeResult<ExistOrAndChainAtomicFact> {
        match tb.peek() {
            Some(EXIST) | Some(EXIST_BANG) => {
                Ok(ExistOrAndChainAtomicFact::ExistFact(self.parse_exist_fact(tb)?))
            }
            Some(NOT) if tb.peek_at(1) == Some(EXIST) => {
                tb.expect(NOT)?;
                if tb.peek() == Some(EXIST_BANG)
                    || (tb.peek() == Some(EXIST) && tb.peek_at(1) == Some(super::keywords::BANG))
                {
                    return Err(RuntimeParseError::new(
                        "`not exist!` is not supported",
                        tb.line,
                        tb.source_path.clone(),
                    )
                    .into());
                }
                let ExistFact::PlainExistFact(body) = self.parse_exist_fact(tb)? else {
                    return Err(RuntimeParseError::new(
                        "`not exist` expects a plain exist fact",
                        tb.line,
                        tb.source_path.clone(),
                    )
                    .into());
                };
                Ok(ExistOrAndChainAtomicFact::ExistFact(ExistFact::NotExistFact(
                    body,
                )))
            }
            Some(FORALL) => Err(RuntimeParseError::new(
                "nested `forall` is not allowed here",
                tb.line,
                tb.source_path.clone(),
            )
            .into()),
            _ => Ok(self.parse_quantifier_free_fact_top(tb)?.into_exist_or_and()),
        }
    }

    fn parse_quantifier_free_fact_top(
        &mut self,
        tb: &mut TokenBlock,
    ) -> RuntimeResult<QuantifierFreeFact> {
        let fact = self.parse_quantifier_free_fact_inline(tb)?;
        if !tb.exceed_end_of_head() {
            return Err(RuntimeParseError::new(
                format!("trailing tokens in fact: `{}`", tb.peek().unwrap_or("")),
                tb.line,
                tb.source_path.clone(),
            )
            .into());
        }
        if !tb.body.is_empty() {
            return Err(RuntimeParseError::new(
                "this fact form cannot have an indented body",
                tb.line,
                tb.source_path.clone(),
            )
            .into());
        }
        Ok(fact)
    }

    fn parse_quantifier_free_fact_inline(
        &mut self,
        tb: &mut TokenBlock,
    ) -> RuntimeResult<QuantifierFreeFact> {
        let first = self.parse_and_chain_atomic_fact(tb)?;
        let mut list = vec![first];
        while tb.peek() == Some(OR) {
            tb.advance()?;
            list.push(self.parse_and_chain_atomic_fact(tb)?);
        }
        if list.len() == 1 {
            return Ok(match list.remove(0) {
                AndChainAtomicFact::AtomicFact(a) => QuantifierFreeFact::AtomicFact(a),
                AndChainAtomicFact::AndFact(a) => QuantifierFreeFact::AndFact(a),
                AndChainAtomicFact::ChainFact(c) => QuantifierFreeFact::ChainFact(c),
            });
        }
        Ok(QuantifierFreeFact::OrFact(OrFact {
            fact_id: self.ids.allocate_fact_id(),
            facts: list,
            span: tb.span(),
        }))
    }

    fn parse_and_chain_atomic_fact(
        &mut self,
        tb: &mut TokenBlock,
    ) -> RuntimeResult<AndChainAtomicFact> {
        let first = self.parse_chain_or_atomic(tb, true)?;
        match first {
            ChainAtomicFact::ChainFact(c) => Ok(AndChainAtomicFact::ChainFact(c)),
            ChainAtomicFact::AtomicFact(a) => {
                let mut collected = vec![a];
                while tb.peek() == Some(AND) {
                    tb.advance()?;
                    match self.parse_chain_or_atomic(tb, true)? {
                        ChainAtomicFact::AtomicFact(next) => collected.push(next),
                        ChainAtomicFact::ChainFact(_) => {
                            return Err(RuntimeParseError::new(
                                "`and` cannot combine chain facts",
                                tb.line,
                                tb.source_path.clone(),
                            )
                            .into());
                        }
                    }
                }
                if collected.len() == 1 {
                    Ok(AndChainAtomicFact::AtomicFact(collected.remove(0)))
                } else {
                    Ok(AndChainAtomicFact::AndFact(AndFact {
                        fact_id: self.ids.allocate_fact_id(),
                        facts: collected,
                        span: tb.span(),
                    }))
                }
            }
        }
    }

    // obj op obj [op obj…] or `$in` membership / `$prop` (prop args deferred).
    fn parse_chain_or_atomic(
        &mut self,
        tb: &mut TokenBlock,
        positive: bool,
    ) -> RuntimeResult<ChainAtomicFact> {
        let span = tb.span();

        if tb.peek() == Some(FACT_PREFIX) {
            tb.advance()?;
            let prop = tb.advance()?;
            if prop == IN {
                return Err(RuntimeParseError::new(
                    "leading `$in` is invalid; write `x $in S`",
                    tb.line,
                    tb.source_path.clone(),
                )
                .into());
            }
            return Err(RuntimeParseError::new(
                format!("named prop `${prop}` is not wired yet in new_pipeline"),
                tb.line,
                tb.source_path.clone(),
            )
            .into());
        }

        let first = parse_obj(tb)?;
        let mut objs = vec![first];
        let mut prop_names: Vec<AtomicName> = Vec::new();

        while !tb.exceed_end_of_head() {
            let Some(tok) = tb.peek().map(str::to_string) else {
                break;
            };
            if tok == FACT_PREFIX {
                tb.advance()?;
                let prop = tb.advance()?;
                if prop != IN {
                    return Err(RuntimeParseError::new(
                        format!("infix `${prop}` is not wired yet in new_pipeline"),
                        tb.line,
                        tb.source_path.clone(),
                    )
                    .into());
                }
                if !prop_names.is_empty() {
                    return Err(RuntimeParseError::new(
                        "`$in` cannot appear in a comparison chain",
                        tb.line,
                        tb.source_path.clone(),
                    )
                    .into());
                }
                let set = parse_obj(tb)?;
                if !tb.exceed_end_of_head()
                    && (tb.peek().map(is_comparison_op).unwrap_or(false)
                        || tb.peek() == Some(FACT_PREFIX))
                {
                    return Err(RuntimeParseError::new(
                        "`$in` cannot appear in a comparison chain",
                        tb.line,
                        tb.source_path.clone(),
                    )
                    .into());
                }
                let element = objs.remove(0);
                let atomic = build_membership(self, element, set, positive, span)?;
                return Ok(ChainAtomicFact::AtomicFact(atomic));
            }
            if is_comparison_op(&tok) {
                tb.advance()?;
                prop_names.push(AtomicName::WithoutMod(tok));
                objs.push(parse_obj(tb)?);
                continue;
            }
            break;
        }

        if prop_names.is_empty() {
            return Err(RuntimeParseError::new(
                "expected comparison operator or `$in`",
                tb.line,
                tb.source_path.clone(),
            )
            .into());
        }

        if objs.len() == 2 && prop_names.len() == 1 {
            let right = objs.pop().unwrap();
            let left = objs.pop().unwrap();
            let op = match prop_names.pop().unwrap() {
                AtomicName::WithoutMod(s) => s,
                AtomicName::WithMod(_, _) => {
                    return Err(RuntimeParseError::new(
                        "mod-qualified operators are not supported here",
                        tb.line,
                        tb.source_path.clone(),
                    )
                    .into());
                }
            };
            let atomic = build_compare(self, &op, left, right, positive, span)?;
            return Ok(ChainAtomicFact::AtomicFact(atomic));
        }

        if !positive {
            return Err(RuntimeParseError::new(
                "negated fact must be a single atomic (one operator)",
                tb.line,
                tb.source_path.clone(),
            )
            .into());
        }

        Ok(ChainAtomicFact::ChainFact(ChainFact {
            fact_id: self.ids.allocate_fact_id(),
            objs,
            prop_names,
            span,
        }))
    }
}

fn build_membership(
    rt: &mut Runtime,
    element: Obj,
    set: Obj,
    positive: bool,
    span: SourceSpan,
) -> RuntimeResult<AtomicFact> {
    let fact_id = rt.ids.allocate_fact_id();
    if positive {
        Ok(AtomicFact::InFact(InFact {
            fact_id,
            element,
            set,
            span,
        }))
    } else {
        Ok(AtomicFact::NotInFact(NotInFact {
            fact_id,
            element,
            set,
            span,
        }))
    }
}

fn build_compare(
    rt: &mut Runtime,
    op: &str,
    left: Obj,
    right: Obj,
    positive: bool,
    span: SourceSpan,
) -> RuntimeResult<AtomicFact> {
    let fact_id = rt.ids.allocate_fact_id();
    Ok(match (op, positive) {
        (EQUAL, true) => AtomicFact::EqualFact(EqualFact {
            fact_id,
            left,
            right,
            span,
        }),
        (EQUAL, false) => AtomicFact::NotEqualFact(NotEqualFact {
            fact_id,
            left,
            right,
            span,
        }),
        (super::keywords::NOT_EQUAL, true) => AtomicFact::NotEqualFact(NotEqualFact {
            fact_id,
            left,
            right,
            span,
        }),
        (super::keywords::NOT_EQUAL, false) => AtomicFact::EqualFact(EqualFact {
            fact_id,
            left,
            right,
            span,
        }),
        (super::keywords::LESS, true) => AtomicFact::LessFact(LessFact {
            fact_id,
            left,
            right,
            span,
        }),
        (super::keywords::LESS, false) => AtomicFact::NotLessFact(NotLessFact {
            fact_id,
            left,
            right,
            span,
        }),
        (super::keywords::GREATER, true) => AtomicFact::GreaterFact(GreaterFact {
            fact_id,
            left,
            right,
            span,
        }),
        (super::keywords::GREATER, false) => AtomicFact::NotGreaterFact(NotGreaterFact {
            fact_id,
            left,
            right,
            span,
        }),
        (super::keywords::LESS_EQUAL, true) => AtomicFact::LessEqualFact(LessEqualFact {
            fact_id,
            left,
            right,
            span,
        }),
        (super::keywords::LESS_EQUAL, false) => AtomicFact::NotLessEqualFact(NotLessEqualFact {
            fact_id,
            left,
            right,
            span,
        }),
        (super::keywords::GREATER_EQUAL, true) => {
            AtomicFact::GreaterEqualFact(GreaterEqualFact {
                fact_id,
                left,
                right,
                span,
            })
        }
        (super::keywords::GREATER_EQUAL, false) => {
            AtomicFact::NotGreaterEqualFact(NotGreaterEqualFact {
                fact_id,
                left,
                right,
                span,
            })
        }
                _ => {
            return Err(RuntimeParseError::new(
                format!("unknown comparison `{op}`"),
                span.line,
                span.path.clone(),
            )
            .into());
        }
    })
}

trait QuantifierFreeFactExt {
    fn into_fact(self) -> Fact;
    fn into_exist_or_and(self) -> ExistOrAndChainAtomicFact;
}

impl QuantifierFreeFactExt for QuantifierFreeFact {
    fn into_fact(self) -> Fact {
        match self {
            QuantifierFreeFact::AtomicFact(a) => Fact::AtomicFact(a),
            QuantifierFreeFact::AndFact(a) => Fact::AndFact(a),
            QuantifierFreeFact::ChainFact(c) => Fact::ChainFact(c),
            QuantifierFreeFact::OrFact(o) => Fact::OrFact(o),
        }
    }

    fn into_exist_or_and(self) -> ExistOrAndChainAtomicFact {
        match self {
            QuantifierFreeFact::AtomicFact(a) => ExistOrAndChainAtomicFact::AtomicFact(a),
            QuantifierFreeFact::AndFact(a) => ExistOrAndChainAtomicFact::AndFact(a),
            QuantifierFreeFact::ChainFact(c) => ExistOrAndChainAtomicFact::ChainFact(c),
            QuantifierFreeFact::OrFact(o) => ExistOrAndChainAtomicFact::OrFact(o),
        }
    }
}
