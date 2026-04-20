use crate::prelude::*;

impl Runtime {
    pub fn parse_witness_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(WITNESS)?;
        if tb.current_token_is_equal_to(EXIST) {
            self.parse_witness_exist_fact(tb)
        } else if tb.current_token_is_equal_to(FACT_PREFIX) {
            self.parse_witness_nonempty_set(tb)
        } else {
            return Err(
                RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
 None,
                "witness expects a exist or nonempty set".to_string(),
                tb.line_file.clone(),
                None,
                vec![],
            ))));
        }
    }

    // witness exist x, y R st {x > y} from 1, 0:
    // Or omit ':' and proof: witness exist ... from 1, 0
    pub fn parse_witness_exist_fact(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        let exist_fact_in_witness = self.parse_exist_fact(tb)?;
        tb.skip_token(FROM)?;
        let equal_tos = self.parse_obj_list(tb)?;
        let proof = if tb.exceed_end_of_head() {
            if !tb.body.is_empty() {
                return Err(
                    RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
 None,
                "witness exist: indented proof body requires ':' at end of header line"
                            .to_string(),
                tb.line_file.clone(),
                None,
                vec![],
            ))));
            }
            Vec::new()
        } else {
            tb.skip_token(COLON)?;
            if !tb.exceed_end_of_head() {
                return Err(
                    RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
 None,
                "witness exist: unexpected tokens after ':' in header".to_string(),
                tb.line_file.clone(),
                None,
                vec![],
            ))));
            }
            let names = exist_fact_in_witness
                .params_def_with_type
                .collect_param_names();
            let lf = tb.line_file.clone();
            self.parse_stmts_with_optional_free_param_scope(
                FreeParamObjType::Exist,
                &names,
                lf,
                |this| {
                    tb.body
                        .iter_mut()
                        .map(|b| this.parse_stmt(b))
                        .collect::<Result<_, _>>()
                },
            )?
        };
        Ok(WitnessExistFact::new(
            equal_tos,
            exist_fact_in_witness,
            proof,
            tb.line_file.clone(),
        )
        .into())
    }

    // witness $is_nonempty_set(R) from 1:
    pub fn parse_witness_nonempty_set(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Stmt, RuntimeError> {
        tb.skip_token(FACT_PREFIX)?;
        tb.skip_token(IS_NONEMPTY_SET)?;
        tb.skip_token(LEFT_BRACE)?;
        let set = self.parse_obj(tb)?;
        tb.skip_token(RIGHT_BRACE)?;
        tb.skip_token(FROM)?;
        let obj = self.parse_obj(tb)?;

        let mut proof = Vec::with_capacity(tb.body.len());
        for block in tb.body.iter_mut() {
            proof.push(self.parse_stmt(block)?);
        }
        Ok(WitnessNonemptySet::new(obj, set, proof, tb.line_file.clone()).into())
    }
}
