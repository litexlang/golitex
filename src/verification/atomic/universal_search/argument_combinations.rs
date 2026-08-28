//! Reusable tuple, vector, and matrix-row argument matching combinators.

use super::*;

impl ArgMatcher<'_> {
    /// Match two pairs (left_left, given_left) and (left_right, given_right); if either returns None, return None; else merge maps and return Some(merged).
    pub(super) fn match_arg_binary_then_merge(
        &mut self,
        left_left: &Obj,
        left_right: &Obj,
        given_left: &Obj,
        given_right: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        let left_res =
            self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(left_left, given_left)?;
        let map1 = match left_res {
            Some(m) => m,
            None => return Ok(None),
        };
        let right_res =
            self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(left_right, given_right)?;
        let map2 = match right_res {
            Some(m) => m,
            None => return Ok(None),
        };
        let merged = self.merge_arg_match_maps(map1, map2);
        Ok(merged)
    }

    pub(super) fn match_arg_ternary_then_merge(
        &mut self,
        a1: &Obj,
        a2: &Obj,
        a3: &Obj,
        b1: &Obj,
        b2: &Obj,
        b3: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        let m12 = self.match_arg_binary_then_merge(a1, a2, b1, b2)?;
        let map12 = match m12 {
            Some(m) => m,
            None => return Ok(None),
        };
        let m3 = self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(a3, b3)?;
        let map3 = match m3 {
            Some(m) => m,
            None => return Ok(None),
        };
        Ok(self.merge_arg_match_maps(map12, map3))
    }

    pub(super) fn match_arg_quaternary_then_merge(
        &mut self,
        a1: &Obj,
        a2: &Obj,
        a3: &Obj,
        a4: &Obj,
        b1: &Obj,
        b2: &Obj,
        b3: &Obj,
        b4: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        let Some(mut merged) = self.match_arg_ternary_then_merge(a1, a2, a3, b1, b2, b3)? else {
            return Ok(None);
        };
        let Some(last) = self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(a4, b4)?
        else {
            return Ok(None);
        };
        if !self.merge_arg_match_map_into(&mut merged, last) {
            return Ok(None);
        }
        Ok(Some(merged))
    }

    pub(super) fn match_arg_quinary_then_merge(
        &mut self,
        a1: &Obj,
        a2: &Obj,
        a3: &Obj,
        a4: &Obj,
        a5: &Obj,
        b1: &Obj,
        b2: &Obj,
        b3: &Obj,
        b4: &Obj,
        b5: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        let Some(mut merged) =
            self.match_arg_quaternary_then_merge(a1, a2, a3, a4, b1, b2, b3, b4)?
        else {
            return Ok(None);
        };
        let Some(last) = self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(a5, b5)?
        else {
            return Ok(None);
        };
        if !self.merge_arg_match_map_into(&mut merged, last) {
            return Ok(None);
        }
        Ok(Some(merged))
    }

    pub(super) fn merge_arg_match_maps(
        &mut self,
        mut map1: HashMap<String, Obj>,
        map2: HashMap<String, Obj>,
    ) -> Option<HashMap<String, Obj>> {
        if !self.merge_arg_match_map_into(&mut map1, map2) {
            return None;
        }
        Some(map1)
    }

    /// Zip known/given argument pairs of equal length; merge substitution maps from each recursive match.
    pub(super) fn match_arg_pairs_then_merge(
        &mut self,
        pairs: Vec<(&Obj, &Obj)>,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        let mut merged: HashMap<String, Obj> = HashMap::new();
        for (left_elem, given_elem) in pairs {
            let sub_map = match self
                .match_arg_in_atomic_fact_in_known_forall_with_given_arg(left_elem, given_elem)?
            {
                Some(m) => m,
                None => return Ok(None),
            };
            if !self.merge_arg_match_map_into(&mut merged, sub_map) {
                return Ok(None);
            }
        }
        Ok(Some(merged))
    }

    pub(super) fn match_boxed_arg_vec_then_merge(
        &mut self,
        left_elements: &[Box<Obj>],
        given_elements: &[Box<Obj>],
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        if left_elements.len() != given_elements.len() {
            return Ok(None);
        }
        let pairs = left_elements
            .iter()
            .zip(given_elements.iter())
            .map(|(l, g)| (l.as_ref(), g.as_ref()))
            .collect();
        self.match_arg_pairs_then_merge(pairs)
    }

    pub(super) fn match_arg_vec_then_merge(
        &mut self,
        left: &[Obj],
        given: &[Obj],
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        if left.len() != given.len() {
            return Ok(None);
        }
        let pairs = left.iter().zip(given.iter()).collect();
        self.match_arg_pairs_then_merge(pairs)
    }

    pub(super) fn match_arg_matrix_rows_then_merge(
        &mut self,
        left_rows: &[Vec<Box<Obj>>],
        given_rows: &[Vec<Box<Obj>>],
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        if left_rows.len() != given_rows.len() {
            return Ok(None);
        }
        let mut merged: HashMap<String, Obj> = HashMap::new();
        for (lr, gr) in left_rows.iter().zip(given_rows.iter()) {
            let sub_map = match self.match_boxed_arg_vec_then_merge(lr, gr)? {
                Some(m) => m,
                None => return Ok(None),
            };
            if !self.merge_arg_match_map_into(&mut merged, sub_map) {
                return Ok(None);
            }
        }
        Ok(Some(merged))
    }
}
