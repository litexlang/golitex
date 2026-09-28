use std::fmt;

/// Remove the stable `#<digits>#` identity annotations used by the current
/// source formatter for bound symbols. Contract checks compare the resulting
/// alpha-readable source while Result/compiler logic continues to use the
/// original SymbolIds structurally.
pub fn without_bound_symbol_display_ids(source: &str) -> String {
    let bytes = source.as_bytes();
    let mut output = String::with_capacity(source.len());
    let mut cursor = 0;
    while cursor < bytes.len() {
        if bytes[cursor] == b'#' {
            let digits_start = cursor + 1;
            let mut end = digits_start;
            while end < bytes.len() && bytes[end].is_ascii_digit() {
                end += 1;
            }
            if end > digits_start && end < bytes.len() && bytes[end] == b'#' {
                cursor = end + 1;
                continue;
            }
        }
        let character = source[cursor..]
            .chars()
            .next()
            .expect("cursor remains on a UTF-8 character boundary");
        output.push(character);
        cursor += character.len_utf8();
    }
    output
}

/// Stable semantic identity of a reserved theorem implemented by the Litex
/// runtime rather than by a source `thm`/`axiom` declaration.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum BuiltinTheoremId {
    FunctionSetMember,
    SetBuilderMember,
    DefinedSetMember,
    StructMember,
    CartesianMemberFromCoordinates,
    IndexCartesianMember,
    IndexCartesianNonemptyByChoiceFromFamily,
    IndexCartesianNonemptyByChoiceFromPointwise,
    SumLessEqualFromPointwise,
    FiniteSetSumLessEqualFromPointwise,
    FiniteSetSummandLessEqualSum,
    TupleEqualFromCoordinates,
    FiniteSetSumSubstitution,
    SumOverBijectiveFiniteSetEnumerations,
    RationalHasUniqueReducedFraction,
    SubsetOfFiniteSetIsFinite,
    FiniteSetHasBijectiveIndex,
    RealLeastUpperBoundExists,
    RealMemberLeLeastUpperBound,
    RealLeastUpperBoundLeUpperBound,
    RealGreatestLowerBoundExists,
    RealGreatestLowerBoundLeMember,
    RealLowerBoundLeGreatestLowerBound,
    RealArchimedeanNaturalUpperBound,
    RationalBetweenReals,
}

impl BuiltinTheoremId {
    pub fn from_name(name: &str) -> Option<Self> {
        Some(match name {
            "fn_set_member" => Self::FunctionSetMember,
            "set_builder_member" => Self::SetBuilderMember,
            "defined_set_member" => Self::DefinedSetMember,
            "struct_member" => Self::StructMember,
            "cart_member_from_coordinates" => Self::CartesianMemberFromCoordinates,
            "index_cart_member" => Self::IndexCartesianMember,
            "index_cart_nonempty_by_choice_from_family" => {
                Self::IndexCartesianNonemptyByChoiceFromFamily
            }
            "index_cart_nonempty_by_choice_from_pointwise" => {
                Self::IndexCartesianNonemptyByChoiceFromPointwise
            }
            "sum_le_sum_from_pointwise" => Self::SumLessEqualFromPointwise,
            "finite_set_sum_le_from_pointwise" => Self::FiniteSetSumLessEqualFromPointwise,
            "finite_set_summand_le_sum" => Self::FiniteSetSummandLessEqualSum,
            "tuple_equal_from_coordinates" => Self::TupleEqualFromCoordinates,
            "finite_set_sum_substitution" => Self::FiniteSetSumSubstitution,
            "sum_over_bijective_finite_set_enumerations" => {
                Self::SumOverBijectiveFiniteSetEnumerations
            }
            "rational_has_unique_reduced_fraction" => Self::RationalHasUniqueReducedFraction,
            "subset_of_finite_set_is_finite" => Self::SubsetOfFiniteSetIsFinite,
            "finite_set_has_bijective_index" => Self::FiniteSetHasBijectiveIndex,
            "real_least_upper_bound_exists" => Self::RealLeastUpperBoundExists,
            "real_member_le_least_upper_bound" => Self::RealMemberLeLeastUpperBound,
            "real_least_upper_bound_le_upper_bound" => Self::RealLeastUpperBoundLeUpperBound,
            "real_greatest_lower_bound_exists" => Self::RealGreatestLowerBoundExists,
            "real_greatest_lower_bound_le_member" => Self::RealGreatestLowerBoundLeMember,
            "real_lower_bound_le_greatest_lower_bound" => Self::RealLowerBoundLeGreatestLowerBound,
            "real_archimedean_natural_upper_bound" => Self::RealArchimedeanNaturalUpperBound,
            "rational_between_reals" => Self::RationalBetweenReals,
            _ => return None,
        })
    }

    pub const fn as_str(self) -> &'static str {
        match self {
            Self::FunctionSetMember => "fn_set_member",
            Self::SetBuilderMember => "set_builder_member",
            Self::DefinedSetMember => "defined_set_member",
            Self::StructMember => "struct_member",
            Self::CartesianMemberFromCoordinates => "cart_member_from_coordinates",
            Self::IndexCartesianMember => "index_cart_member",
            Self::IndexCartesianNonemptyByChoiceFromFamily => {
                "index_cart_nonempty_by_choice_from_family"
            }
            Self::IndexCartesianNonemptyByChoiceFromPointwise => {
                "index_cart_nonempty_by_choice_from_pointwise"
            }
            Self::SumLessEqualFromPointwise => "sum_le_sum_from_pointwise",
            Self::FiniteSetSumLessEqualFromPointwise => "finite_set_sum_le_from_pointwise",
            Self::FiniteSetSummandLessEqualSum => "finite_set_summand_le_sum",
            Self::TupleEqualFromCoordinates => "tuple_equal_from_coordinates",
            Self::FiniteSetSumSubstitution => "finite_set_sum_substitution",
            Self::SumOverBijectiveFiniteSetEnumerations => {
                "sum_over_bijective_finite_set_enumerations"
            }
            Self::RationalHasUniqueReducedFraction => "rational_has_unique_reduced_fraction",
            Self::SubsetOfFiniteSetIsFinite => "subset_of_finite_set_is_finite",
            Self::FiniteSetHasBijectiveIndex => "finite_set_has_bijective_index",
            Self::RealLeastUpperBoundExists => "real_least_upper_bound_exists",
            Self::RealMemberLeLeastUpperBound => "real_member_le_least_upper_bound",
            Self::RealLeastUpperBoundLeUpperBound => "real_least_upper_bound_le_upper_bound",
            Self::RealGreatestLowerBoundExists => "real_greatest_lower_bound_exists",
            Self::RealGreatestLowerBoundLeMember => "real_greatest_lower_bound_le_member",
            Self::RealLowerBoundLeGreatestLowerBound => "real_lower_bound_le_greatest_lower_bound",
            Self::RealArchimedeanNaturalUpperBound => "real_archimedean_natural_upper_bound",
            Self::RationalBetweenReals => "rational_between_reals",
        }
    }
}

impl fmt::Display for BuiltinTheoremId {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.as_str())
    }
}
