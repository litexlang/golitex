use std::fmt;

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
    FamilyIntersectionMember,
    FamilyIntersectionMemberFacts,
    IndexedIntersectionMember,
    FiniteSetSumSubstitution,
    SumOverBijectiveFiniteSetEnumerations,
    RationalHasUniqueReducedFraction,
    SubsetOfFiniteSetIsFinite,
    FiniteSetHasBijectiveIndex,
    FiniteSetReduceSingleton,
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
            "family_intersect_member" => Self::FamilyIntersectionMember,
            "family_intersect_member_facts" => Self::FamilyIntersectionMemberFacts,
            "index_intersect_member" => Self::IndexedIntersectionMember,
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
            "finite_set_reduce_singleton" => Self::FiniteSetReduceSingleton,
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
            Self::FamilyIntersectionMember => "family_intersect_member",
            Self::FamilyIntersectionMemberFacts => "family_intersect_member_facts",
            Self::IndexedIntersectionMember => "index_intersect_member",
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
            Self::FiniteSetReduceSingleton => "finite_set_reduce_singleton",
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

impl BuiltinTheoremId {
    pub fn arity(self) -> usize {
        match self {
            Self::FiniteSetHasBijectiveIndex
            | Self::RationalHasUniqueReducedFraction
            | Self::IndexCartesianNonemptyByChoiceFromFamily
            | Self::IndexCartesianNonemptyByChoiceFromPointwise
            | Self::RealArchimedeanNaturalUpperBound => 1,
            Self::RealMemberLeLeastUpperBound
            | Self::RealLeastUpperBoundLeUpperBound
            | Self::RealGreatestLowerBoundLeMember
            | Self::RealLowerBoundLeGreatestLowerBound => 3,
            _ => 2,
        }
    }
}

pub fn is_reserved_builtin_name(name: &str) -> bool {
    BuiltinTheoremId::from_name(name).is_some() || builtin_certificate_arity(name).is_some()
}

// Opaque legacy predicates produced by completeness and consumed by its
// projection theorems. Recognizing their signature never proves their truth.
pub fn builtin_certificate_arity(name: &str) -> Option<usize> {
    match name {
        "is_real_least_upper_bound" | "is_real_greatest_lower_bound" => Some(2),
        _ => None,
    }
}
