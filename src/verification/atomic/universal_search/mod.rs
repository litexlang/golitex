//! Atomic verification by instantiating known universal facts.

use crate::prelude::*;
use crate::verification::known_forall_profile::{self, KnownForallSearchPhase};
use std::collections::HashMap;
use std::rc::Rc;
use std::result::Result;

mod anonymous_function_alpha;
mod anonymous_function_bodies;
mod argument_combinations;
mod argument_shapes;
mod arithmetic_arguments;
mod binder_arguments;
mod collection_arguments;
mod finite_set_measure_arguments;
mod function_collection_arguments;
mod interval_sequence_arguments;
mod iterated_arguments;
mod matcher_dispatch;
mod matcher_state;
mod matrix_index_arguments;
mod search;
mod set_operation_arguments;
mod tuple_arguments;

use argument_shapes::*;
use matcher_state::ArgMatcher;
