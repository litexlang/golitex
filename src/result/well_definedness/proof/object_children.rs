//! Object proof identities and recursive child uses.

use crate::prelude::*;

/// Runtime-wide identity of one fixed object whose well-definedness was verified.
///
/// Visibility still follows the owning Litex environment. Runtime-wide
/// allocation only prevents committed child environments from colliding with
/// their parents and prevents rolled-back identities from being reused.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct WellDefinedObjId(u64);

impl WellDefinedObjId {
    pub fn new(value: u64) -> Self {
        Self(value)
    }

    pub fn value(self) -> u64 {
        self.0
    }
}

/// Exact construction position at which a parent object consumes one direct
/// child object. Roles are ordered and may repeat the same object identity.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum WellDefinedObjChildRole {
    /// The already-checked callable prefix consumed by the next source
    /// application layer.  For `g(1)(2)`, the outer object points to the
    /// independently named prefix object `g(1)` through this edge.
    FunctionPrefix {
        through_layer_index: usize,
    },
    /// A structured callable expression consumed by the first application
    /// layer, for example an anonymous function, sequence literal, matrix
    /// operator, field projection, or instantiated template.
    FunctionHead,
    FunctionArgument {
        layer_index: usize,
        argument_index: usize,
    },
    BuiltinArgument {
        argument_index: usize,
    },
    ConstructorArgument {
        argument_index: usize,
    },
    BinderParameterCarrier {
        parameter_group_index: usize,
    },
    BinderReturnCarrier,
    BinderBody,
    /// A nested object check performed while proving the parent well-defined,
    /// but not consumed as a value slot by the parent's target constructor.
    /// These ordered audit edges preserve Litex's verification trace. A Lean
    /// emitter must never use them to fill a constructor argument.
    VerificationDependency {
        dependency_index: usize,
    },
}

#[derive(Clone)]
pub struct WellDefinedObjChildUse {
    pub role: WellDefinedObjChildRole,
    pub obj_id: WellDefinedObjId,
    /// Exact object checked at this edge. This independently freezes audit
    /// dependencies, whose target cannot be reconstructed from a constructor
    /// value slot.
    pub source_object: Obj,
}

impl WellDefinedObjChildUse {
    pub fn new(
        role: WellDefinedObjChildRole,
        obj_id: WellDefinedObjId,
        source_object: Obj,
    ) -> Self {
        Self {
            role,
            obj_id,
            source_object,
        }
    }
}

impl std::fmt::Debug for WellDefinedObjChildUse {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("WellDefinedObjChildUse")
            .field("role", &self.role)
            .field("obj_id", &self.obj_id)
            .field("source_object", &self.source_object.to_string())
            .finish()
    }
}
