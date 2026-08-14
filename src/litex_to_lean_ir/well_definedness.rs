use super::*;
use crate::obj::FnObjHead;
use crate::prelude::{
    obj_for_bound_param_in_scope, objs_equal_with_nested_binder_alpha_equivalence, Number,
    ParamObjType,
};
use crate::result::WellDefinedObjChildRole;
use crate::stmt::parameter_def::ParamGroupWithSet;
use std::collections::{HashMap, HashSet, VecDeque};

/// Validate the frozen WD graph without consulting a live Litex environment.
/// Both IR construction and Lean emission call this boundary so neither side
/// can accept dangling or retargeted verifier evidence.
pub(crate) fn validate_litex_to_lean_well_definedness_certificate(
    certificate: &LitexToLeanWellDefinednessCertificateIr,
) -> Result<(), String> {
    let mut facts_by_well_defined_id = HashMap::new();
    for fact in certificate.facts.iter() {
        if facts_by_well_defined_id
            .insert(fact.well_defined_fact_id, fact)
            .is_some()
        {
            return Err(format!(
                "WellDefinedFactId {} is duplicated in one frozen certificate",
                fact.well_defined_fact_id.value()
            ));
        }
        if fact.expected_proposition.to_string() != fact.fact.proposition.to_string() {
            return Err(format!(
                "WellDefinedFactId {} changed proposition inside the frozen certificate",
                fact.well_defined_fact_id.value()
            ));
        }
    }

    let mut objects_by_id = HashMap::new();
    for object in certificate.objects.iter() {
        if objects_by_id
            .insert(object.well_defined_obj_id, object)
            .is_some()
        {
            return Err(format!(
                "WellDefinedObjId {} is duplicated in one frozen certificate",
                object.well_defined_obj_id.value()
            ));
        }
    }

    let mut binder_scopes_by_id = HashMap::new();
    for scope in certificate.binder_scopes.iter() {
        if binder_scopes_by_id.insert(scope.scope_id, scope).is_some() {
            return Err(format!(
                "WellDefinedBinderScopeId {} is duplicated in one frozen certificate",
                scope.scope_id.value()
            ));
        }
        let mut premise_roles = HashSet::new();
        let mut premise_fact_ids = HashSet::new();
        for premise in scope.premises.iter() {
            if !premise_roles.insert(premise.role) {
                return Err(format!(
                    "WellDefinedBinderScopeId {} repeats premise role {:?}",
                    scope.scope_id.value(),
                    premise.role
                ));
            }
            if !premise_fact_ids.insert(premise.fact_id) {
                return Err(format!(
                    "WellDefinedBinderScopeId {} repeats premise FactId {}",
                    scope.scope_id.value(),
                    premise.fact_id.value()
                ));
            }
        }
    }
    for scope in certificate.binder_scopes.iter() {
        validate_binder_scope_chain(
            scope.scope_id,
            &scope.ambient_scope_ids,
            &binder_scopes_by_id,
        )?;
        validate_binder_scope_recipe(scope)?;
    }
    for fact in certificate.facts.iter() {
        validate_scope_reference_chain(
            &format!("WellDefinedFactId {}", fact.well_defined_fact_id.value()),
            &fact.ambient_binder_scope_ids,
            &binder_scopes_by_id,
        )?;
    }

    let mut root_ids = HashSet::new();
    for root_id in certificate.root_obj_ids.iter().copied() {
        if !root_ids.insert(root_id) {
            return Err(format!(
                "WellDefinedObjId {} is duplicated in the root object list",
                root_id.value()
            ));
        }
        if !objects_by_id.contains_key(&root_id) {
            return Err(format!(
                "root WellDefinedObjId {} has no frozen object record",
                root_id.value()
            ));
        }
    }

    let mut root_uses = HashSet::new();
    for root_use in certificate.root_proof_uses.iter().copied() {
        if !root_uses.insert(root_use) {
            return Err(format!(
                "WellDefinedObjId {} has a duplicated {:?} root use",
                root_use.well_defined_obj_id.value(),
                root_use.phase
            ));
        }
        if !root_ids.contains(&root_use.well_defined_obj_id) {
            return Err(format!(
                "root use for WellDefinedObjId {} is absent from the root object list",
                root_use.well_defined_obj_id.value()
            ));
        }
    }
    for root_id in root_ids.iter() {
        if !certificate
            .root_proof_uses
            .iter()
            .any(|root_use| root_use.well_defined_obj_id == *root_id)
        {
            return Err(format!(
                "root WellDefinedObjId {} has no execution-phase use",
                root_id.value()
            ));
        }
    }

    let mut source_object_uses = HashMap::new();
    for source_use in certificate.source_object_uses.iter() {
        if source_object_uses
            .insert(source_use.source_occurrence_id, source_use)
            .is_some()
        {
            return Err(format!(
                "source occurrence {} has more than one frozen WD object use",
                source_use.source_occurrence_id.value()
            ));
        }
        if source_use.source_object.source_occurrence_id() != Some(source_use.source_occurrence_id)
        {
            return Err(format!(
                "source occurrence {} changed or lost its parser-owned identity inside the frozen WD object use",
                source_use.source_occurrence_id.value()
            ));
        }
        let object = objects_by_id
            .get(&source_use.well_defined_obj_id)
            .ok_or_else(|| {
                format!(
                    "source occurrence {} cites missing WellDefinedObjId {}",
                    source_use.source_occurrence_id.value(),
                    source_use.well_defined_obj_id.value()
                )
            })?;
        if crate::obj::obj_equality_key(&source_use.source_object)
            != crate::obj::obj_equality_key(&object.source_object)
        {
            return Err(format!(
                "source occurrence {} changed the source object owned by WellDefinedObjId {}",
                source_use.source_occurrence_id.value(),
                source_use.well_defined_obj_id.value()
            ));
        }
    }

    let mut used_fact_ids = HashSet::new();
    let fact_scope_ids = certificate
        .facts
        .iter()
        .map(|fact| (fact.well_defined_fact_id, &fact.ambient_binder_scope_ids))
        .collect::<HashMap<_, _>>();
    let mut parent_ids_by_child = HashMap::<WellDefinedObjId, Vec<WellDefinedObjId>>::new();
    let mut remaining_child_counts = HashMap::new();
    let mut owned_scope_ids = HashSet::new();
    for object in certificate.objects.iter() {
        validate_scope_reference_chain(
            &format!("WellDefinedObjId {}", object.well_defined_obj_id.value()),
            &object.ambient_binder_scope_ids,
            &binder_scopes_by_id,
        )?;
        if let Some(scope_id) = object.owned_binder_scope_id {
            if !owned_scope_ids.insert(scope_id) {
                return Err(format!(
                    "WellDefinedBinderScopeId {} is owned by more than one object",
                    scope_id.value()
                ));
            }
            let scope = binder_scopes_by_id.get(&scope_id).ok_or_else(|| {
                format!(
                    "WellDefinedObjId {} owns missing WellDefinedBinderScopeId {}",
                    object.well_defined_obj_id.value(),
                    scope_id.value()
                )
            })?;
            if !objs_equal_with_nested_binder_alpha_equivalence(
                &object.source_object,
                &scope.owner_object,
            ) {
                return Err(format!(
                    "WellDefinedObjId {} changed the owner of WellDefinedBinderScopeId {}",
                    object.well_defined_obj_id.value(),
                    scope_id.value()
                ));
            }
            if scope.ambient_scope_ids != object.ambient_binder_scope_ids {
                return Err(format!(
                    "WellDefinedObjId {} and its owned binder scope {} disagree on their ambient scope chain",
                    object.well_defined_obj_id.value(),
                    scope_id.value()
                ));
            }
        }
        if matches!(object.source_object, Obj::AnonymousFn(_))
            && object.owned_binder_scope_id.is_none()
        {
            return Err(format!(
                "WellDefinedObjId {} anonymous function has no frozen binder scope",
                object.well_defined_obj_id.value()
            ));
        }
        remaining_child_counts.insert(object.well_defined_obj_id, object.child_uses.len());
        let mut child_roles = HashSet::new();
        let mut verification_dependency_indices = Vec::new();
        for child in object.child_uses.iter() {
            if !child_roles.insert(child.role) {
                return Err(format!(
                    "WellDefinedObjId {} repeats object-child role {:?}",
                    object.well_defined_obj_id.value(),
                    child.role
                ));
            }
            if let WellDefinedObjChildRole::VerificationDependency { dependency_index } = child.role
            {
                verification_dependency_indices.push(dependency_index);
            }
            let child_object = objects_by_id.get(&child.obj_id).ok_or_else(|| {
                format!(
                    "WellDefinedObjId {} cites missing child WellDefinedObjId {} at role {:?}",
                    object.well_defined_obj_id.value(),
                    child.obj_id.value(),
                    child.role
                )
            })?;
            let mut available_scope_ids = object.ambient_binder_scope_ids.clone();
            if let Some(scope_id) = object.owned_binder_scope_id {
                available_scope_ids.push(scope_id);
            }
            if !available_scope_ids.starts_with(&child_object.ambient_binder_scope_ids) {
                return Err(format!(
                    "WellDefinedObjId {} child {} at role {:?} requires binder scopes {:?}, outside the parent's available chain {:?}",
                    object.well_defined_obj_id.value(),
                    child.obj_id.value(),
                    child.role,
                    child_object.ambient_binder_scope_ids,
                    available_scope_ids
                ));
            }
            if crate::obj::obj_equality_key(&child.source_object)
                != crate::obj::obj_equality_key(&child_object.source_object)
            {
                return Err(format!(
                    "WellDefinedObjId {} changed child snapshot at role {:?}: edge retained `{}`, but WellDefinedObjId {} owns `{}`",
                    object.well_defined_obj_id.value(),
                    child.role,
                    child.source_object,
                    child.obj_id.value(),
                    child_object.source_object
                ));
            }
            if let Some(expected_child) =
                expected_construction_child(&object.source_object, child.role)?
            {
                if crate::obj::obj_equality_key(&expected_child)
                    != crate::obj::obj_equality_key(&child.source_object)
                {
                    return Err(format!(
                        "WellDefinedObjId {} changed construction child {:?}: expected `{}`, got `{}` from WellDefinedObjId {}",
                        object.well_defined_obj_id.value(),
                        child.role,
                        expected_child,
                        child_object.source_object,
                        child.obj_id.value()
                    ));
                }
            }
            parent_ids_by_child
                .entry(child.obj_id)
                .or_default()
                .push(object.well_defined_obj_id);
        }
        verification_dependency_indices.sort_unstable();
        if verification_dependency_indices
            .iter()
            .copied()
            .ne(0..verification_dependency_indices.len())
        {
            return Err(format!(
                "WellDefinedObjId {} has non-contiguous verification-dependency indices {:?}",
                object.well_defined_obj_id.value(),
                verification_dependency_indices
            ));
        }
        for expected_role in expected_construction_roles(&object.source_object) {
            if !child_roles.contains(&expected_role) {
                return Err(format!(
                    "WellDefinedObjId {} is missing required construction-child role {:?} for `{}`",
                    object.well_defined_obj_id.value(),
                    expected_role,
                    object.source_object
                ));
            }
        }

        let mut direct_fact_ids = HashSet::new();
        for fact_id in object.well_defined_fact_ids.iter().copied() {
            if !direct_fact_ids.insert(fact_id) {
                return Err(format!(
                    "WellDefinedObjId {} repeats direct WellDefinedFactId {}",
                    object.well_defined_obj_id.value(),
                    fact_id.value()
                ));
            }
            facts_by_well_defined_id.get(&fact_id).ok_or_else(|| {
                format!(
                    "WellDefinedObjId {} cites missing direct WellDefinedFactId {}",
                    object.well_defined_obj_id.value(),
                    fact_id.value()
                )
            })?;
            let mut available_scope_ids = object.ambient_binder_scope_ids.clone();
            if let Some(scope_id) = object.owned_binder_scope_id {
                available_scope_ids.push(scope_id);
            }
            let retained_scope_ids = fact_scope_ids
                .get(&fact_id)
                .expect("every validated WD fact has scope metadata");
            if !available_scope_ids.starts_with(retained_scope_ids.as_slice()) {
                return Err(format!(
                    "WellDefinedObjId {} direct WellDefinedFactId {} requires binder scopes {:?}, outside the object's available chain {:?}",
                    object.well_defined_obj_id.value(),
                    fact_id.value(),
                    retained_scope_ids,
                    available_scope_ids
                ));
            }
            used_fact_ids.insert(fact_id);
        }

        let mut requirement_roles = HashSet::new();
        for requirement in object.target_requirements.iter() {
            if !requirement_roles.insert(requirement.role) {
                return Err(format!(
                    "WellDefinedObjId {} repeats target requirement role {:?}",
                    object.well_defined_obj_id.value(),
                    requirement.role
                ));
            }
            let fact = facts_by_well_defined_id
                .get(&requirement.well_defined_fact_id)
                .ok_or_else(|| {
                    format!(
                        "WellDefinedObjId {} target requirement cites missing WellDefinedFactId {}",
                        object.well_defined_obj_id.value(),
                        requirement.well_defined_fact_id.value()
                    )
                })?;
            if fact.expected_proposition.to_string() != requirement.expected_proposition.to_string()
            {
                return Err(format!(
                    "WellDefinedObjId {} target requirement changed WellDefinedFactId {}",
                    object.well_defined_obj_id.value(),
                    requirement.well_defined_fact_id.value()
                ));
            }
            if !direct_fact_ids.contains(&requirement.well_defined_fact_id) {
                return Err(format!(
                    "WellDefinedObjId {} target requirement {:?} does not cite one of its direct WD facts",
                    object.well_defined_obj_id.value(),
                    requirement.role
                ));
            }
            if matches!(
                requirement.role,
                WellDefinednessRequirementRole::AnonymousFunctionBodyMembership
                    | WellDefinednessRequirementRole::AnonymousFunctionBoundParameterSubset { .. }
            ) {
                let mut exact_scope_ids = object.ambient_binder_scope_ids.clone();
                exact_scope_ids.push(object.owned_binder_scope_id.ok_or_else(|| {
                    format!(
                        "WellDefinedObjId {} anonymous closure has no owned binder scope",
                        object.well_defined_obj_id.value()
                    )
                })?);
                if fact_scope_ids
                    .get(&requirement.well_defined_fact_id)
                    .copied()
                    != Some(&exact_scope_ids)
                {
                    return Err(format!(
                        "WellDefinedObjId {} anonymous closure fact {} was proved outside its exact binder scope",
                        object.well_defined_obj_id.value(),
                        requirement.well_defined_fact_id.value()
                    ));
                }
            }
            used_fact_ids.insert(requirement.well_defined_fact_id);
        }
        validate_object_target_requirement_recipe(object, &requirement_roles)?;
    }

    if owned_scope_ids.len() != certificate.binder_scopes.len() {
        return Err("well-definedness certificate contains an unowned binder scope".to_string());
    }

    let mut ready = VecDeque::new();
    for (object_id, child_count) in remaining_child_counts.iter() {
        if *child_count == 0 {
            ready.push_back(*object_id);
        }
    }
    let mut completed_object_count = 0;
    while let Some(object_id) = ready.pop_front() {
        completed_object_count += 1;
        if let Some(parent_ids) = parent_ids_by_child.get(&object_id) {
            for parent_id in parent_ids.iter() {
                let remaining = remaining_child_counts
                    .get_mut(parent_id)
                    .expect("validated parent object ID");
                *remaining -= 1;
                if *remaining == 0 {
                    ready.push_back(*parent_id);
                }
            }
        }
    }
    if completed_object_count != certificate.objects.len() {
        return Err("well-definedness object graph contains a cycle".to_string());
    }

    let mut reachable_object_ids = HashSet::new();
    let mut pending_object_ids = certificate.root_obj_ids.clone();
    while let Some(object_id) = pending_object_ids.pop() {
        if !reachable_object_ids.insert(object_id) {
            continue;
        }
        let object = objects_by_id
            .get(&object_id)
            .expect("validated reachable object ID");
        pending_object_ids.extend(object.child_uses.iter().map(|child| child.obj_id));
    }
    if reachable_object_ids.len() != certificate.objects.len() {
        return Err(
            "well-definedness certificate contains an object outside its root closure".to_string(),
        );
    }

    let mut target_requirement_keys = HashSet::new();
    for requirement in certificate.target_requirements.iter() {
        if !target_requirement_keys.insert((requirement.source_occurrence_id, requirement.role)) {
            return Err(format!(
                "source occurrence {} repeats target requirement role {:?}",
                requirement.source_occurrence_id.value(),
                requirement.role
            ));
        }
        let object = objects_by_id
            .get(&requirement.well_defined_obj_id)
            .ok_or_else(|| {
                format!(
                    "target requirement cites missing WellDefinedObjId {}",
                    requirement.well_defined_obj_id.value()
                )
            })?;
        let source_use = source_object_uses
            .get(&requirement.source_occurrence_id)
            .ok_or_else(|| {
                format!(
                    "target requirement for source occurrence {} has no exact WD object use",
                    requirement.source_occurrence_id.value()
                )
            })?;
        if source_use.phase != requirement.phase {
            return Err(format!(
                "target requirement for source occurrence {} changed execution phase from {:?} to {:?}",
                requirement.source_occurrence_id.value(),
                source_use.phase,
                requirement.phase
            ));
        }
        if source_use.well_defined_obj_id != requirement.well_defined_obj_id {
            let mut pending = vec![source_use.well_defined_obj_id];
            let mut visited = HashSet::new();
            while let Some(object_id) = pending.pop() {
                if !visited.insert(object_id) {
                    continue;
                }
                let object = objects_by_id
                    .get(&object_id)
                    .expect("validated source-use object closure");
                pending.extend(object.child_uses.iter().map(|child| child.obj_id));
            }
            if !visited.contains(&requirement.well_defined_obj_id) {
                return Err(format!(
                    "target requirement for source occurrence {} cites WellDefinedObjId {}, outside exact object-use closure {}",
                    requirement.source_occurrence_id.value(),
                    requirement.well_defined_obj_id.value(),
                    source_use.well_defined_obj_id.value()
                ));
            }
        }
        if !matches!(object.source_object, Obj::FnObj(_)) {
            return Err(format!(
                "target requirement for source occurrence {} is not owned by a function application",
                requirement.source_occurrence_id.value()
            ));
        }
        let well_defined_fact = facts_by_well_defined_id
            .get(&requirement.well_defined_fact_id)
            .ok_or_else(|| {
                format!(
                    "target requirement cites missing WellDefinedFactId {}",
                    requirement.well_defined_fact_id.value()
                )
            })?;
        if well_defined_fact.expected_proposition.to_string()
            != requirement.expected_proposition.to_string()
        {
            return Err(format!(
                "target requirement changed WellDefinedFactId {}",
                requirement.well_defined_fact_id.value()
            ));
        }
        if !object.target_requirements.iter().any(|owned| {
            owned.role == requirement.role
                && owned.well_defined_fact_id == requirement.well_defined_fact_id
                && owned.expected_proposition.to_string()
                    == requirement.expected_proposition.to_string()
        }) {
            return Err(format!(
                "target requirement is not an edge of WellDefinedObjId {}",
                requirement.well_defined_obj_id.value()
            ));
        }
        used_fact_ids.insert(requirement.well_defined_fact_id);
    }

    for fact_id in facts_by_well_defined_id.keys() {
        if !used_fact_ids.contains(fact_id) {
            return Err(format!(
                "WellDefinedFactId {} is outside every frozen object edge",
                fact_id.value()
            ));
        }
    }

    let mut parameter_fact_ids = HashSet::new();
    for parameter_fact in certificate.parameter_facts.iter() {
        if !parameter_fact_ids.insert(parameter_fact.fact_id) {
            return Err(format!(
                "parameter FactId {} is duplicated in one well-definedness certificate",
                parameter_fact.fact_id.value()
            ));
        }
    }

    Ok(())
}

/// Check that target proof arguments are an exact recipe for the source
/// constructor. This belongs at the frozen-IR boundary: emitters may consume
/// the recipe, but may not be the first component to discover that it was
/// deleted, reindexed, or retargeted.
fn validate_object_target_requirement_recipe(
    object: &LitexToLeanWellDefinednessObjectIr,
    roles: &HashSet<WellDefinednessRequirementRole>,
) -> Result<(), String> {
    let object_id = object.well_defined_obj_id.value();
    let unexpected = |role: WellDefinednessRequirementRole| {
        Err(format!(
            "WellDefinedObjId {object_id} retains incompatible target requirement role {role:?} for `{}`",
            object.source_object
        ))
    };

    for requirement in object.target_requirements.iter() {
        match requirement.role {
            WellDefinednessRequirementRole::BuiltinArgumentMembership { argument_index } => {
                let arguments = arithmetic_arguments(&object.source_object)
                    .ok_or_else(|| unexpected(requirement.role).unwrap_err())?;
                let argument = arguments.get(argument_index).ok_or_else(|| {
                    format!(
                        "WellDefinedObjId {object_id} has out-of-range builtin membership role {argument_index}"
                    )
                })?;
                let Fact::AtomicFact(AtomicFact::InFact(membership)) =
                    &requirement.expected_proposition
                else {
                    return Err(format!(
                        "WellDefinedObjId {object_id} builtin membership role {argument_index} retained a non-membership proposition"
                    ));
                };
                if !objs_equal_with_nested_binder_alpha_equivalence(&membership.element, argument)
                    || !matches!(&membership.set, Obj::StandardSet(StandardSet::C))
                {
                    return Err(format!(
                        "WellDefinedObjId {object_id} builtin membership role {argument_index} changed its exact operand or C carrier"
                    ));
                }
            }
            WellDefinednessRequirementRole::BuiltinArgumentNonzero { argument_index } => {
                let arguments = arithmetic_arguments(&object.source_object)
                    .ok_or_else(|| unexpected(requirement.role).unwrap_err())?;
                let argument = arguments.get(argument_index).ok_or_else(|| {
                    format!(
                        "WellDefinedObjId {object_id} has out-of-range builtin nonzero role {argument_index}"
                    )
                })?;
                if !matches!(object.source_object, Obj::Div(_)) || argument_index != 1 {
                    return unexpected(requirement.role);
                }
                let Fact::AtomicFact(AtomicFact::NotEqualFact(nonzero)) =
                    &requirement.expected_proposition
                else {
                    return Err(format!(
                        "WellDefinedObjId {object_id} builtin nonzero role retained a non-inequality proposition"
                    ));
                };
                let zero: Obj = Number::new("0".to_string()).into();
                if !objs_equal_with_nested_binder_alpha_equivalence(&nonzero.left, argument)
                    || !objs_equal_with_nested_binder_alpha_equivalence(&nonzero.right, &zero)
                {
                    return Err(format!(
                        "WellDefinedObjId {object_id} division nonzero role changed its exact denominator"
                    ));
                }
            }
            WellDefinednessRequirementRole::ConstructorPairwiseDistinct {
                left_index,
                right_index,
            } => {
                let Obj::ListSet(list_set) = &object.source_object else {
                    return unexpected(requirement.role);
                };
                if left_index >= right_index || right_index >= list_set.list.len() {
                    return Err(format!(
                        "WellDefinedObjId {object_id} has reversed or out-of-range pairwise role ({left_index}, {right_index})"
                    ));
                }
                let Fact::AtomicFact(AtomicFact::NotEqualFact(distinct)) =
                    &requirement.expected_proposition
                else {
                    return Err(format!(
                        "WellDefinedObjId {object_id} pairwise role retained a non-inequality proposition"
                    ));
                };
                if !objs_equal_with_nested_binder_alpha_equivalence(
                    &distinct.left,
                    list_set.list[left_index].as_ref(),
                ) || !objs_equal_with_nested_binder_alpha_equivalence(
                    &distinct.right,
                    list_set.list[right_index].as_ref(),
                ) {
                    return Err(format!(
                        "WellDefinedObjId {object_id} pairwise role ({left_index}, {right_index}) changed its ordered entries"
                    ));
                }
            }
            WellDefinednessRequirementRole::FunctionArgumentMembership {
                layer_index,
                parameter_index,
            } => {
                let Obj::FnObj(application) = &object.source_object else {
                    return unexpected(requirement.role);
                };
                let argument = application
                    .body
                    .get(layer_index)
                    .and_then(|layer| layer.get(parameter_index))
                    .ok_or_else(|| {
                        format!(
                            "WellDefinedObjId {object_id} has out-of-range function-membership role ({layer_index}, {parameter_index})"
                        )
                    })?;
                let Fact::AtomicFact(AtomicFact::InFact(membership)) =
                    &requirement.expected_proposition
                else {
                    return Err(format!(
                        "WellDefinedObjId {object_id} function-membership role retained a non-membership proposition"
                    ));
                };
                if !objs_equal_with_nested_binder_alpha_equivalence(
                    &membership.element,
                    argument.as_ref(),
                ) {
                    return Err(format!(
                        "WellDefinedObjId {object_id} function-membership role ({layer_index}, {parameter_index}) changed its exact argument"
                    ));
                }
            }
            WellDefinednessRequirementRole::FunctionDomain { layer_index, .. } => {
                let Obj::FnObj(application) = &object.source_object else {
                    return unexpected(requirement.role);
                };
                if layer_index >= application.body.len() {
                    return Err(format!(
                        "WellDefinedObjId {object_id} has out-of-range function-domain layer {layer_index}"
                    ));
                }
            }
            WellDefinednessRequirementRole::AnonymousFunctionBodyMembership => {
                let Obj::AnonymousFn(function) = &object.source_object else {
                    return unexpected(requirement.role);
                };
                let Fact::AtomicFact(AtomicFact::InFact(membership)) =
                    &requirement.expected_proposition
                else {
                    return Err(format!(
                        "WellDefinedObjId {object_id} anonymous-function closure retained a non-membership proposition"
                    ));
                };
                if !objs_equal_with_nested_binder_alpha_equivalence(
                    &membership.element,
                    function.equal_to.as_ref(),
                ) || !objs_equal_with_nested_binder_alpha_equivalence(
                    &membership.set,
                    function.body.ret_set.as_ref(),
                ) {
                    return Err(format!(
                        "WellDefinedObjId {object_id} anonymous-function closure changed its body or return carrier"
                    ));
                }
            }
            WellDefinednessRequirementRole::AnonymousFunctionBoundParameterSubset {
                parameter_group_index,
                parameter_index,
            } => {
                let Obj::AnonymousFn(function) = &object.source_object else {
                    return unexpected(requirement.role);
                };
                let group = function
                    .body
                    .params_def_with_set
                    .get(parameter_group_index)
                    .ok_or_else(|| {
                        format!(
                            "WellDefinedObjId {object_id} anonymous-function subset route has out-of-range parameter group {parameter_group_index}"
                        )
                    })?;
                let binding = group.params.get(parameter_index).ok_or_else(|| {
                    format!(
                        "WellDefinedObjId {object_id} anonymous-function subset route has out-of-range parameter index {parameter_index}"
                    )
                })?;
                let bound = obj_for_bound_param_in_scope(binding, ParamObjType::FnSet);
                if !objs_equal_with_nested_binder_alpha_equivalence(
                    function.equal_to.as_ref(),
                    &bound,
                ) {
                    return Err(format!(
                        "WellDefinedObjId {object_id} anonymous-function subset route does not target its indexed bound parameter"
                    ));
                }
                let Fact::AtomicFact(AtomicFact::SubsetFact(subset)) =
                    &requirement.expected_proposition
                else {
                    return Err(format!(
                        "WellDefinedObjId {object_id} anonymous-function subset route retained a non-subset proposition"
                    ));
                };
                if !objs_equal_with_nested_binder_alpha_equivalence(&subset.left, group.set_obj())
                    || !objs_equal_with_nested_binder_alpha_equivalence(
                        &subset.right,
                        function.body.ret_set.as_ref(),
                    )
                {
                    return Err(format!(
                        "WellDefinedObjId {object_id} anonymous-function subset route changed its parameter or return carrier"
                    ));
                }
            }
        }
    }

    let expected_roles = match &object.source_object {
        Obj::Add(_) | Obj::Sub(_) | Obj::Mul(_) => HashSet::from([
            WellDefinednessRequirementRole::BuiltinArgumentMembership { argument_index: 0 },
            WellDefinednessRequirementRole::BuiltinArgumentMembership { argument_index: 1 },
        ]),
        Obj::Div(_) => HashSet::from([
            WellDefinednessRequirementRole::BuiltinArgumentMembership { argument_index: 0 },
            WellDefinednessRequirementRole::BuiltinArgumentMembership { argument_index: 1 },
            WellDefinednessRequirementRole::BuiltinArgumentNonzero { argument_index: 1 },
        ]),
        Obj::ListSet(list_set) => {
            let mut expected = HashSet::new();
            for left_index in 0..list_set.list.len() {
                for right_index in left_index + 1..list_set.list.len() {
                    expected.insert(
                        WellDefinednessRequirementRole::ConstructorPairwiseDistinct {
                            left_index,
                            right_index,
                        },
                    );
                }
            }
            expected
        }
        Obj::AnonymousFn(_) => {
            let closure_routes = roles
                .iter()
                .filter(|role| {
                    matches!(
                        role,
                        WellDefinednessRequirementRole::AnonymousFunctionBodyMembership
                            | WellDefinednessRequirementRole::AnonymousFunctionBoundParameterSubset { .. }
                    )
                })
                .count();
            if closure_routes != 1 || roles.len() != 1 {
                return Err(format!(
                    "WellDefinedObjId {object_id} anonymous function requires exactly one checked return-closure route, retained {} roles",
                    roles.len()
                ));
            }
            roles.clone()
        }
        Obj::FnObj(application) => {
            let Some((last_layer_index, last_layer)) =
                application.body.iter().enumerate().next_back()
            else {
                return Err(format!(
                    "WellDefinedObjId {object_id} function application has no source layer"
                ));
            };
            for parameter_index in 0..last_layer.len() {
                let expected = WellDefinednessRequirementRole::FunctionArgumentMembership {
                    layer_index: last_layer_index,
                    parameter_index,
                };
                if !roles.contains(&expected) {
                    return Err(format!(
                        "WellDefinedObjId {object_id} is missing function argument requirement {expected:?}"
                    ));
                }
            }
            return Ok(());
        }
        _ => HashSet::new(),
    };
    if *roles != expected_roles {
        return Err(format!(
            "WellDefinedObjId {object_id} target requirement recipe changed: expected {expected_roles:?}, retained {roles:?}"
        ));
    }
    Ok(())
}

fn validate_scope_reference_chain(
    description: &str,
    scope_ids: &[WellDefinedBinderScopeId],
    scopes_by_id: &HashMap<WellDefinedBinderScopeId, &LitexToLeanWellDefinednessBinderScopeIr>,
) -> Result<(), String> {
    let mut seen = HashSet::new();
    for (index, scope_id) in scope_ids.iter().copied().enumerate() {
        if !seen.insert(scope_id) {
            return Err(format!(
                "{description} repeats WellDefinedBinderScopeId {}",
                scope_id.value()
            ));
        }
        let scope = scopes_by_id.get(&scope_id).ok_or_else(|| {
            format!(
                "{description} cites missing WellDefinedBinderScopeId {}",
                scope_id.value()
            )
        })?;
        if scope.ambient_scope_ids != scope_ids[..index] {
            return Err(format!(
                "{description} has a non-lexical binder scope chain at scope {}",
                scope_id.value()
            ));
        }
    }
    Ok(())
}

fn validate_binder_scope_chain(
    scope_id: WellDefinedBinderScopeId,
    ambient_scope_ids: &[WellDefinedBinderScopeId],
    scopes_by_id: &HashMap<WellDefinedBinderScopeId, &LitexToLeanWellDefinednessBinderScopeIr>,
) -> Result<(), String> {
    if ambient_scope_ids.contains(&scope_id) {
        return Err(format!(
            "WellDefinedBinderScopeId {} contains itself in its ambient chain",
            scope_id.value()
        ));
    }
    validate_scope_reference_chain(
        &format!("WellDefinedBinderScopeId {}", scope_id.value()),
        ambient_scope_ids,
        scopes_by_id,
    )
}

fn validate_binder_scope_recipe(
    scope: &LitexToLeanWellDefinednessBinderScopeIr,
) -> Result<(), String> {
    let scope_id = scope.scope_id.value();
    let Obj::AnonymousFn(function) = &scope.owner_object else {
        return Err(format!(
            "WellDefinedBinderScopeId {scope_id} currently has unsupported non-anonymous owner `{}`",
            scope.owner_object
        ));
    };
    let mut expected_roles = HashSet::new();
    let mut expected_role_order = Vec::new();
    for (parameter_group_index, group) in function.body.params_def_with_set.iter().enumerate() {
        for (parameter_index, binding) in group.params.iter().enumerate() {
            let role = WellDefinedBinderPremiseRole::ParameterMembership {
                parameter_group_index,
                parameter_index,
            };
            expected_roles.insert(role);
            expected_role_order.push(role);
            let premise = scope
                .premises
                .iter()
                .find(|premise| premise.role == role)
                .ok_or_else(|| {
                    format!(
                        "WellDefinedBinderScopeId {scope_id} is missing parameter premise {role:?}"
                    )
                })?;
            if premise.symbol_id != Some(binding.id()) {
                return Err(format!(
                    "WellDefinedBinderScopeId {scope_id} parameter premise {role:?} changed SymbolId"
                ));
            }
            let Fact::AtomicFact(AtomicFact::InFact(membership)) = &premise.proposition else {
                return Err(format!(
                    "WellDefinedBinderScopeId {scope_id} parameter premise {role:?} is not a membership"
                ));
            };
            let bound = obj_for_bound_param_in_scope(binding, ParamObjType::FnSet);
            if !objs_equal_with_nested_binder_alpha_equivalence(&membership.element, &bound)
                || !objs_equal_with_nested_binder_alpha_equivalence(
                    &membership.set,
                    group.set_obj(),
                )
            {
                return Err(format!(
                    "WellDefinedBinderScopeId {scope_id} parameter premise {role:?} changed its bound object or carrier"
                ));
            }
        }
    }
    for (domain_index, domain) in function.body.dom_facts.iter().enumerate() {
        let role = WellDefinedBinderPremiseRole::Domain { domain_index };
        expected_roles.insert(role);
        expected_role_order.push(role);
        let premise = scope
            .premises
            .iter()
            .find(|premise| premise.role == role)
            .ok_or_else(|| {
                format!("WellDefinedBinderScopeId {scope_id} is missing domain premise {role:?}")
            })?;
        if premise.symbol_id.is_some()
            || premise.proposition.to_string() != Fact::from(domain.clone()).to_string()
        {
            return Err(format!(
                "WellDefinedBinderScopeId {scope_id} domain premise {role:?} changed its exact proposition"
            ));
        }
    }
    let retained_roles = scope
        .premises
        .iter()
        .map(|premise| premise.role)
        .collect::<HashSet<_>>();
    if retained_roles != expected_roles {
        return Err(format!(
            "WellDefinedBinderScopeId {scope_id} changed its binder premise recipe: expected {expected_roles:?}, retained {retained_roles:?}"
        ));
    }
    let retained_role_order = scope
        .premises
        .iter()
        .map(|premise| premise.role)
        .collect::<Vec<_>>();
    if retained_role_order != expected_role_order {
        return Err(format!(
            "WellDefinedBinderScopeId {scope_id} changed binder premise order: expected {expected_role_order:?}, retained {retained_role_order:?}"
        ));
    }

    let direct_fact_ids = scope
        .premises
        .iter()
        .map(|premise| premise.fact_id)
        .collect::<HashSet<_>>();
    let mut inferred_fact_ids = HashSet::new();
    for inferred in scope.inferred_premises.iter() {
        let Some(fact_id) = inferred.fact_id else {
            return Err(format!(
                "WellDefinedBinderScopeId {scope_id} retained an inferred premise without FactId"
            ));
        };
        if direct_fact_ids.contains(&fact_id) || !inferred_fact_ids.insert(fact_id) {
            return Err(format!(
                "WellDefinedBinderScopeId {scope_id} repeats local FactId {}",
                fact_id.value()
            ));
        }
    }
    Ok(())
}

fn arithmetic_arguments(object: &Obj) -> Option<[&Obj; 2]> {
    match object {
        Obj::Add(value) => Some([value.left.as_ref(), value.right.as_ref()]),
        Obj::Sub(value) => Some([value.left.as_ref(), value.right.as_ref()]),
        Obj::Mul(value) => Some([value.left.as_ref(), value.right.as_ref()]),
        Obj::Div(value) => Some([value.left.as_ref(), value.right.as_ref()]),
        _ => None,
    }
}

/// Resolve only target-constructor value slots. Verification dependencies are
/// deliberately excluded: they preserve Litex's audit trace but may never be
/// substituted into a Lean constructor argument.
fn expected_construction_child(
    parent: &Obj,
    role: WellDefinedObjChildRole,
) -> Result<Option<Obj>, String> {
    let invalid = || {
        Err(format!(
            "object `{parent}` cannot own construction-child role {role:?}"
        ))
    };
    match role {
        WellDefinedObjChildRole::VerificationDependency { .. } => Ok(None),
        WellDefinedObjChildRole::FunctionPrefix {
            through_layer_index,
        } => match parent {
            Obj::FnObj(application) if through_layer_index < application.body.len() => {
                Ok(Some(application.prefix_obj(through_layer_index + 1)))
            }
            _ => invalid(),
        },
        WellDefinedObjChildRole::FunctionHead => match parent {
            Obj::FnObj(application) => Ok(Some(application.head.as_ref().clone().into())),
            _ => invalid(),
        },
        WellDefinedObjChildRole::FunctionArgument {
            layer_index,
            argument_index,
        } => match parent {
            Obj::FnObj(application) => application
                .body
                .get(layer_index)
                .and_then(|layer| layer.get(argument_index))
                .map(|argument| Some(argument.as_ref().clone()))
                .ok_or_else(|| {
                    format!(
                        "function application `{parent}` has no argument at layer {layer_index}, index {argument_index}"
                    )
                }),
            _ => invalid(),
        },
        WellDefinedObjChildRole::BuiltinArgument { argument_index } => {
            let arguments = match parent {
                Obj::Add(value) => [&value.left, &value.right],
                Obj::Sub(value) => [&value.left, &value.right],
                Obj::Mul(value) => [&value.left, &value.right],
                Obj::Div(value) => [&value.left, &value.right],
                _ => return invalid(),
            };
            arguments
                .get(argument_index)
                .map(|argument| Some(argument.as_ref().clone()))
                .ok_or_else(|| {
                    format!(
                        "builtin object `{parent}` has no argument at index {argument_index}"
                    )
                })
        }
        WellDefinedObjChildRole::ConstructorArgument { argument_index } => {
            parent
                .well_definedness_constructor_argument(argument_index)
                .map(Some)
                .ok_or_else(|| {
                    format!(
                        "object `{parent}` has no positional constructor argument at index {argument_index}"
                    )
                })
        }
        WellDefinedObjChildRole::BinderParameterCarrier {
            parameter_group_index,
        } => {
            let carrier = match parent {
                Obj::FnSet(value) => value
                    .body
                    .params_def_with_set
                    .get(parameter_group_index)
                    .map(ParamGroupWithSet::set_obj),
                Obj::AnonymousFn(value) => value
                    .body
                    .params_def_with_set
                    .get(parameter_group_index)
                    .map(ParamGroupWithSet::set_obj),
                Obj::SetBuilder(value) if parameter_group_index == 0 => {
                    Some(value.param_set.as_ref())
                }
                _ => return invalid(),
            };
            carrier
                .map(|carrier| Some(carrier.clone()))
                .ok_or_else(|| {
                    format!(
                        "binder object `{parent}` has no parameter carrier at group {parameter_group_index}"
                    )
                })
        }
        WellDefinedObjChildRole::BinderReturnCarrier => match parent {
            Obj::FnSet(value) => Ok(Some(value.body.ret_set.as_ref().clone())),
            Obj::AnonymousFn(value) => Ok(Some(value.body.ret_set.as_ref().clone())),
            _ => invalid(),
        },
        WellDefinedObjChildRole::BinderBody => match parent {
            Obj::AnonymousFn(value) => Ok(Some(value.equal_to.as_ref().clone())),
            _ => invalid(),
        },
    }
}

fn expected_construction_roles(parent: &Obj) -> Vec<WellDefinedObjChildRole> {
    match parent {
        Obj::FnObj(application) => {
            let Some((last_layer_index, last_layer)) =
                application.body.iter().enumerate().next_back()
            else {
                return Vec::new();
            };
            let mut roles = Vec::new();
            if last_layer_index == 0 {
                if matches!(
                    application.head.as_ref(),
                    FnObjHead::AnonymousFnLiteral(_)
                        | FnObjHead::FiniteSeqListObj(_)
                        | FnObjHead::MatrixOperator(_)
                        | FnObjHead::ObjAsStructInstanceWithFieldAccess(_)
                        | FnObjHead::InstantiatedTemplateObj(_)
                ) {
                    roles.push(WellDefinedObjChildRole::FunctionHead);
                }
            } else {
                roles.push(WellDefinedObjChildRole::FunctionPrefix {
                    through_layer_index: last_layer_index - 1,
                });
            }
            roles.extend(last_layer.iter().enumerate().map(|(argument_index, _)| {
                WellDefinedObjChildRole::FunctionArgument {
                    layer_index: last_layer_index,
                    argument_index,
                }
            }));
            roles
        }
        Obj::Add(_) | Obj::Sub(_) | Obj::Mul(_) | Obj::Div(_) => (0..2)
            .map(|argument_index| WellDefinedObjChildRole::BuiltinArgument { argument_index })
            .collect(),
        Obj::FnSet(value) => {
            let mut roles = value
                .body
                .params_def_with_set
                .iter()
                .enumerate()
                .map(
                    |(parameter_group_index, _)| WellDefinedObjChildRole::BinderParameterCarrier {
                        parameter_group_index,
                    },
                )
                .collect::<Vec<_>>();
            roles.push(WellDefinedObjChildRole::BinderReturnCarrier);
            roles
        }
        Obj::AnonymousFn(value) => {
            let mut roles = value
                .body
                .params_def_with_set
                .iter()
                .enumerate()
                .map(
                    |(parameter_group_index, _)| WellDefinedObjChildRole::BinderParameterCarrier {
                        parameter_group_index,
                    },
                )
                .collect::<Vec<_>>();
            roles.push(WellDefinedObjChildRole::BinderReturnCarrier);
            roles.push(WellDefinedObjChildRole::BinderBody);
            roles
        }
        Obj::SetBuilder(_) => vec![WellDefinedObjChildRole::BinderParameterCarrier {
            parameter_group_index: 0,
        }],
        _ => {
            let mut roles = Vec::new();
            let mut argument_index = 0;
            while parent
                .well_definedness_constructor_argument(argument_index)
                .is_some()
            {
                roles.push(WellDefinedObjChildRole::ConstructorArgument { argument_index });
                argument_index += 1;
            }
            roles
        }
    }
}
