//! Range endpoints, literal values, and for-range parameter results.

use super::super::*;

pub(in super::super) fn render_forall_domain_intro_suffix(forall: &ForallFact) -> String {
    (1..=forall.dom_facts.len())
        .map(|index| format!(" __domain{index}"))
        .collect::<String>()
}

pub(in super::super) fn obj_from_closed_or_half_open_range(range: &ClosedRangeOrRange) -> Obj {
    match range {
        ClosedRangeOrRange::Range(range) => range.clone().into(),
        ClosedRangeOrRange::ClosedRange(range) => range.clone().into(),
    }
}

pub(in super::super) fn closed_or_half_open_range_endpoints(
    range: &ClosedRangeOrRange,
) -> (&Obj, &Obj) {
    match range {
        ClosedRangeOrRange::Range(range) => (range.start.as_ref(), range.end.as_ref()),
        ClosedRangeOrRange::ClosedRange(range) => (range.start.as_ref(), range.end.as_ref()),
    }
}

pub(in super::super) fn literal_integer_values_for_range(
    range: &ClosedRangeOrRange,
) -> Result<Option<Vec<String>>, String> {
    let (start, end) = closed_or_half_open_range_endpoints(range);
    let (Obj::Number(start), Obj::Number(end)) = (start, end) else {
        return Ok(None);
    };
    let start = start
        .normalized_value
        .parse::<i128>()
        .map_err(|_| "integer-range start is not a literal integer".to_string())?;
    let end = end
        .normalized_value
        .parse::<i128>()
        .map_err(|_| "integer-range end is not a literal integer".to_string())?;
    let closed = matches!(range, ClosedRangeOrRange::ClosedRange(_));
    if (closed && start > end) || (!closed && start >= end) {
        return Ok(Some(Vec::new()));
    }
    let final_value = if closed {
        end
    } else {
        end.checked_sub(1)
            .ok_or_else(|| "half-open integer-range boundary underflowed i128".to_string())?
    };
    let mut values = Vec::new();
    let mut current = start;
    loop {
        values.push(current.to_string());
        if current == final_value {
            break;
        }
        current = current
            .checked_add(1)
            .ok_or_else(|| "integer-range enumeration overflowed i128".to_string())?;
    }
    Ok(Some(values))
}

pub(in super::super) fn validate_by_for_range_parameter_result(
    result: &SuccessVerifyByForRangeParameterResult,
) -> Result<(), String> {
    let (source_start, source_end, closed) = match &result.range {
        ClosedRangeOrRange::Range(range) => (range.start.as_ref(), range.end.as_ref(), false),
        ClosedRangeOrRange::ClosedRange(range) => (range.start.as_ref(), range.end.as_ref(), true),
    };
    let expected_start = LeanTargetObjectRepresentation::Number {
        normalized_value: result.evaluated_start.clone(),
    };
    let expected_end = LeanTargetObjectRepresentation::Number {
        normalized_value: result.evaluated_end.clone(),
    };
    if LeanTargetObjectRepresentation::lower(source_start)? != expected_start
        || LeanTargetObjectRepresentation::lower(source_end)? != expected_end
    {
        return Err(format!(
            "by-for parameter `{}` needs retained endpoint-normalization evidence before a non-literal range may be compiled",
            result.parameter
        ));
    }
    let start = result
        .evaluated_start
        .parse::<i128>()
        .map_err(|_| "by-for evaluated start is not an integer".to_string())?;
    let end = result
        .evaluated_end
        .parse::<i128>()
        .map_err(|_| "by-for evaluated end is not an integer".to_string())?;
    let is_empty = if closed { start > end } else { start >= end };
    if is_empty {
        if result.enumerated_values.is_empty() {
            return Ok(());
        }
        return Err("by-for empty range retained assignments".into());
    }
    let right_boundary = if closed {
        end
    } else {
        end.checked_sub(1)
            .ok_or_else(|| "by-for half-open range boundary underflowed i128".to_string())?
    };
    let mut expected_value = start;
    for retained in &result.enumerated_values {
        if retained.parse::<i128>().ok() != Some(expected_value) {
            return Err(format!(
                "by-for parameter `{}` changed its ordered evaluated values",
                result.parameter
            ));
        }
        if expected_value == right_boundary {
            break;
        }
        expected_value = expected_value
            .checked_add(1)
            .ok_or_else(|| "by-for evaluated range overflowed i128".to_string())?;
    }
    if result
        .enumerated_values
        .last()
        .and_then(|value| value.parse::<i128>().ok())
        != Some(right_boundary)
    {
        return Err(format!(
            "by-for parameter `{}` lost one or more evaluated values",
            result.parameter
        ));
    }
    Ok(())
}
