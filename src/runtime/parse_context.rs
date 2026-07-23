use crate::prelude::*;
use std::collections::HashMap;

#[derive(Clone)]
pub struct ScopeFrame {
    pub bindings: Vec<SymbolBinding>,
    pub reused_names: Vec<String>,
}

impl ScopeFrame {
    pub fn new(bindings: Vec<SymbolBinding>) -> Self {
        ScopeFrame {
            bindings,
            reused_names: vec![],
        }
    }

    pub fn new_reused(reused_names: Vec<String>) -> Self {
        ScopeFrame {
            bindings: vec![],
            reused_names,
        }
    }
}

#[derive(Clone)]
pub struct ParseContext {
    pub free_params: FreeParamCollection,
    pub local_binding_scope_depth: usize,
    pub scope_frames: Vec<ScopeFrame>,
    pub template_instance_bindings: HashMap<String, SymbolBinding>,
}

impl ParseContext {
    pub fn new() -> Self {
        ParseContext {
            free_params: FreeParamCollection::new(),
            local_binding_scope_depth: 0,
            scope_frames: vec![],
            template_instance_bindings: HashMap::new(),
        }
    }

    pub fn clear(&mut self) {
        self.free_params.clear();
        self.local_binding_scope_depth = 0;
        self.scope_frames.clear();
        self.template_instance_bindings.clear();
    }

    pub fn active_binding(&self, name: &str) -> Option<&SymbolBinding> {
        self.scope_frames
            .iter()
            .rev()
            .flat_map(|frame| frame.bindings.iter().rev())
            .find(|binding| binding.name() == name)
    }

    pub fn push_scope_frame(&mut self, bindings: Vec<SymbolBinding>) {
        self.scope_frames.push(ScopeFrame::new(bindings));
    }

    pub fn push_reused_scope_frame(&mut self, names: Vec<String>) {
        self.scope_frames.push(ScopeFrame::new_reused(names));
    }

    pub fn remove_bindings(&mut self, names: &[String]) {
        for name in names {
            let mut removed = false;
            for frame in self.scope_frames.iter_mut().rev() {
                if let Some(index) = frame
                    .reused_names
                    .iter()
                    .rposition(|reused_name| reused_name == name)
                {
                    frame.reused_names.remove(index);
                    removed = true;
                    break;
                }
                if let Some(index) = frame
                    .bindings
                    .iter()
                    .rposition(|binding| binding.name() == name)
                {
                    frame.bindings.remove(index);
                    removed = true;
                    break;
                }
            }
            debug_assert!(removed, "parse binding `{}` should be active", name);
        }
        self.scope_frames
            .retain(|frame| !frame.bindings.is_empty() || !frame.reused_names.is_empty());
    }
}
