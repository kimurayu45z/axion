use std::collections::HashMap;

use axion_resolve::def_id::DefId;

/// The state of a variable during borrow checking.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VarState {
    /// Freshly bound or reassigned, not moved or borrowed.
    Owned,
    /// Ownership transferred; cannot be used.
    Moved,
    /// Immutable borrow active (count tracked).
    Borrowed(u32),
    /// Mutable borrow active (exclusive).
    BorrowedMut,
}

/// Per-scope state map tracking variable states.
#[derive(Debug, Clone)]
pub struct StateMap {
    /// DefId → current VarState.
    pub states: HashMap<DefId, VarState>,
    /// DefId → whether the variable was declared as `mut`.
    pub mutability: HashMap<DefId, bool>,
}

impl StateMap {
    pub fn new() -> Self {
        Self {
            states: HashMap::new(),
            mutability: HashMap::new(),
        }
    }

    /// Register a new variable as Owned.
    pub fn declare(&mut self, def_id: DefId, is_mut: bool) {
        self.states.insert(def_id, VarState::Owned);
        self.mutability.insert(def_id, is_mut);
    }

    /// Get the current state of a variable.
    pub fn get(&self, def_id: &DefId) -> Option<&VarState> {
        self.states.get(def_id)
    }

    /// Set the state of a variable.
    pub fn set(&mut self, def_id: DefId, state: VarState) {
        self.states.insert(def_id, state);
    }

    /// Check if a variable was declared as `mut`.
    pub fn is_mut(&self, def_id: &DefId) -> bool {
        self.mutability.get(def_id).copied().unwrap_or(false)
    }

    /// Take a snapshot of the current state (for scope restoration).
    pub fn snapshot(&self) -> HashMap<DefId, VarState> {
        self.states.clone()
    }

    /// Restore borrow states from a snapshot (borrows end at scope exit).
    /// Moved states are preserved (moves are permanent).
    pub fn restore_borrows(&mut self, snapshot: &HashMap<DefId, VarState>) {
        for (def_id, old_state) in snapshot {
            if let Some(current) = self.states.get(def_id) {
                match current {
                    VarState::Borrowed(_) | VarState::BorrowedMut => {
                        // Borrows end at scope exit — restore to pre-scope state.
                        self.states.insert(*def_id, old_state.clone());
                    }
                    VarState::Moved => {
                        // Moves are permanent.
                    }
                    VarState::Owned => {
                        // Variable may have been reassigned; keep current.
                    }
                }
            }
        }
    }

    /// Merge two branch states (e.g. if/else). If either branch moved a variable,
    /// it's considered moved after the merge.
    pub fn merge_branches(
        &mut self,
        then_states: &HashMap<DefId, VarState>,
        else_states: &HashMap<DefId, VarState>,
    ) {
        for (def_id, then_state) in then_states {
            let else_state = else_states.get(def_id);
            let merged = match (then_state, else_state) {
                (VarState::Moved, _) | (_, Some(VarState::Moved)) => VarState::Moved,
                _ => then_state.clone(),
            };
            self.states.insert(*def_id, merged);
        }
    }
}
