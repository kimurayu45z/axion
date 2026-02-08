use std::collections::HashMap;

use crate::def_id::DefId;

/// Unique identifier for a scope.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ScopeId(pub u32);

/// What kind of syntactic construct introduced this scope.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScopeKind {
    Module,
    Function,
    Block,
    MatchArm,
    ForLoop,
    Closure,
    HandleArm,
}

/// A single lexical scope with dual namespaces (value + type).
#[derive(Debug, Clone)]
pub struct Scope {
    pub id: ScopeId,
    pub kind: ScopeKind,
    pub parent: Option<ScopeId>,
    /// Value namespace: variables, functions, parameters.
    pub values: HashMap<String, DefId>,
    /// Type namespace: types, interfaces, type parameters.
    pub types: HashMap<String, DefId>,
}

/// The full scope hierarchy for a compilation unit.
#[derive(Debug)]
pub struct ScopeTree {
    scopes: Vec<Scope>,
}

impl ScopeTree {
    pub fn new() -> Self {
        Self { scopes: Vec::new() }
    }

    /// Create a new scope and return its id.
    pub fn push_scope(&mut self, kind: ScopeKind, parent: Option<ScopeId>) -> ScopeId {
        let id = ScopeId(self.scopes.len() as u32);
        self.scopes.push(Scope {
            id,
            kind,
            parent,
            values: HashMap::new(),
            types: HashMap::new(),
        });
        id
    }

    pub fn scope(&self, id: ScopeId) -> &Scope {
        &self.scopes[id.0 as usize]
    }

    pub fn scope_mut(&mut self, id: ScopeId) -> &mut Scope {
        &mut self.scopes[id.0 as usize]
    }

    /// Look up a name in the value namespace, walking up the parent chain.
    pub fn lookup_value(&self, scope: ScopeId, name: &str) -> Option<DefId> {
        let s = self.scope(scope);
        if let Some(&def) = s.values.get(name) {
            return Some(def);
        }
        if let Some(parent) = s.parent {
            return self.lookup_value(parent, name);
        }
        None
    }

    /// Look up a name in the type namespace, walking up the parent chain.
    pub fn lookup_type(&self, scope: ScopeId, name: &str) -> Option<DefId> {
        let s = self.scope(scope);
        if let Some(&def) = s.types.get(name) {
            return Some(def);
        }
        if let Some(parent) = s.parent {
            return self.lookup_type(parent, name);
        }
        None
    }

    /// Insert a value binding into the given scope.
    pub fn insert_value(&mut self, scope: ScopeId, name: String, def_id: DefId) -> Option<DefId> {
        self.scope_mut(scope).values.insert(name, def_id)
    }

    /// Insert a type binding into the given scope.
    pub fn insert_type(&mut self, scope: ScopeId, name: String, def_id: DefId) -> Option<DefId> {
        self.scope_mut(scope).types.insert(name, def_id)
    }

    pub fn scopes(&self) -> &[Scope] {
        &self.scopes
    }
}
