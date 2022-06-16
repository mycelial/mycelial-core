//! List CRDT with delta state support
//!
//! # Example
//!
//! ```rust
//! use mycelial_crdt::list::{Value, List};
//!
//! let mut list_0 = List::new(0);
//! let mut list_1 = List::new(1);
//!
//! list_0.append("hello".into());
//! list_1.append("world!".into());
//!
//! let diff_01 = list_0.diff(list_1.vclock());
//! let diff_10 = list_1.diff(list_0.vclock());
//!
//! list_0.apply(&diff_10);
//! list_1.apply(&diff_01);
//!
//! assert_eq!(list_0.to_vec(), vec!["hello", "world!"]);
//! assert_eq!(list_1.to_vec(), vec!["hello", "world!"]);
//! ```

use crate::vclock::{VClock, VClockDiff};
use num::rational::Ratio;
use num::BigInt;
use serde::{Deserialize, Serialize};
use std::cmp::{Ord, PartialOrd};
use std::collections::BTreeMap;

/// Uniquely identifies operation for a given process
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Serialize, Deserialize)]
pub struct Key<T> {
    id: T,
    process: u64,
    op: u64,
}

impl<T: Clone> Key<T> {
    /// Construct new key for a given process and operation number
    pub fn new<R: Into<T>>(id: R, process: u64, op: u64) -> Self {
        Self {
            id: id.into(),
            process,
            op,
        }
    }
}

/// List Key trait
pub trait ListKey: Sized + Ord + Eq + Clone {
    /// Defines behaviour of the list by defining implementation of function `between`
    fn between(
        process: u64,
        op: u64,
        left: Option<&Self>,
        right: Option<&Self>,
    ) -> Result<Self, ListError>;

    /// Check is key is arbitraty precision
    fn is_arbitraty_precision() -> bool;
}

impl ListKey for Key<Ratio<BigInt>> {
    /// Create new key between left and right keys
    fn between(
        process: u64,
        op: u64,
        left: Option<&Self>,
        right: Option<&Self>,
    ) -> Result<Self, ListError> {
        let id = match (left, right) {
            (None, Some(Key { id, .. })) => id - BigInt::from(1_i64),
            (Some(Key { id: id_left, .. }), Some(Key { id: id_right, .. })) => {
                (id_left + id_right) / BigInt::from(2_i64)
            }
            (Some(Key { id, .. }), None) => id + BigInt::from(1_i64),
            (None, None) => Ratio::new_raw(BigInt::from(0), BigInt::from(1)),
        };
        Ok(Key { id, process, op })
    }
    fn is_arbitraty_precision() -> bool {
        true
    }
}

impl ListKey for Key<i64> {
    fn between(
        process: u64,
        op: u64,
        left: Option<&Self>,
        right: Option<&Self>,
    ) -> Result<Self, ListError> {
        let id: i64 = match (left, right) {
            (None, None) => 0,
            (None, Some(Key { id, .. })) => id - 1,
            (Some(Key { id, .. }), None) => id + 1,
            (Some(_), Some(_)) => return Err(ListError::AppendOnly),
        };
        Ok(Key { id, process, op })
    }

    fn is_arbitraty_precision() -> bool {
        false
    }
}

/// Value represents data types, which list can currently store
///
/// Structure is not full and probably will be expanded in near future, hence non_exhaustive
#[non_exhaustive]
#[derive(Debug, PartialEq, Clone, Serialize, Deserialize)]
pub enum Value<Key> {
    /// String
    Str(String),

    /// Bool
    Bool(bool),

    /// Float
    Float(f64),

    /// Vector os Value
    Vec(Vec<Value<Key>>),

    /// Tombstone, for deletion indication
    Tombstone(Key),

    /// Empty value, never actually appears in the List itself
    ///
    /// Required to preserve sequence of vclock operations in diff
    Empty,
}

impl<Key: Eq> Eq for Value<Key> {}

impl<Key> From<&str> for Value<Key> {
    fn from(value: &str) -> Self {
        Value::Str(value.into())
    }
}

impl<Key> From<String> for Value<Key> {
    fn from(value: String) -> Self {
        Value::Str(value)
    }
}

impl<Key> From<f64> for Value<Key> {
    fn from(value: f64) -> Self {
        Value::Float(value)
    }
}

impl<Key> From<bool> for Value<Key> {
    fn from(value: bool) -> Self {
        Value::Bool(value)
    }
}

impl<Key> PartialEq<str> for Value<Key> {
    fn eq(&self, other: &str) -> bool {
        match self {
            Self::Str(s) => s.as_str().eq(other),
            _ => false,
        }
    }
}

impl<Key> Value<Key> {
    fn visible(&self) -> bool {
        !matches!(self, Value::Tombstone(_) | Value::Empty)
    }
}

struct Hooks<Key> {
    pub update: Option<Box<dyn Fn(&Op<Key>)>>,
    pub apply: Option<Box<dyn Fn()>>,
}

impl<Key> std::fmt::Debug for Hooks<Key> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let update = if self.update.is_some() {
            "Some(..)"
        } else {
            "None"
        };
        let apply = if self.apply.is_some() {
            "Some(..)"
        } else {
            "None"
        };
        write!(f, "Hooks{{ update: {}, apply: {}}}", update, apply)
    }
}

impl<Key> Hooks<Key> {
    fn new() -> Self {
        Self {
            update: None,
            apply: None,
        }
    }

    fn set_on_update(&mut self, hook: Box<dyn Fn(&Op<Key>)>) {
        self.update = Some(hook)
    }

    fn unset_on_update(&mut self) {
        self.update = None
    }

    fn set_on_apply(&mut self, hook: Box<dyn Fn()>) {
        self.apply = Some(hook)
    }

    fn unset_on_apply(&mut self) {
        self.apply = None
    }
}

/// Op represents operation over list
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize, Clone)]
pub struct Op<Key> {
    /// Op key
    pub key: Key,

    /// Op value
    pub value: Value<Key>,
}

/// List Error
#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub enum ListError {
    /// Apply operation failed due to missing elements in provided sequence
    OutOfOrder {
        /// Id of the process which owns the list
        process: u64,
        /// Current clock for a process
        current_clock: u64,
        /// Operation clock
        operation_clock: u64,
    },
    /// Insertion failure due to out of bounds index
    OutOfBounds,
    /// Error occurs in append-only list when insert is not append or prepend
    AppendOnly,
}

impl std::fmt::Display for ListError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl std::error::Error for ListError {}

/// List
#[derive(Debug)]
pub struct GenericList<Key> {
    /// process id
    process: u64,
    vclock: VClock,
    data: BTreeMap<Key, Value<Key>>,
    hooks: Hooks<Key>,
}

unsafe impl<Key> Send for GenericList<Key> {}

impl<T> GenericList<Key<T>>
where
    Key<T>: ListKey,
    T: Clone,
{
    /// Create new list
    ///
    /// Process is a unique identifier among peers, part of vclock
    pub fn new(process: u64) -> Self {
        Self {
            process,
            vclock: VClock::new(),
            data: BTreeMap::new(),
            hooks: Hooks::new(),
        }
    }

    /// Set on update hook
    ///
    /// Whenever local update happens, hook will be invoked
    /// Only 1 hook can be current set
    pub fn set_on_update(&mut self, hook: Box<dyn Fn(&Op<Key<T>>)>) {
        self.hooks.set_on_update(hook)
    }

    /// Unset on update hook
    pub fn unset_on_update(&mut self) {
        self.hooks.unset_on_update()
    }

    /// Set on apply hook
    ///
    /// Whenever remote operations gets applied, hook will be invoked
    /// Only 1 hook can be current set
    pub fn set_on_apply(&mut self, hook: Box<dyn Fn()>) {
        self.hooks.set_on_apply(hook)
    }

    /// Unset on apply hook
    pub fn unset_on_apply(&mut self) {
        self.hooks.unset_on_apply()
    }

    /// Insert value at index
    pub fn insert(&mut self, index: usize, value: Value<Key<T>>) -> Result<(), ListError>
    where
        Key<T>: ListKey,
    {
        let mut keys = self.data.keys();
        let (left, right) = match index {
            index if index > self.data.len() => return Err(ListError::OutOfBounds),
            index if index == 0 => (None, keys.next()),
            index if index == self.data.len() => (keys.nth(self.data.len() - 1), None),
            index => {
                let left = (&mut keys).nth(index - 1);
                let right = keys.next();
                (left, right)
            }
        };
        let key = Key::between(
            self.process,
            self.vclock.next_value(self.process),
            left,
            right,
        )?;
        self.on_update(&key, &value);
        self.insert_key(key, value);
        Ok(())
    }

    /// Delete value at index
    pub fn delete(&mut self, index: usize) -> Result<(), ListError> {
        let key = match self
            .data
            .iter()
            .filter(|(_, value)| value.visible())
            .map(|x| x.0)
            .nth(index)
        {
            None => return Err(ListError::OutOfBounds),
            Some(key) => key,
        };
        let tombstone_key = Key::new(
            key.id.clone(),
            self.process,
            self.vclock.next_value(self.process),
        );
        let value = Value::Tombstone(key.clone());
        self.on_update(&tombstone_key, &value);
        self.insert_key(tombstone_key, value);
        Ok(())
    }

    /// Apply operations generated by peers
    ///
    /// Operation applications are idemponent. If an operation number is less than the current vclock for the
    /// process which generated the operation, it will be skipped.
    ///
    /// Gaps in operations are not allowed and will trigger an error.
    pub fn apply(&mut self, ops: &[Op<Key<T>>]) -> Result<(), ListError> {
        let mut applied = 0;

        for op in ops {
            let op_key = op.key.clone();
            match self.vclock.get_clock(op_key.process) {
                clock if clock >= op_key.op => {
                    // this op was already seen
                    continue;
                }
                clock if clock + 1 != op_key.op => {
                    // out of order operation
                    return Err(ListError::OutOfOrder {
                        process: op_key.process,
                        current_clock: clock,
                        operation_clock: op_key.op,
                    });
                }
                _ => (),
            };
            applied += 1;
            self.insert_key(op_key, op.value.clone())
        }

        match (applied, &self.hooks.apply) {
            (0, _) => (),
            (_, None) => (),
            (_, Some(hook)) => hook(),
        }
        Ok(())
    }

    /// Append value at the end
    pub fn append(&mut self, value: Value<Key<T>>) -> Result<(), ListError> {
        self.insert(self.data.len(), value)
    }

    /// Insert value at the start
    pub fn prepend(&mut self, value: Value<Key<T>>) -> Result<(), ListError> {
        self.insert(0, value)
    }

    /// Build vector of values
    pub fn to_vec(&self) -> Vec<&Value<Key<T>>> {
        self.iter().collect()
    }

    /// Return iterator over stored elements
    pub fn iter(&self) -> impl Iterator<Item = &Value<Key<T>>> {
        self.data.iter().map(|x| x.1).filter(|x| x.visible())
    }

    /// Share own vclock state
    pub fn vclock(&self) -> &VClock {
        &self.vclock
    }

    /// Calculate diff
    pub fn diff(&self, other: &VClock) -> Vec<Op<Key<T>>> {
        let vdiff: VClockDiff = (self.vclock(), other).into();
        let mut ops: Vec<Op<Key<T>>> = Vec::new();
        for (key, value) in self.data.iter() {
            // check if peer already seen that key
            match vdiff.get_range(key.process) {
                Some((start, end)) if key.op > start && key.op <= end => (),
                _ => continue,
            };

            // check if peer has seen the key which is being held by given tombstone
            if let Value::Tombstone(tombstone_key) = value {
                // if peer hasn't seen the insert which is being deleted, then generate an empty value to preserve
                // sequence of operations
                match vdiff.get_range(tombstone_key.process) {
                    Some((start, end)) if tombstone_key.op > start && tombstone_key.op <= end => {
                        ops.push(Op {
                            key: tombstone_key.clone(),
                            value: Value::Empty,
                        });
                    }
                    _ => (),
                }
            }
            ops.push(Op {
                key: key.clone(),
                value: value.clone(),
            })
        }
        ops.sort_by(|left, right| left.key.op.cmp(&right.key.op));
        ops
    }

    /// Get size of stored data (without tombstones)
    pub fn size(&self) -> usize {
        // FIXME: add list metrics to avoid scan
        self.data.values().filter(|x| x.visible()).count()
    }

    fn insert_key(&mut self, key: Key<T>, value: Value<Key<T>>) {
        self.vclock.inc(key.process);
        match value {
            Value::Tombstone(ref key) => {
                self.data.remove(key);
            }
            Value::Empty => return,
            _ => (),
        }
        self.data.insert(key, value);
    }

    fn on_update(&self, key: &Key<T>, value: &Value<Key<T>>) {
        if let Some(ref u) = self.hooks.update {
            u(&Op {
                key: key.clone(),
                value: value.clone(),
            })
        }
    }
}

/// General purpose List, supports inserts at any position
pub type List = GenericList<Key<Ratio<BigInt>>>;

/// Append only list, same as List except allows only prepend & append operations
pub type AppendOnlyList = GenericList<Key<i64>>;
