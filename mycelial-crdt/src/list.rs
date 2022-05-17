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
use std::cmp::{Ord, Ordering, PartialOrd};
use std::collections::BTreeMap;

/// Uniquely identifies operation for a given process
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Serialize, Deserialize)]
pub struct Key {
    id: Ratio<BigInt>,
    process: u64,
    op: u64,
}

impl Key {
    /// Construct new key for a given process and operation number
    pub fn new<T: Into<Ratio<BigInt>>>(id: T, process: u64, op: u64) -> Self {
        Self {
            id: id.into(),
            process,
            op,
        }
    }

    /// Create new key between left and right keys
    pub fn between(process: u64, op: u64, left: Option<&Key>, right: Option<&Key>) -> Self {
        let id = match (left, right) {
            (None, Some(Key { id, .. })) => id - BigInt::from(1_i64),
            (Some(Key { id: id_left, .. }), Some(Key { id: id_right, .. })) => {
                (id_left + id_right) / BigInt::from(2_i64)
            }
            (Some(Key { id, .. }), None) => id + BigInt::from(1_i64),
            (None, None) => Ratio::new_raw(BigInt::from(0), BigInt::from(1)),
        };
        Key { id, process, op }
    }
}

/// Value represents data types, which list can currently store
///
/// Structure is not full and probably will be expanded in near future, hence non_exhaustive
#[non_exhaustive]
#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
pub enum Value {
    /// String
    Str(String),

    /// Vector os Value
    Vec(Vec<Value>),

    /// Tombstone, for deletion indication
    Tombstone(Key),

    /// Empty value, never actually appears in the List itself
    ///
    /// Required to preserve sequence of vclock operations in diff
    Empty,
}

impl<T: Into<String>> From<T> for Value {
    fn from(value: T) -> Value {
        Value::Str(value.into())
    }
}

impl PartialEq<str> for Value {
    fn eq(&self, other: &str) -> bool {
        match self {
            Self::Str(s) => s.as_str().eq(other),
            _ => false,
        }
    }
}

impl Value {
    fn visible(&self) -> bool {
        !matches!(self, Value::Tombstone(_) | Value::Empty)
    }
}

struct Hooks {
    pub update: Option<Box<dyn Fn(&Op)>>,
}

impl std::fmt::Debug for Hooks {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.update.is_some() {
            true => write!(f, "Hooks{{ update: Some(..) }}"),
            false => write!(f, "Hooks{{ update: None }}"),
        }
    }
}

impl Hooks {
    fn new() -> Self {
        Self { update: None }
    }

    fn set_on_update(&mut self, hook: Box<dyn Fn(&Op)>) {
        self.update = Some(hook)
    }

    fn unset_on_update(&mut self) {
        self.update = None
    }
}


/// Op, represents operation over list
///
/// Currently everything is represented as an **I**nsert, since deletion can be represented as a
/// insertion of a tombstone
#[derive(Debug, Eq, PartialEq, Serialize, Deserialize, Clone)]
pub enum Op {
    /// I - short for Insertion
    I { 
        /// Op key
        key: Key, 
        /// Op value
        value: Value 
    },
}

impl Op {
    fn key(&self) -> &Key {
        match self {
            Op::I { key, .. } => key,
        }
    }
}

impl PartialOrd for Op {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.key().partial_cmp(other.key())
    }
}

impl Ord for Op {
    fn cmp(&self, other: &Self) -> Ordering {
        self.key().cmp(other.key())
    }
}

/// List Error
#[derive(Debug, Clone, Copy)]
pub enum ListError {
    /// Apply operation failed due to missing elements in provided sequence
    OutOfOrder {
        /// Id of a process, which owns list
        process: u64,
        /// Current clock for a process
        current_clock: u64,
        /// Operation clock
        operation_clock: u64,
    },
    /// Insertion failure due to out of bounds index
    OutOfBounds,
}

/// List
#[derive(Debug)]
pub struct List {
    process: u64,
    vclock: VClock,
    data: BTreeMap<Key, Value>,
    hooks: Hooks,
}

unsafe impl Send for List {}

impl List {
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
    /// Whenever local update happens - hook will be invoked
    /// Only 1 hook could be current set
    pub fn set_on_update(&mut self, hook: Box<dyn Fn(&Op)>) {
        self.hooks.set_on_update(hook)
    }

    /// Unset on update hook
    pub fn unset_on_update(&mut self) {
        self.hooks.unset_on_update()
    }

    /// Insert value at index
    pub fn insert(&mut self, index: usize, value: Value) -> Result<(), ListError> {
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
        );
        self.on_update(&key, &value);
        self.insert_key(key, value);
        Ok(())
    }

    // FIXME: OutOfBounds error
    /// Delete value at index
    pub fn delete(&mut self, index: usize) {
        let key = match self
            .data
            .iter()
            .filter(|(_, value)| value.visible())
            .map(|x| x.0)
            .nth(index)
        {
            None => return,
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
    }

    /// Apply operations generated by peers
    ///
    /// Operation application are idemponent, if operation number is less that current vclock for a
    /// process, which generated operation - it will be skipped
    ///
    /// Gaps in operations are not allowed and would trigger error
    pub fn apply(&mut self, ops: &[Op]) -> Result<(), ListError> {
        for op in ops {
            let op_key = op.key().clone();
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
            match op {
                Op::I { value, .. } => self.insert_key(op_key, value.clone()),
            }
        }
        Ok(())
    }

    /// Append value at the end
    pub fn append(&mut self, value: Value) -> Result<(), ListError> {
        self.insert(self.data.len(), value)
    }

    /// Build vector of values
    pub fn to_vec<'a, 'b: 'a>(&'b self) -> Vec<&'a Value> {
        self.data
            .iter()
            .map(|x| x.1)
            .filter(|x| x.visible())
            .collect()
    }

    /// Share own vclock state
    pub fn vclock(&self) -> &VClock {
        &self.vclock
    }

    /// Calculate diff
    pub fn diff(&self, other: &VClock) -> Vec<Op> {
        let vdiff: VClockDiff = (self.vclock(), other).into();
        let mut ops: Vec<Op> = Vec::new();
        for (key, value) in self.data.iter() {
            // check if peer already seen that key
            match vdiff.get_range(key.process) {
                Some((start, end)) if key.op > start && key.op <= end => (),
                _ => continue,
            };

            // check if peer seen key, which is being held by tombstone
            if let Value::Tombstone(tombstone_key) = value {
                // if peer didn't see insert, which is being deleted - generate empty value to preserve
                // sequence of operations
                match vdiff.get_range(tombstone_key.process) {
                    Some((start, end)) if tombstone_key.op > start && tombstone_key.op <= end => {
                        ops.push(Op::I {
                            key: tombstone_key.clone(),
                            value: Value::Empty,
                        });
                    }
                    _ => (),
                }
            }
            ops.push(Op::I {
                key: key.clone(),
                value: value.clone(),
            })
        }
        ops.sort_by(|left, right| left.key().op.cmp(&right.key().op));
        ops
    }

    /// Get size of stored data (without tombstones)
    pub fn size(&self) -> usize {
        // FIXME: add list metrics to avoid scan
        self.data.values().filter(|x| x.visible()).count()
    }

    fn insert_key(&mut self, key: Key, value: Value) {
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

    fn on_update(&self, key: &Key, value: &Value) {
        if let Some(ref u) = self.hooks.update {
            u(&Op::I {
                key: key.clone(),
                value: value.clone(),
            })
        }
    }

}
