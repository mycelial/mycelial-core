//! VClock and helpers around vclock to simplify some tasks
//!
//! # Example
//!
//! ```rust
//! use mycelial_crdt::vclock::{VClock, VClockDiff};
//!
//! let mut vclock_0 = VClock::new();
//! let mut vclock_1 = VClock::new();
//!
//! assert_eq!(vclock_0.get_clock(0), 0);
//! vclock_0.inc(0);
//! vclock_0.inc(0);
//! assert_eq!(vclock_0.get_clock(0), 2);
//!
//! assert_eq!(vclock_1.get_clock(1), 0);
//! vclock_1.inc(1);
//! assert_eq!(vclock_1.get_clock(1), 1);
//!
//! // Difference between vclock_0 and vclock_1
//! let vclock_diff: VClockDiff = (&vclock_0, &vclock_1).into();
//! assert_eq!(
//!     vclock_diff.into_iter().map(|(&p, &(s, e))| (p, (s, e))).collect::<Vec<_>>(),
//!     vec![(0, (0, 2))]
//! );
//!
//! // Difference between vclock_1 and vclock_0
//! let vclock_diff: VClockDiff = (&vclock_1, &vclock_0).into();
//! assert_eq!(
//!     vclock_diff.into_iter().map(|(&p, &(s, e))| (p, (s, e))).collect::<Vec<_>>(),
//!     vec![(1, (0, 1))]
//! );
//! ```

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::convert::From;

/// VClock represented as a hashmap where key is a process id and value is current clock value
#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
pub struct VClock(HashMap<u64, u64>);

impl VClock {
    /// Initialize new VClock
    pub fn new() -> Self {
        Self(HashMap::new())
    }

    /// Increment given process clock by 1
    pub fn inc(&mut self, process: u64) -> u64 {
        let value = match self.0.get(&process) {
            Some(&value) => value,
            None => 0,
        } + 1;
        self.0.insert(process, value);
        value
    }

    /// Get current clock value for a given process
    pub fn get_clock(&self, process: u64) -> u64 {
        self.0.get(&process).map_or(0, |&x| x)
    }

    /// Peek next process clock value
    pub fn next_value(&self, process: u64) -> u64 {
        self.get_clock(process) + 1
    }
}

impl Default for VClock {
    fn default() -> Self {
        Self::new()
    }
}

impl<'a> IntoIterator for &'a VClock {
    type Item = (&'a u64, &'a u64);
    type IntoIter = std::collections::hash_map::Iter<'a, u64, u64>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

/// VClockDiff represents difference ranges between 2 vclocks
#[derive(Debug, PartialEq, Eq)]
pub struct VClockDiff(HashMap<u64, (u64, u64)>);

impl VClockDiff {
    /// Initialize empty vclock diff
    pub fn new() -> Self {
        Self(HashMap::new())
    }

    /// Get difference range for a given process
    pub fn get_range(&self, process: u64) -> Option<(u64, u64)> {
        self.0.get(&process).copied()
    }

    /// Insert new range for a given process
    ///
    /// Not really used, simplifies tests
    pub fn insert(&mut self, process: u64, diff: (u64, u64)) {
        self.0.insert(process, diff);
    }
}

impl Default for VClockDiff {
    fn default() -> Self {
        Self::new()
    }
}

impl<'a> IntoIterator for &'a VClockDiff {
    type Item = (&'a u64, &'a (u64, u64));
    type IntoIter = std::collections::hash_map::Iter<'a, u64, (u64, u64)>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl From<(&VClock, &VClock)> for VClockDiff {
    fn from((vclock_left, vclock_right): (&VClock, &VClock)) -> Self {
        let mut vdiff = VClockDiff::new();
        for (&process, &clock_left) in vclock_left {
            let clock_right = vclock_right.get_clock(process);
            if clock_left > clock_right {
                vdiff.insert(process, (clock_right, clock_left));
            };
        }
        vdiff
    }
}
