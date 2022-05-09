use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::convert::From;

#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
pub struct VClock(HashMap<u64, u64>);

impl VClock {
    pub fn new() -> Self {
        Self(HashMap::new())
    }

    pub fn inc(&mut self, process: u64) -> u64 {
        let value = match self.0.get(&process) {
            Some(&value) => value,
            None => 0,
        } + 1;
        self.0.insert(process, value);
        value
    }

    pub fn get_clock(&self, process: u64) -> u64 {
        self.0.get(&process).map_or(0, |&x| x)
    }

    pub fn next_value(&self, process: u64) -> u64 {
        self.get_clock(process) + 1
    }

    pub fn iter(&self) -> impl Iterator<Item = (&u64, &u64)> {
        self.0.iter()
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

#[derive(Debug, PartialEq, Eq)]
pub struct VClockDiff(HashMap<u64, (u64, u64)>);

impl VClockDiff {
    pub fn new() -> Self {
        Self(HashMap::new())
    }

    pub fn get_range(&self, process: u64) -> Option<(u64, u64)> {
        self.0.get(&process).copied()
    }

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
