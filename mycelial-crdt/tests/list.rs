use mycelial_crdt::list::{Key, List, Op, Value};
use num::rational::Ratio;
use num::BigInt;
use quickcheck::{quickcheck, Arbitrary, Gen, TestResult};

#[test]
fn test_list() {
    let mut list = List::new(0);
    assert!(list.insert(0, "hello".into()).is_ok());

    assert_eq!(list.to_vec(), vec![&Value::Str("hello".into())]);

    assert!(list.insert(1, "world".into()).is_ok());
    assert_eq!(
        list.to_vec(),
        vec![&Value::Str("hello".into()), &Value::Str("world".into()),]
    );

    list.delete(0);
    assert_eq!(list.to_vec(), vec![&Value::Str("world".into())]);

    list.delete(0);
    assert!(list.to_vec().is_empty());
}

#[test]
fn test_diff_apply() {
    let mut list_a = List::new(0);
    list_a.append("hello".into()).unwrap();
    list_a.append(" ".into()).unwrap();
    list_a.append("world".into()).unwrap();
    list_a.delete(1);
    assert_eq!(
        list_a.to_vec(),
        vec![&Value::Str("hello".into()), &Value::Str("world".into())]
    );

    let mut list_b = List::new(1);
    assert!(list_b.diff(list_a.vclock()).is_empty());

    let ops = list_a.diff(list_b.vclock());
    assert_eq!(
        vec![
            Op {
                key: Key::new(BigInt::from(0), 0, 1),
                value: "hello".into()
            },
            Op {
                key: Key::new(BigInt::from(1), 0, 2),
                value: Value::Empty
            },
            Op {
                key: Key::new(BigInt::from(2), 0, 3),
                value: "world".into()
            },
            Op {
                key: Key::new(BigInt::from(1), 0, 4),
                value: Value::Tombstone(Key::new(BigInt::from(1), 0, 2))
            }
        ],
        ops
    );
    assert!(list_b.apply(&ops).is_ok());
    assert_eq!(list_a.to_vec(), list_b.to_vec());
}

#[test]
fn test_diff_apply_deletion() {
    let mut list_a = List::new(0);
    list_a.append("hello".into()).unwrap();
    list_a.append(" ".into()).unwrap();
    list_a.append("world".into()).unwrap();
    assert_eq!(
        list_a.to_vec(),
        vec![
            &Value::Str("hello".into()),
            &Value::Str(" ".into()),
            &Value::Str("world".into())
        ]
    );

    let mut list_b = List::new(1);
    assert!(list_b.diff(list_a.vclock()).is_empty());

    let ops = list_a.diff(list_b.vclock());
    assert_eq!(
        vec![
            Op {
                key: Key::new(BigInt::from(0), 0, 1),
                value: "hello".into()
            },
            Op {
                key: Key::new(BigInt::from(1), 0, 2),
                value: " ".into()
            },
            Op {
                key: Key::new(BigInt::from(2), 0, 3),
                value: "world".into()
            },
        ],
        ops
    );
    assert!(list_b.apply(&ops).is_ok());
    assert_eq!(list_a.to_vec(), list_b.to_vec());

    list_a.delete(1);
    let ops = list_a.diff(list_b.vclock());
    // no empty value here, only tombstone, since list_b seen insert of " "
    assert_eq!(
        vec![Op {
            key: Key::new(BigInt::from(1), 0, 4),
            value: Value::Tombstone(Key::new(BigInt::from(1), 0, 2))
        }],
        ops
    );
    assert!(list_b.apply(&ops).is_ok());
    assert_eq!(list_a.to_vec(), list_b.to_vec());
}

#[test]
fn test_key_between() {
    // initial key
    assert_eq!(
        Key::new(BigInt::from(0), 0, 0),
        Key::between(0, 0, None, None)
    );

    // insert at head
    assert_eq!(
        Key::new(BigInt::from(-1), 0, 0),
        Key::between(0, 0, None, Some(&Key::new(BigInt::from(0), 0, 0)))
    );

    // insert at between
    assert_eq!(
        Key::new(Ratio::new_raw(BigInt::from(-1), BigInt::from(2)), 0, 0),
        Key::between(
            0,
            0,
            Some(&Key::new(BigInt::from(-1), 0, 0)),
            Some(&Key::new(BigInt::from(0), 0, 0))
        )
    );

    // insert at tail
    assert_eq!(
        Key::new(BigInt::from(1), 0, 0),
        Key::between(0, 0, Some(&Key::new(BigInt::from(0), 0, 0)), None),
    );
}

#[test]
fn test_hooks() {
    use std::sync::mpsc::channel;

    let (tx, rx) = channel();
    let mut list = List::new(0);

    let hook: Box<dyn Fn(&Op)> = Box::new(move |op| {
        tx.send(op.clone()).unwrap_or(());
    });
    list.set_on_update(hook);

    list.append("1".into()).unwrap_or(());
    assert!(matches!(
        rx.try_recv(),
        Ok(Op {
            value: Value::Str(_),
            ..
        })
    ));

    list.delete(0);
    assert!(matches!(
        rx.try_recv(),
        Ok(Op {
            value: Value::Tombstone(_),
            ..
        })
    ));

    list.unset_on_update();
    assert!(matches!(rx.recv(), Err(_)))
}

#[derive(Debug, Clone)]
enum Position {
    Head,
    Tail,
    InBetween(usize),
}

#[derive(Debug, Clone)]
enum TestOp {
    Insert {
        process: u64,
        position: Position,
        value: Value,
    },
    Delete {
        process: u64,
        position: Position,
    },
    Merge {
        from: u64,
        to: u64,
    },
}

impl TestOp {
    fn process(&self) -> u64 {
        match self {
            &TestOp::Insert { process, .. } => process,
            &TestOp::Delete { process, .. } => process,
            &TestOp::Merge { from, to } => from.max(to),
        }
    }
}

impl Arbitrary for TestOp {
    fn arbitrary(g: &mut Gen) -> Self {
        let max_processes = 7;
        let process = u64::arbitrary(g) % max_processes;

        let position = match usize::arbitrary(g) % 10 {
            0 => Position::InBetween(usize::arbitrary(g)),
            num if num <= 5 => Position::Head,
            _ => Position::Tail,
        };

        match (u8::arbitrary(g) as usize) % 10 {
            0 => TestOp::Merge {
                from: u64::arbitrary(g) % max_processes,
                to: u64::arbitrary(g) % max_processes,
            },
            num if num <= 2 => TestOp::Delete { process, position },
            _ => TestOp::Insert {
                value: Value::from(format!("{}", u8::arbitrary(g))),
                process,
                position,
            },
        }
    }
}

#[test]
fn test_convergence() {
    fn check(ops: Vec<TestOp>) -> TestResult {
        let max = (&ops).iter().map(|op| op.process()).max();
        let lists = &mut match max {
            Some(max) => (0..=max).map(|pos| List::new(pos)).collect::<Vec<_>>(),
            None => return TestResult::discard(),
        };

        for op in ops {
            match op {
                TestOp::Insert {
                    process,
                    value,
                    position,
                } => {
                    let list = lists.get_mut(process as usize).unwrap();
                    let index = match position {
                        Position::Head => 0,
                        Position::Tail => list.size(),
                        Position::InBetween(val) => {
                            let size = list.size();
                            if size == 0 {
                                0
                            } else {
                                val % size
                            }
                        }
                    };
                    list.insert(index, value).unwrap();
                }
                TestOp::Delete { process, position } => {
                    let list = lists.get_mut(process as usize).unwrap();
                    let index = match position {
                        Position::Head => 0,
                        Position::Tail => list.size().max(1) - 1,
                        Position::InBetween(val) => val % list.size().max(1),
                    };
                    list.delete(index);
                }
                TestOp::Merge { from, to } => {
                    let (from, to) = (from as usize, to as usize);
                    let diff = {
                        let list_from = lists.get(from).unwrap();
                        let list_to = lists.get(to).unwrap();
                        list_from.diff(list_to.vclock())
                    };
                    match lists.get_mut(to).unwrap().apply(&diff) {
                        Ok(_) => (),
                        Err(e) => {
                            return TestResult::error(format!(
                                "failed to apply diff between {} and {}: {:?}",
                                from, to, e
                            ))
                        }
                    }
                }
            }
        }

        // merge all lists
        let len = lists.len();
        for from in 0..len {
            for to in 0..len {
                let diff = {
                    let list_from = lists.get(from).unwrap();
                    let list_to = lists.get(to).unwrap();
                    list_from.diff(list_to.vclock())
                };
                match lists.get_mut(to).unwrap().apply(&diff) {
                    Ok(_) => (),
                    Err(e) => {
                        return TestResult::error(format!(
                            "failed to apply diff between {} and {}: {:?}",
                            from, to, e
                        ))
                    }
                }
            }
        }

        // compare list with each other
        let eq = lists
            .windows(2)
            .map(|slice| slice.get(0).unwrap().to_vec() == slice.get(1).unwrap().to_vec())
            .all(|x| x == true);
        TestResult::from_bool(eq)
    }
    quickcheck(check as fn(Vec<TestOp>) -> TestResult)
}
