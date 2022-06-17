use mycelial_crdt::list::{GenericList, Key, List, ListError, ListKey, Op, Value};
use num::rational::Ratio;
use num::BigInt;
use quickcheck::{quickcheck, Arbitrary, Gen, TestResult};
use std::sync::mpsc::channel;

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

    assert!(list.delete(0).is_ok());
    assert_eq!(list.to_vec(), vec![&Value::Str("world".into())]);

    assert!(list.delete(0).is_ok());
    assert!(list.to_vec().is_empty());
}

#[test]
fn test_diff_apply() {
    let mut list_a = List::new(0);
    assert!(list_a.append("hello".into()).is_ok());
    assert!(list_a.append(" ".into()).is_ok());
    assert!(list_a.append("world".into()).is_ok());
    assert!(list_a.delete(1).is_ok());
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
    assert!(list_a.append("hello".into()).is_ok());
    assert!(list_a.append(" ".into()).is_ok());
    assert!(list_a.append("world".into()).is_ok());
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

    assert!(list_a.delete(1).is_ok());
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
        <Key::<Ratio<BigInt>> as ListKey>::between(0, 0, None, None).unwrap()
    );

    // insert at head
    assert_eq!(
        Key::new(BigInt::from(-1), 0, 0),
        <Key::<Ratio<BigInt>> as ListKey>::between(
            0,
            0,
            None,
            Some(&Key::new(BigInt::from(0), 0, 0))
        )
        .unwrap()
    );

    // insert at between
    assert_eq!(
        Key::new(Ratio::new_raw(BigInt::from(-1), BigInt::from(2)), 0, 0),
        <Key::<Ratio<BigInt>> as ListKey>::between(
            0,
            0,
            Some(&Key::new(BigInt::from(-1), 0, 0)),
            Some(&Key::new(BigInt::from(0), 0, 0))
        )
        .unwrap()
    );

    // insert at tail
    assert_eq!(
        Key::new(BigInt::from(1), 0, 0),
        <Key::<Ratio<BigInt>> as ListKey>::between(
            0,
            0,
            Some(&Key::new(BigInt::from(0), 0, 0)),
            None
        )
        .unwrap(),
    );
}

#[test]
fn test_on_update_hook() {
    let (tx, rx) = channel();
    let mut list = List::new(0);

    let hook: Box<dyn Fn(&Op<Key<Ratio<BigInt>>>)> = Box::new(move |op| {
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

    assert!(list.delete(0).is_ok());
    assert!(matches!(
        rx.try_recv(),
        Ok(Op {
            value: Value::Tombstone(_),
            ..
        })
    ));

    // unset drops Sender, Received will always return Err
    list.unset_on_update();
    assert!(matches!(rx.recv(), Err(_)))
}

#[test]
fn test_on_apply_hook() {
    let (tx, rx) = channel();
    let mut list_0 = List::new(0);
    let mut list_1 = List::new(1);

    let hook: Box<dyn Fn()> = Box::new(move || {
        tx.send(()).unwrap_or(());
    });
    list_1.set_on_apply(hook);

    list_0.append("0".into()).unwrap_or(());
    let diff = list_0.diff(list_1.vclock());
    assert!(list_1.apply(&diff).is_ok());
    assert!(matches!(rx.try_recv(), Ok(()),));

    // unset drops Sender, Received will always return Err
    list_1.unset_on_apply();
    assert!(matches!(rx.recv(), Err(_)))
}

#[derive(Debug, Clone)]
enum Position {
    Head,
    Tail,
    InBetween(usize),
}

#[derive(Debug, Clone)]
enum TestOp<T> {
    Insert {
        process: u64,
        position: Position,
        value: Value<Key<T>>,
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

impl<T: Clone + 'static> TestOp<T> {
    fn process(&self) -> u64 {
        match self {
            &TestOp::Insert { process, .. } => process,
            &TestOp::Delete { process, .. } => process,
            &TestOp::Merge { from, to } => from.max(to),
        }
    }
}

impl<T: Clone + 'static> Arbitrary for TestOp<T> {
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

fn check<T: Clone + 'static>(ops: Vec<TestOp<T>>) -> TestResult
where
    Key<T>: ListKey,
{
    // currently list without arbitrary precision arithmetic for keys is append only
    let append_only_error_allowed = !Key::<T>::is_arbitraty_precision();

    // allocate lists
    let max = (&ops).iter().map(|op| op.process()).max();
    let lists = &mut match max {
        Some(max) => (0..=max)
            .map(|pos| GenericList::<Key<T>>::new(pos))
            .collect::<Vec<_>>(),
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
                match index {
                    0 => list.prepend(value),
                    val if val == list.size() => list.append(value),
                    _ => match list.insert(index, value) {
                        Ok(()) => Ok(()),
                        Err(ListError::AppendOnly) if append_only_error_allowed => Ok(()),
                        e => e,
                    },
                }
                .unwrap()
            }
            TestOp::Delete { process, position } => {
                let list = lists.get_mut(process as usize).unwrap();
                let index = match position {
                    Position::Head => 0,
                    Position::Tail => list.size().max(1) - 1,
                    Position::InBetween(val) => val % list.size().max(1),
                };
                list.delete(index).ok();
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
    if !eq {
        return TestResult::error("lists do not converge after merging");
    }

    // check that total diff restores list
    let eq = lists
        .iter()
        .map(|list| {
            let mut empty = GenericList::<Key<T>>::new(100500);
            let diff = list.diff(empty.vclock());
            empty.apply(&diff).is_ok() && empty.to_vec() == list.to_vec()
        })
        .all(|x| x == true);
    if !eq {
        return TestResult::error("could not rebuild list from total diff");
    }
    TestResult::from_bool(true)
}

#[test]
fn test_list_convergence() {
    quickcheck(check as fn(Vec<TestOp<Ratio<BigInt>>>) -> TestResult);
}

#[test]
fn test_append_only_list_convergence() {
    quickcheck(check as fn(Vec<TestOp<i64>>) -> TestResult);
}
