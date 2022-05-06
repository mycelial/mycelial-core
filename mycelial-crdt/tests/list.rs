use mycelial_crdt::list::{List, Op, Value, Key};
use num::BigInt;
use num::rational::Ratio;
use std::collections::HashMap;
use quickcheck::{quickcheck, Arbitrary, Gen, TestResult};

#[test]
fn test_list() {
    let mut list = List::new(0);
    assert!(list.insert(0, "hello".into()).is_ok());

    assert_eq!(
        list.to_vec(),
        vec![&Value::Str("hello".into())]
    );

    assert!(list.insert(1, "world".into()).is_ok());
    assert_eq!(
        list.to_vec(),
        vec![
            &Value::Str("hello".into()),
            &Value::Str("world".into()),
        ]
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
    assert_eq!(list_a.to_vec(), vec![&Value::Str("hello".into()), &Value::Str("world".into())]);

    let mut list_b = List::new(1);
    assert!(list_b.diff(list_a.vclock()).is_empty());

    let ops = list_a.diff(list_b.vclock());
    assert_eq!(
        vec![
            Op::I { key: Key::new(BigInt::from(0), 0, 1), value: "hello".into() },
            Op::I { key: Key::new(BigInt::from(1), 0, 2), value: Value::Empty },
            Op::I { key: Key::new(BigInt::from(2), 0, 3), value: "world".into() },
            Op::I { key: Key::new(BigInt::from(1), 0, 4), value: Value::Tombstone(Key::new(BigInt::from(1), 0, 2))}
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
            Op::I { key: Key::new(BigInt::from(0), 0, 1), value: "hello".into() },
            Op::I { key: Key::new(BigInt::from(1), 0, 2), value: " ".into() },
            Op::I { key: Key::new(BigInt::from(2), 0, 3), value: "world".into() },
        ],
        ops
    );
    assert!(list_b.apply(&ops).is_ok());
    assert_eq!(list_a.to_vec(), list_b.to_vec());

    list_a.delete(1);
    let ops = list_a.diff(list_b.vclock());
    // no empty value here, only tombstone, since list_b seen insert of " "
    assert_eq!(
        vec![
            Op::I { key: Key::new(BigInt::from(1), 0, 4), value: Value::Tombstone(Key::new(BigInt::from(1), 0, 2))}
        ],
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
        Key::between(0, 0, Some(&Key::new(BigInt::from(-1), 0, 0)), Some(&Key::new(BigInt::from(0), 0, 0)))
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

    let hook: Box<dyn Fn(&Op)> = Box::new(move |op| { tx.send(op.clone()).unwrap_or(()); });
    list.set_on_update(hook);

    list.append("1".into()).unwrap_or(());
    assert!(matches!(rx.try_recv(), Ok(Op::I{value: Value::Str(_), ..})));

    list.delete(0);
    assert!(matches!(rx.try_recv(), Ok(Op::I{value: Value::Tombstone(_), ..})));

    list.unset_on_update();
    assert!(matches!(rx.recv(), Err(_)))

}


#[derive(Debug, Clone)]
enum OpType {
    Insert,
    Delete,
}

#[derive(Debug, Clone)]
enum Position {
    Head,
    Tail,
    InBetween(usize),
}

#[derive(Debug, Clone)]
struct TestOp {
    ty: OpType,
    value: Value,
    position: Position,
    process: u64,
}

#[derive(Debug, Clone)]
struct TestOps {
    ops: Vec<TestOp>
}

impl Arbitrary for TestOps {
    fn arbitrary(g: &mut Gen) -> Self {
        let operations = usize::arbitrary(g) % 1000;
        let ops: Vec<TestOp> = (0..=operations).map(|pos| {
            let process = u64::arbitrary(g) % 8;
            let ty = match bool::arbitrary(g) {
                true => OpType::Insert,
                false => OpType::Delete,
            };
            let value: Value = format!("{}", process).into();
            let position = match usize::arbitrary(g) % 2 {
                0 => { Position::Head },
                1 => { Position::Tail },
                _ => { Position::InBetween(pos) },
            };
            TestOp { ty, value, position, process }
        }).collect();
        TestOps{ ops }
    }
}


#[test]
fn test_convergence() {
    fn check(ops: TestOps) -> TestResult {
        // populate lists with operations
        let mut lists = HashMap::<u64, List>::new();
        for op in ops.ops {
            if lists.get(&op.process).is_none() {
                lists.insert(op.process, List::new(op.process));
            };
            lists.get_mut(&op.process).map(|list| {
                let index = match op.position {
                    Position::Head => 0,
                    Position::Tail => list.size(),
                    Position::InBetween(pos) => pos % list.size(),
                };
                match op.ty {
                    OpType::Insert => list.insert(index, op.value).unwrap_or(()),
                    OpType::Delete => list.delete(index),
                }
            });
        };

        if lists.len() < 2 {
            return TestResult::discard()
        }

        // merge lists
        let processes = lists.keys().map(|&x| x).collect::<Vec<u64>>();
        for process_left in &processes{
            for process_right in &processes{
                let diff_ops = {
                    let list_left = lists.get(process_left).unwrap();
                    let list_right = lists.get(process_right).unwrap();
                    list_left.diff(list_right.vclock())
                };
                lists.get_mut(process_right).map(|list| list.apply(&diff_ops).unwrap());
            }
        }

        // compare list with each other
        let eq = processes.windows(2).map(|slice| {
            lists.get(&slice[0]).unwrap().to_vec() == lists.get(&slice[1]).unwrap().to_vec()
        }).all(|x| x == true);

        TestResult::from_bool(eq)
    }
    quickcheck(check as fn(TestOps) -> TestResult)
}
