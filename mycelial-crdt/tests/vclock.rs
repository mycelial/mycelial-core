use mycelial_crdt::vclock::{VClock, VClockDiff};

#[test]
fn test_vclock() {
    let mut vclock = VClock::new();
    assert_eq!(vclock.get_clock(0), 0);
    assert_eq!(Vec::from_iter((&vclock).into_iter()), vec![]);

    vclock.inc(0);
    assert_eq!(vclock.get_clock(0), 1);
    assert_eq!(Vec::from_iter((&vclock).into_iter()), vec![(&0, &1)]);
}

#[test]
fn test_vclock_diff() {
    let mut vclock_0 = VClock::new();
    assert_eq!(1, vclock_0.inc(0));

    let mut vclock_1 = VClock::new();
    assert_eq!(1, vclock_1.inc(1));

    assert_eq!(
        { let diff: VClockDiff = (&vclock_0, &vclock_1).into(); diff },
        { let mut diff = VClockDiff::new(); diff.insert(0, (0, 1)); diff }
    );

    assert_eq!(
        { let diff: VClockDiff = (&vclock_1, &vclock_0).into(); diff },
        { let mut diff = VClockDiff::new(); diff.insert(1, (0, 1)); diff }
    );
}
