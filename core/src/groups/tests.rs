//! Tests that group hooks preserve group hierarchy and annotations.

use std::{fmt, hash::Hash};

use super::*;

type TestCell = u8;

#[derive(Clone, Copy, Debug, Hash)]
struct TestKey(u8);

impl GroupKey for TestKey {}

#[derive(Debug, PartialEq, Eq)]
struct RecordedGroup {
    name: String,
    key: Option<u64>,
    inputs: Vec<TestCell>,
    outputs: Vec<TestCell>,
    groups: Vec<Self>,
}

impl RecordedGroup {
    fn root() -> Self {
        Self {
            name: "top-level".into(),
            key: None,
            inputs: vec![],
            outputs: vec![],
            groups: vec![],
        }
    }

    fn group(name: String, key: u64) -> Self {
        Self {
            name,
            key: Some(key),
            inputs: vec![],
            outputs: vec![],
            groups: vec![],
        }
    }
}

fn write_group(group: &RecordedGroup, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(formatter, "({}", group.name)?;
    if !group.inputs.is_empty() {
        write!(formatter, " (inputs {:?})", group.inputs)?;
    }
    if !group.outputs.is_empty() {
        write!(formatter, " (outputs {:?})", group.outputs)?;
    }
    if !group.groups.is_empty() {
        write!(formatter, " (groups")?;
        for child in &group.groups {
            write!(formatter, " ")?;
            write_group(child, formatter)?;
        }
        write!(formatter, ")")?;
    }
    write!(formatter, ")")
}

impl fmt::Display for RecordedGroup {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write_group(self, formatter)
    }
}

#[derive(Debug)]
struct RecordingHooks {
    stack: Vec<RecordedGroup>,
}

impl Default for RecordingHooks {
    fn default() -> Self {
        Self {
            stack: vec![RecordedGroup::root()],
        }
    }
}

impl RecordingHooks {
    fn top_level(self) -> RecordedGroup {
        assert_eq!(self.stack.len(), 1, "all groups must have been popped");
        self.stack.into_iter().next().unwrap()
    }
}

impl RegionsGroupHooks<(), TestCell> for RecordingHooks {
    type Error = &'static str;
    type RootHook = Self;

    fn get_root_hook(&mut self) -> &mut Self::RootHook {
        self
    }

    fn push_group<N, NR, K>(&mut self, name: N, key: K)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
        K: GroupKey,
    {
        self.stack.push(RecordedGroup::group(
            name().into(),
            GroupKeyInstance::from(key).into(),
        ));
    }

    fn pop_group(&mut self, meta: RegionsGroup<TestCell>) {
        let group = self.stack.last_mut().expect("cannot pop the root group");
        group.inputs.extend(meta.inputs());
        group.outputs.extend(meta.outputs());

        let group = self.stack.pop().expect("cannot pop the root group");
        self.stack
            .last_mut()
            .expect("cannot append a group without a parent")
            .groups
            .push(group);
    }
}

fn assert_layout(hooks: RecordingHooks, expected: &str) -> RecordedGroup {
    let top_level = hooks.top_level();
    assert_eq!(top_level.to_string(), expected);
    top_level
}

#[test]
fn empty_layout() {
    assert_layout(RecordingHooks::default(), "(top-level)");
}

#[test]
fn one_level_forwards_ordered_annotations() {
    let mut hooks = RecordingHooks::default();
    hooks
        .group_impl(
            || "one",
            TestKey(1),
            |_, group| {
                group.annotate_inputs([2, 1]);
                group.annotate_output(3);
                Ok(())
            },
        )
        .unwrap();

    assert_layout(
        hooks,
        "(top-level (groups (one (inputs [2, 1]) (outputs [3]))))",
    );
}

#[test]
fn nested_groups_are_attached_to_their_active_parent() {
    let mut hooks = RecordingHooks::default();
    hooks
        .group_impl(
            || "one",
            TestKey(1),
            |layouter, _| layouter.group_impl(|| "two", TestKey(2), |_, _| Ok(())),
        )
        .unwrap();

    assert_layout(hooks, "(top-level (groups (one (groups (two)))))");
}

#[test]
fn consecutive_groups_are_siblings() {
    let mut hooks = RecordingHooks::default();
    hooks
        .group_impl(|| "one", TestKey(1), |_, _| Ok(()))
        .unwrap();
    hooks
        .group_impl(|| "two", TestKey(2), |_, _| Ok(()))
        .unwrap();

    assert_layout(hooks, "(top-level (groups (one) (two)))");
}

#[test]
fn repeated_groups_keep_equal_keys_and_independent_annotations() {
    let mut hooks = RecordingHooks::default();
    for (input, output) in [(1, 2), (3, 4)] {
        hooks
            .group_impl(
                || "one",
                TestKey(1),
                |_, group| {
                    group.annotate_input(input);
                    group.annotate_output(output);
                    Ok(())
                },
            )
            .unwrap();
    }

    let top_level = assert_layout(
        hooks,
        "(top-level (groups (one (inputs [1]) (outputs [2])) (one (inputs [3]) (outputs [4]))))",
    );
    assert_eq!(top_level.groups[0].key, top_level.groups[1].key);
}

#[test]
fn a_cell_can_be_an_input_and_output() {
    let mut hooks = RecordingHooks::default();
    hooks
        .group_impl(
            || "one",
            TestKey(1),
            |_, group| {
                group.annotate_inputs([1, 2]);
                group.annotate_outputs([2, 3]);
                Ok(())
            },
        )
        .unwrap();

    assert_layout(
        hooks,
        "(top-level (groups (one (inputs [1, 2]) (outputs [2, 3]))))",
    );
}

#[test]
fn failed_group_is_popped_before_the_next_group() {
    let mut hooks = RecordingHooks::default();
    let result: Result<(), &'static str> =
        hooks.group_impl(|| "failed", TestKey(1), |_, _| Err("expected failure"));
    assert_eq!(result, Err("expected failure"));

    hooks
        .group_impl(|| "after", TestKey(2), |_, _| Ok(()))
        .unwrap();

    assert_layout(hooks, "(top-level (groups (failed) (after)))");
}
