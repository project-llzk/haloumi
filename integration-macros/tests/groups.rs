use std::hash::Hash;

use haloumi_integration::core::{
    groups::{GroupKey, GroupLayouter, RegionsGroup, RegionsGroupHooks},
    table::DecomposeIn,
};
use haloumi_integration_macros::group;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct TestCell(u8);

#[derive(Clone, Debug, PartialEq, Eq)]
struct TestValue(Vec<TestCell>);

impl DecomposeIn<TestCell> for TestValue {
    fn cells(&self) -> impl IntoIterator<Item = TestCell> {
        self.0.clone()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct TestError;

#[derive(Debug, PartialEq, Eq)]
struct RecordedGroup {
    name: String,
    inputs: Vec<TestCell>,
    outputs: Vec<TestCell>,
    children: Vec<Self>,
}

impl RecordedGroup {
    fn root() -> Self {
        Self {
            name: "root".into(),
            inputs: vec![],
            outputs: vec![],
            children: vec![],
        }
    }

    fn group(name: String) -> Self {
        Self {
            name,
            inputs: vec![],
            outputs: vec![],
            children: vec![],
        }
    }
}

#[derive(Debug)]
struct RecordingLayouter {
    stack: Vec<RecordedGroup>,
}

impl Default for RecordingLayouter {
    fn default() -> Self {
        Self {
            stack: vec![RecordedGroup::root()],
        }
    }
}

impl RecordingLayouter {
    fn finish(self) -> RecordedGroup {
        assert_eq!(self.stack.len(), 1, "all groups must have been popped");
        self.stack.into_iter().next().unwrap()
    }
}

impl RegionsGroupHooks<(), TestCell> for RecordingLayouter {
    type Error = TestError;
    type RootHook = Self;

    fn get_root_hook(&mut self) -> &mut Self::RootHook {
        self
    }

    fn push_group<N, NR, K>(&mut self, name: N, _: K)
    where
        N: FnOnce() -> NR,
        NR: Into<String>,
        K: GroupKey,
    {
        self.stack.push(RecordedGroup::group(name().into()));
    }

    fn pop_group(&mut self, meta: RegionsGroup<TestCell>) {
        let group = self.stack.last_mut().expect("cannot pop the root group");
        group.inputs.extend(meta.inputs());
        group.outputs.extend(meta.outputs());

        let group = self.stack.pop().expect("cannot pop the root group");
        self.stack
            .last_mut()
            .expect("cannot append a group without a parent")
            .children
            .push(group);
    }
}

/// The generated code only requires a layouter with a `group` method. This
/// local extension deliberately uses that structural interface rather than
/// the integration macro that patches a downstream layouter trait.
trait GroupLayouterExt {
    fn group<A, AR, N, NR, K>(&mut self, name: N, key: K, assignment: A) -> Result<AR, TestError>
    where
        A: FnMut(
            &mut GroupLayouter<'_, (), RecordingLayouter>,
            &mut RegionsGroup<TestCell>,
        ) -> Result<AR, TestError>,
        N: FnOnce() -> NR,
        NR: Into<String>,
        K: GroupKey;
}

impl GroupLayouterExt for RecordingLayouter {
    fn group<A, AR, N, NR, K>(&mut self, name: N, key: K, assignment: A) -> Result<AR, TestError>
    where
        A: FnMut(
            &mut GroupLayouter<'_, (), RecordingLayouter>,
            &mut RegionsGroup<TestCell>,
        ) -> Result<AR, TestError>,
        N: FnOnce() -> NR,
        NR: Into<String>,
        K: GroupKey,
    {
        self.group_impl(name, key, assignment)
    }
}

impl GroupLayouterExt for GroupLayouter<'_, (), RecordingLayouter> {
    fn group<A, AR, N, NR, K>(&mut self, name: N, key: K, assignment: A) -> Result<AR, TestError>
    where
        A: FnMut(
            &mut GroupLayouter<'_, (), RecordingLayouter>,
            &mut RegionsGroup<TestCell>,
        ) -> Result<AR, TestError>,
        N: FnOnce() -> NR,
        NR: Into<String>,
        K: GroupKey,
    {
        self.group_impl(name, key, assignment)
    }
}

#[group]
fn grouped(
    layouter: &mut impl GroupLayouterExt,
    #[input] input: TestValue,
    #[input]
    #[output]
    input_output: &mut TestValue,
    #[output] output: &mut TestValue,
) -> Result<TestValue, TestError> {
    let _ = layouter;
    *input_output = TestValue(vec![TestCell(6)]);
    *output = TestValue(vec![TestCell(4)]);
    Ok(TestValue(vec![TestCell(5)]))
}

#[group]
fn renamed_layouter(
    #[layouter] region: &mut impl GroupLayouterExt,
    #[input] input: TestValue,
) -> Result<TestValue, TestError> {
    let _ = region;
    Ok(input.clone())
}

#[group]
fn nested_inner(
    layouter: &mut impl GroupLayouterExt,
    #[input] input: TestValue,
) -> Result<TestValue, TestError> {
    let _ = layouter;
    Ok(input.clone())
}

#[group]
fn nested_outer(
    layouter: &mut impl GroupLayouterExt,
    #[input] input: TestValue,
) -> Result<TestValue, TestError> {
    nested_inner(layouter, input.clone())
}

#[group]
fn fails(
    layouter: &mut impl GroupLayouterExt,
    #[input] input: TestValue,
) -> Result<TestValue, TestError> {
    let _ = layouter;
    let _ = input;
    Err(TestError)
}

#[test]
fn generated_code_records_argument_and_return_annotations() {
    let mut layouter = RecordingLayouter::default();
    let mut input_output = TestValue(vec![TestCell(3)]);
    let mut output = TestValue(vec![]);

    assert_eq!(
        grouped(
            &mut layouter,
            TestValue(vec![TestCell(1), TestCell(2)]),
            &mut input_output,
            &mut output,
        ),
        Ok(TestValue(vec![TestCell(5)])),
    );

    assert_eq!(
        layouter.finish().children,
        [RecordedGroup {
            name: "grouped".into(),
            inputs: vec![TestCell(1), TestCell(2), TestCell(3)],
            outputs: vec![TestCell(6), TestCell(4), TestCell(5)],
            children: vec![],
        }],
    );
}

#[test]
fn generated_code_uses_the_annotated_layouter_parameter() {
    let mut layouter = RecordingLayouter::default();

    assert_eq!(
        renamed_layouter(&mut layouter, TestValue(vec![TestCell(7)])),
        Ok(TestValue(vec![TestCell(7)])),
    );
    assert_eq!(
        layouter.finish().children,
        [RecordedGroup {
            name: "renamed_layouter".into(),
            inputs: vec![TestCell(7)],
            outputs: vec![TestCell(7)],
            children: vec![],
        }],
    );
}

#[test]
fn generated_code_nests_groups() {
    let mut layouter = RecordingLayouter::default();

    assert_eq!(
        nested_outer(&mut layouter, TestValue(vec![TestCell(8)])),
        Ok(TestValue(vec![TestCell(8)])),
    );
    assert_eq!(
        layouter.finish().children,
        [RecordedGroup {
            name: "nested_outer".into(),
            inputs: vec![TestCell(8)],
            outputs: vec![TestCell(8)],
            children: vec![RecordedGroup {
                name: "nested_inner".into(),
                inputs: vec![TestCell(8)],
                outputs: vec![TestCell(8)],
                children: vec![],
            }],
        }],
    );
}

#[test]
fn generated_code_pops_a_failed_group() {
    let mut layouter = RecordingLayouter::default();

    assert_eq!(
        fails(&mut layouter, TestValue(vec![TestCell(9)])),
        Err(TestError)
    );
    assert_eq!(
        layouter.finish().children,
        [RecordedGroup {
            name: "fails".into(),
            inputs: vec![TestCell(9)],
            outputs: vec![],
            children: vec![],
        }],
    );
}
