use std::{
    hash::Hash,
    marker::PhantomData,
    panic::{AssertUnwindSafe, catch_unwind},
};

use haloumi_integration::core::{
    groups::{GroupKey, GroupKeyInstance, GroupLayouter, RegionsGroup, RegionsGroupHooks},
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

#[derive(Clone)]
struct NoopHooks;

impl RegionsGroupHooks<(), TestCell> for NoopHooks {
    type Error = TestError;
    type RootHook = Self;

    fn get_root_hook(&mut self) -> &mut Self::RootHook {
        self
    }

    fn push_group<N, NR, K>(&mut self, _name: N, _key: K)
    where
        N: FnOnce() -> NR,
        NR: Into<String>,
        K: GroupKey,
    {
    }

    fn pop_group(&mut self, _meta: RegionsGroup<TestCell>) {}
}

#[derive(haloumi_integration_macros::RegionsGroupHooks)]
#[cell(TestCell)]
#[error(TestError)]
struct DelegatingHooks<F, T>
where
    T: Clone,
{
    _field: PhantomData<F>,
    #[delegate]
    inner: T,
}

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
    keys: Vec<u64>,
}

impl Default for RecordingLayouter {
    fn default() -> Self {
        Self {
            stack: vec![RecordedGroup::root()],
            keys: vec![],
        }
    }
}

impl RecordingLayouter {
    fn finish(self) -> RecordedGroup {
        assert_eq!(self.stack.len(), 1, "all groups must have been popped");
        self.stack.into_iter().next().unwrap()
    }

    fn keys(&self) -> &[u64] {
        &self.keys
    }
}

impl RegionsGroupHooks<(), TestCell> for RecordingLayouter {
    type Error = TestError;
    type RootHook = Self;

    fn get_root_hook(&mut self) -> &mut Self::RootHook {
        self
    }

    fn push_group<N, NR, K>(&mut self, name: N, key: K)
    where
        N: FnOnce() -> NR,
        NR: Into<String>,
        K: GroupKey,
    {
        self.keys.push(GroupKeyInstance::from(key).into());
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

#[test]
fn derived_group_hooks_merge_generated_and_existing_where_clauses() {
    fn assert_group_hooks<T>()
    where
        T: RegionsGroupHooks<(), TestCell, Error = TestError>,
    {
    }

    assert_group_hooks::<DelegatingHooks<(), NoopHooks>>();
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

#[group]
fn mutates_input_output(
    layouter: &mut impl GroupLayouterExt,
    #[input]
    #[output]
    value: &mut TestValue,
    replace_value: bool,
) -> Result<(), TestError> {
    let _ = layouter;
    if replace_value {
        *value = TestValue(vec![TestCell(11)]);
    }
    Ok(())
}

#[group]
#[allow(unreachable_code)]
fn returns_early(
    layouter: &mut impl GroupLayouterExt,
    #[input]
    #[output]
    value: &mut TestValue,
) -> Result<TestValue, TestError> {
    let _ = layouter;
    *value = TestValue(vec![TestCell(13)]);
    return Ok(TestValue(vec![TestCell(14)]));
}

fn always_fails() -> Result<(), TestError> {
    Err(TestError)
}

#[group]
fn propagates_error(
    layouter: &mut impl GroupLayouterExt,
    #[input]
    #[output]
    value: &mut TestValue,
) -> Result<TestValue, TestError> {
    let _ = layouter;
    *value = TestValue(vec![TestCell(16)]);
    always_fails()?;
    Ok(TestValue(vec![TestCell(17)]))
}

#[group]
fn mutates_optional_input_output(
    layouter: &mut impl GroupLayouterExt,
    #[input]
    #[output]
    value: &mut Option<TestValue>,
    replacement: Option<TestValue>,
) -> Result<(), TestError> {
    let _ = layouter;
    *value = replacement.clone();
    Ok(())
}

#[group]
fn returns_output_alias(
    layouter: &mut impl GroupLayouterExt,
    #[output] value: &mut TestValue,
) -> Result<TestValue, TestError> {
    let _ = layouter;
    *value = TestValue(vec![TestCell(24)]);
    Ok(value.clone())
}

#[group]
fn keyed(layouter: &mut impl GroupLayouterExt, #[input] value: TestValue) -> Result<(), TestError> {
    let _ = layouter;
    let _ = value;
    Ok(())
}

#[group]
fn differently_keyed(
    layouter: &mut impl GroupLayouterExt,
    #[input] value: TestValue,
) -> Result<(), TestError> {
    let _ = layouter;
    let _ = value;
    Ok(())
}

#[group]
#[allow(unreachable_code)]
fn panics_after_mutating_output(
    layouter: &mut impl GroupLayouterExt,
    #[input]
    #[output]
    value: &mut TestValue,
) -> Result<(), TestError> {
    let _ = layouter;
    *value = TestValue(vec![TestCell(27)]);
    panic!("expected test panic");
}

#[group]
fn nested_early_return(
    layouter: &mut impl GroupLayouterExt,
    #[input]
    #[output]
    value: &mut TestValue,
) -> Result<TestValue, TestError> {
    returns_early(layouter, value)
}

#[derive(Default)]
struct Stateful {
    calls: usize,
}

impl Stateful {
    #[group]
    fn record_call(
        &mut self,
        layouter: &mut impl GroupLayouterExt,
        #[input] value: TestValue,
    ) -> Result<TestValue, TestError> {
        let _ = layouter;
        self.calls += 1;
        Ok(value.clone())
    }
}

#[group]
fn returns_borrowed_value<'a>(
    layouter: &mut impl GroupLayouterExt,
    #[input] value: &'a TestValue,
) -> Result<&'a TestValue, TestError> {
    let _ = layouter;
    Ok(value)
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

#[test]
fn mutable_input_output_records_cells_before_and_after_the_body() {
    let mut layouter = RecordingLayouter::default();
    let mut unchanged = TestValue(vec![TestCell(10)]);
    let mut changed = TestValue(vec![TestCell(12)]);

    assert_eq!(
        mutates_input_output(&mut layouter, &mut unchanged, false),
        Ok(())
    );
    assert_eq!(
        mutates_input_output(&mut layouter, &mut changed, true),
        Ok(())
    );

    assert_eq!(
        layouter.finish().children,
        [
            RecordedGroup {
                name: "mutates_input_output".into(),
                inputs: vec![TestCell(10)],
                outputs: vec![TestCell(10)],
                children: vec![],
            },
            RecordedGroup {
                name: "mutates_input_output".into(),
                inputs: vec![TestCell(12)],
                outputs: vec![TestCell(11)],
                children: vec![],
            },
        ],
    );
}

#[test]
fn direct_early_return_records_final_outputs() {
    let mut layouter = RecordingLayouter::default();
    let mut value = TestValue(vec![TestCell(12)]);

    assert_eq!(
        returns_early(&mut layouter, &mut value),
        Ok(TestValue(vec![TestCell(14)])),
    );
    assert_eq!(
        layouter.finish().children,
        [RecordedGroup {
            name: "returns_early".into(),
            inputs: vec![TestCell(12)],
            outputs: vec![TestCell(13), TestCell(14)],
            children: vec![],
        }],
    );
}

#[test]
fn propagated_error_records_final_output_parameters() {
    let mut layouter = RecordingLayouter::default();
    let mut value = TestValue(vec![TestCell(15)]);

    assert_eq!(propagates_error(&mut layouter, &mut value), Err(TestError));
    assert_eq!(
        layouter.finish().children,
        [RecordedGroup {
            name: "propagates_error".into(),
            inputs: vec![TestCell(15)],
            outputs: vec![TestCell(16)],
            children: vec![],
        }],
    );
}

#[test]
fn mutable_input_output_records_structural_changes() {
    let mut layouter = RecordingLayouter::default();
    let mut populated = Some(TestValue(vec![TestCell(20), TestCell(21)]));
    let mut empty = None;

    assert_eq!(
        mutates_optional_input_output(&mut layouter, &mut populated, None),
        Ok(())
    );
    assert_eq!(
        mutates_optional_input_output(
            &mut layouter,
            &mut empty,
            Some(TestValue(vec![TestCell(22), TestCell(23)])),
        ),
        Ok(())
    );

    assert_eq!(
        layouter.finish().children,
        [
            RecordedGroup {
                name: "mutates_optional_input_output".into(),
                inputs: vec![TestCell(20), TestCell(21)],
                outputs: vec![],
                children: vec![],
            },
            RecordedGroup {
                name: "mutates_optional_input_output".into(),
                inputs: vec![],
                outputs: vec![TestCell(22), TestCell(23)],
                children: vec![],
            },
        ],
    );
}

#[test]
fn output_and_return_aliases_are_deduplicated() {
    let mut layouter = RecordingLayouter::default();
    let mut value = TestValue(vec![]);

    assert_eq!(
        returns_output_alias(&mut layouter, &mut value),
        Ok(TestValue(vec![TestCell(24)])),
    );
    assert_eq!(
        layouter.finish().children,
        [RecordedGroup {
            name: "returns_output_alias".into(),
            inputs: vec![],
            outputs: vec![TestCell(24)],
            children: vec![],
        }],
    );
}

#[test]
fn repeated_calls_share_a_group_key_and_distinct_functions_do_not() {
    let mut layouter = RecordingLayouter::default();

    keyed(&mut layouter, TestValue(vec![TestCell(25)])).unwrap();
    keyed(&mut layouter, TestValue(vec![TestCell(26)])).unwrap();
    differently_keyed(&mut layouter, TestValue(vec![TestCell(27)])).unwrap();

    assert_eq!(layouter.keys().len(), 3);
    assert_eq!(layouter.keys()[0], layouter.keys()[1]);
    assert_ne!(layouter.keys()[0], layouter.keys()[2]);
}

#[test]
fn nested_early_return_records_inner_and_outer_outputs() {
    let mut layouter = RecordingLayouter::default();
    let mut value = TestValue(vec![TestCell(28)]);

    assert_eq!(
        nested_early_return(&mut layouter, &mut value),
        Ok(TestValue(vec![TestCell(14)])),
    );
    assert_eq!(
        layouter.finish().children,
        [RecordedGroup {
            name: "nested_early_return".into(),
            inputs: vec![TestCell(28)],
            outputs: vec![TestCell(13), TestCell(14)],
            children: vec![RecordedGroup {
                name: "returns_early".into(),
                inputs: vec![TestCell(28)],
                outputs: vec![TestCell(13), TestCell(14)],
                children: vec![],
            }],
        }],
    );
}

#[test]
fn panic_unwinds_the_group_without_recording_final_outputs() {
    let mut layouter = RecordingLayouter::default();
    let mut value = TestValue(vec![TestCell(26)]);

    assert!(
        catch_unwind(AssertUnwindSafe(|| {
            let _ = panics_after_mutating_output(&mut layouter, &mut value);
        }))
        .is_err()
    );
    keyed(&mut layouter, TestValue(vec![TestCell(29)])).unwrap();

    assert_eq!(
        layouter.finish().children,
        [
            RecordedGroup {
                name: "panics_after_mutating_output".into(),
                inputs: vec![TestCell(26)],
                outputs: vec![],
                children: vec![],
            },
            RecordedGroup {
                name: "keyed".into(),
                inputs: vec![TestCell(29)],
                outputs: vec![],
                children: vec![],
            },
        ],
    );
}

#[test]
fn grouped_methods_preserve_mutable_self_and_returned_borrows() {
    let mut layouter = RecordingLayouter::default();
    let mut state = Stateful::default();
    let value = TestValue(vec![TestCell(30)]);

    assert_eq!(
        state.record_call(&mut layouter, value.clone()),
        Ok(value.clone()),
    );
    assert_eq!(state.calls, 1);
    assert_eq!(returns_borrowed_value(&mut layouter, &value), Ok(&value));
    assert_eq!(
        layouter.finish().children,
        [
            RecordedGroup {
                name: "record_call".into(),
                inputs: vec![TestCell(30)],
                outputs: vec![TestCell(30)],
                children: vec![],
            },
            RecordedGroup {
                name: "returns_borrowed_value".into(),
                inputs: vec![TestCell(30)],
                outputs: vec![TestCell(30)],
                children: vec![],
            },
        ],
    );
}
