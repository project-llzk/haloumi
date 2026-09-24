use haloumi_integration::core::table::DecomposeIn;
use haloumi_integration_macros::DecomposeInCells;

#[derive(Debug, PartialEq, Eq)]
struct Cell(u8);

struct Included(u8);

impl DecomposeIn<Cell> for Included {
    fn cells(&self) -> impl IntoIterator<Item = Cell> {
        [Cell(self.0)]
    }
}

struct SkippedWithImplementation(u8);

impl DecomposeIn<Cell> for SkippedWithImplementation {
    fn cells(&self) -> impl IntoIterator<Item = Cell> {
        [Cell(self.0)]
    }
}

struct SkippedWithoutImplementation;

#[derive(DecomposeInCells)]
#[cell(Cell)]
struct Named {
    included: Included,
    #[skip]
    skipped: SkippedWithImplementation,
}

#[derive(DecomposeInCells)]
#[cell(Cell)]
struct Tuple(#[skip] SkippedWithoutImplementation, Included);

#[derive(DecomposeInCells)]
#[cell(Cell)]
enum Variants {
    Named {
        included: Included,
        #[skip]
        skipped: SkippedWithImplementation,
    },
    SkipFirst(#[skip] SkippedWithoutImplementation, Included),
    SkipLast(Included, #[skip] SkippedWithoutImplementation),
}

fn cells(value: impl DecomposeIn<Cell>) -> Vec<Cell> {
    value.cells().into_iter().collect()
}

#[test]
fn skipped_fields_are_not_decomposed_or_bounded() {
    assert_eq!(
        cells(Named {
            included: Included(1),
            skipped: SkippedWithImplementation(99),
        }),
        [Cell(1)],
    );
    assert_eq!(
        cells(Tuple(SkippedWithoutImplementation, Included(2))),
        [Cell(2)],
    );
    assert_eq!(
        cells(Variants::Named {
            included: Included(3),
            skipped: SkippedWithImplementation(99),
        }),
        [Cell(3)],
    );
    assert_eq!(
        cells(Variants::SkipFirst(
            SkippedWithoutImplementation,
            Included(4)
        )),
        [Cell(4)],
    );
    assert_eq!(
        cells(Variants::SkipLast(
            Included(5),
            SkippedWithoutImplementation
        )),
        [Cell(5)],
    );
}

#[test]
fn expansion() {
    macrotest::expand_args("tests/expand/decompose_in_cells/pass/*.rs", ["--ugly"]);
}
