use haloumi_integration_macros::DecomposeInCells;

struct Cell;
struct Included;
struct Skipped;

#[derive(DecomposeInCells)]
#[cell(Cell)]
struct Named {
    included: Included,
    #[skip]
    skipped: Skipped,
}

#[derive(DecomposeInCells)]
#[cell(Cell)]
struct Tuple(#[skip] Skipped, Included);

#[derive(DecomposeInCells)]
#[cell(Cell)]
enum Variants {
    Named {
        included: Included,
        #[skip]
        skipped: Skipped,
    },
    SkipFirst(#[skip] Skipped, Included),
    SkipLast(Included, #[skip] Skipped),
}

#[derive(DecomposeInCells)]
#[cell(Cell)]
enum HeterogeneousVariants {
    Unit,
    Single(Included),
    Pair(Included, Included),
}

#[derive(DecomposeInCells)]
#[cell(Cell)]
struct WithWhere<T>
where
    T: Clone,
{
    value: T,
}
