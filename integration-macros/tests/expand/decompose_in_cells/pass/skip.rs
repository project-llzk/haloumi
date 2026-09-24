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
