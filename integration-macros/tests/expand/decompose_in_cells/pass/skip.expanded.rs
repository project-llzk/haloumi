use haloumi_integration_macros::DecomposeInCells;
struct Cell;
struct Included;
struct Skipped;
#[cell(Cell)]
struct Named {
    included: Included,
    #[skip]
    skipped: Skipped,
}
impl haloumi_integration::core::table::DecomposeIn<Cell> for Named
where
    Included: haloumi_integration::core::table::DecomposeIn<Cell>,
{
    fn cells(&self) -> impl IntoIterator<Item = Cell> {
        std::iter::empty().chain(self.included.cells())
    }
}
#[cell(Cell)]
struct Tuple(#[skip] Skipped, Included);
impl haloumi_integration::core::table::DecomposeIn<Cell> for Tuple
where
    Included: haloumi_integration::core::table::DecomposeIn<Cell>,
{
    fn cells(&self) -> impl IntoIterator<Item = Cell> {
        std::iter::empty().chain(self.1.cells())
    }
}
#[cell(Cell)]
enum Variants {
    Named { included: Included, #[skip] skipped: Skipped },
    SkipFirst(#[skip] Skipped, Included),
    SkipLast(Included, #[skip] Skipped),
}
impl haloumi_integration::core::table::DecomposeIn<Cell> for Variants
where
    Included: haloumi_integration::core::table::DecomposeIn<Cell>,
    Included: haloumi_integration::core::table::DecomposeIn<Cell>,
    Included: haloumi_integration::core::table::DecomposeIn<Cell>,
{
    fn cells(&self) -> impl IntoIterator<Item = Cell> {
        match self {
            Self::Named { included, skipped: _ } => {
                (std::iter::empty().chain(included.cells())).collect::<Vec<_>>()
            }
            Self::SkipFirst(_, __1) => {
                (std::iter::empty().chain(__1.cells())).collect::<Vec<_>>()
            }
            Self::SkipLast(__0, _) => {
                (std::iter::empty().chain(__0.cells())).collect::<Vec<_>>()
            }
        }
    }
}
#[cell(Cell)]
enum HeterogeneousVariants {
    Unit,
    Single(Included),
    Pair(Included, Included),
}
impl haloumi_integration::core::table::DecomposeIn<Cell> for HeterogeneousVariants
where
    Included: haloumi_integration::core::table::DecomposeIn<Cell>,
    Included: haloumi_integration::core::table::DecomposeIn<Cell>,
    Included: haloumi_integration::core::table::DecomposeIn<Cell>,
{
    fn cells(&self) -> impl IntoIterator<Item = Cell> {
        match self {
            Self::Unit => (std::iter::empty()).collect::<Vec<_>>(),
            Self::Single(__0) => {
                (std::iter::empty().chain(__0.cells())).collect::<Vec<_>>()
            }
            Self::Pair(__0, __1) => {
                (std::iter::empty().chain(__0.cells()).chain(__1.cells()))
                    .collect::<Vec<_>>()
            }
        }
    }
}
#[cell(Cell)]
struct WithWhere<T>
where
    T: Clone,
{
    value: T,
}
impl<T> haloumi_integration::core::table::DecomposeIn<Cell> for WithWhere<T>
where
    T: Clone,
    T: haloumi_integration::core::table::DecomposeIn<Cell>,
{
    fn cells(&self) -> impl IntoIterator<Item = Cell> {
        std::iter::empty().chain(self.value.cells())
    }
}
