use std::{collections::HashMap, convert::Infallible};

use ff::Field;
use haloumi_core::expressions::{EvaluableExpr, ExprBuilder, ExpressionInfo};
use haloumi_ir::{Slot, meta::HasMeta as _, stmt::IRStmt};
use haloumi_synthesis::SynthesizedCircuit;

use crate::{
    expressions::{ScopedExpression, UnresolvedExpr},
    groups::{IRGroupGenError, prepend_comment},
    lookups::{
        callbacks::LookupCallbacks,
        table::{LookupTableGenerator, tables_for_lookup},
    },
    regions::region_row::RegionRow,
    temps::{ExprOrTemp, Temp, Temps},
};

pub fn codegen_lookup_invocations<'sco, 'syn, 'ctx, 'cb, F, E>(
    syn: &'syn SynthesizedCircuit<F, E>,
    region_rows: &[RegionRow<'syn, 'ctx, 'syn, F>],
    lookup_cb: &'cb dyn LookupCallbacks<F, E>,
    generate_debug_comments: bool,
) -> Result<Vec<IRStmt<UnresolvedExpr<'syn, 'sco, F, E>>>, IRGroupGenError>
where
    'syn: 'sco,
    'ctx: 'sco + 'syn,
    'cb: 'sco + 'syn,
    F: Field + Ord,
    E: Clone + ExpressionInfo + EvaluableExpr<F> + ExprBuilder<F> + std::fmt::Debug,
{
    let lookups = syn.lookups().iter().collect::<Vec<_>>();
    let tables_sto = lookups
        .iter()
        .map(|lookup| tables_for_lookup(syn, lookup))
        .collect::<Vec<_>>();
    let tables = tables_sto
        .iter()
        .map(|t| -> &dyn LookupTableGenerator<F> { t })
        .collect::<Vec<_>>();
    let mut temps = Temps::new();
    let ir = lookup_cb.on_lookups(&lookups, &tables, &mut temps)?;
    region_rows
        .iter()
        .enumerate()
        .map(|(n, rr)| {
            let mut region_ir = ir.map_into(&mut |e| {
                e.map_into(|e| ScopedExpression::from_ref(e.as_ref(), *rr).simplified())
            });
            region_ir.meta_mut().at_row(rr.row_number());

            // The IR representing the lookup is generated only once, with a sequence of temps
            // 0,1,...
            // When the IR is cloned under the scope of a region row the temporaries
            // have the same ids as the original. This causes collissions between the variable
            // names of the temporaries across the region rows.
            //
            // To avoid this, starting from region row #1, the temporaries are renamed to a fresh
            // new set. The `rebase_temps` method accepts a closure representing the mapping
            // between the original name and the new name, which is implemented with a HashMap
            // that creates a fresh temporary every time a new temporary is encountered. All
            // temporaries are created from the same `Temps` instance and thus will be unique
            // across the body of the group.
            if n > 0 {
                rebase_temps(&mut region_ir, &mut temps);
            }

            Ok(prepend_comment(
                region_ir,
                || IRStmt::comment(format!("Lookups @ {} @ {}", rr.header(), rr.row_number())),
                generate_debug_comments,
            ))
        })
        .collect()
}

/// Renames all temporaries in call outputs and [`ExprOrTemp::Temp`] to a fresh new set.
///
/// It doesn't go inside `T` so it won't rename temporaries inside it.
fn rebase_temps<T: std::fmt::Debug>(stmt: &mut IRStmt<ExprOrTemp<T>>, temps: &mut Temps) {
    log::debug!("Rebasing lookup IR: {stmt:?}");
    let mut local_temps = HashMap::new();
    stmt.try_map_inplace(&mut |expr| -> Result<(), Infallible> {
        if let ExprOrTemp::Temp(temp) = expr {
            let new_temp = *local_temps
                .entry(*temp)
                .or_insert_with(|| temps.next().unwrap());
            log::debug!("Replacing temp {temp:?} in expr with {new_temp:?}");
            *temp = new_temp;
        }
        Ok(())
    })
    .unwrap();
    stmt.try_map_slot_inplace(&mut |slot| -> Result<(), Infallible> {
        if let Slot::Temp(temp) = slot {
            let new_temp = **local_temps
                .entry(Temp(*temp))
                .or_insert_with(|| temps.next().unwrap());
            log::debug!("Replacing temp {temp:?} in slot with {new_temp:?}");
            *temp = new_temp;
        }
        Ok(())
    })
    .unwrap();
}

#[cfg(test)]
mod tests {
    use super::*;

    type S = IRStmt<ExprOrTemp<()>>;

    #[test]
    fn test_rebase_temps() {
        let mut temps = Temps::new();

        let mut input_stmt = S::call(
            "called module",
            [ExprOrTemp::Temp(temps.next().unwrap())],
            [temps.next().unwrap().into()],
        );
        let expected_stmt = S::call(
            "called module",
            [ExprOrTemp::Temp(Temp(2))],
            [Slot::Temp(3)],
        );

        rebase_temps(&mut input_stmt, &mut temps);
        assert_eq!(input_stmt, expected_stmt);
    }

    #[test]
    fn test_rebase_temps_2() {
        let mut temps = Temps::new();

        let base_input_stmt = S::call(
            "called module",
            [ExprOrTemp::Temp(temps.next().unwrap())],
            [temps.next().unwrap().into()],
        );
        let mut input_stmt = [base_input_stmt.clone(), base_input_stmt];
        let expected_stmt = [
            S::call(
                "called module",
                [ExprOrTemp::Temp(Temp(2))],
                [Slot::Temp(3)],
            ),
            S::call(
                "called module",
                [ExprOrTemp::Temp(Temp(4))],
                [Slot::Temp(5)],
            ),
        ];

        for stmt in &mut input_stmt {
            rebase_temps(stmt, &mut temps);
        }
        assert_eq!(input_stmt, expected_stmt);
    }

    #[test]
    fn test_rebase_temps_3() {
        let mut temps = Temps::new();

        let base_input_stmt = S::seq([
            S::comment("begin block"),
            S::call(
                "called module",
                [ExprOrTemp::Temp(temps.next().unwrap())],
                [temps.next().unwrap().into()],
            ),
            S::call(
                "second module",
                [ExprOrTemp::Temp(temps.next().unwrap())],
                [temps.next().unwrap().into()],
            ),
            S::comment("end block"),
        ]);
        let mut input_stmt = [
            base_input_stmt.clone(),
            base_input_stmt.clone(),
            base_input_stmt,
        ];
        let expected_stmt = S::seq([
            S::comment("begin block"),
            S::call(
                "called module",
                [ExprOrTemp::Temp(Temp(0))],
                [Slot::Temp(1)],
            ),
            S::call(
                "second module",
                [ExprOrTemp::Temp(Temp(2))],
                [Slot::Temp(3)],
            ),
            S::comment("end block"),
            S::comment("begin block"),
            S::call(
                "called module",
                [ExprOrTemp::Temp(Temp(4))],
                [Slot::Temp(6)],
            ),
            S::call(
                "second module",
                [ExprOrTemp::Temp(Temp(5))],
                [Slot::Temp(7)],
            ),
            S::comment("end block"),
            S::comment("begin block"),
            S::call(
                "called module",
                [ExprOrTemp::Temp(Temp(8))],
                [Slot::Temp(10)],
            ),
            S::call(
                "second module",
                [ExprOrTemp::Temp(Temp(9))],
                [Slot::Temp(11)],
            ),
            S::comment("end block"),
        ]);

        for (n, stmt) in input_stmt.iter_mut().enumerate() {
            if n > 0 {
                rebase_temps(stmt, &mut temps);
            }
        }
        let input_stmt = S::seq(input_stmt);
        assert_eq!(input_stmt, expected_stmt);
    }
}
