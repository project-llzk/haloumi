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
                let mut local_temps = HashMap::new();
                rebase_temps(&mut region_ir, &mut |temp| {
                    *local_temps
                        .entry(temp)
                        .or_insert_with(|| temps.next().unwrap())
                });
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
fn rebase_temps<T>(stmt: &mut IRStmt<ExprOrTemp<T>>, renaming_fn: &mut impl FnMut(Temp) -> Temp) {
    stmt.try_map_inplace(&mut |expr| -> Result<(), Infallible> {
        if let ExprOrTemp::Temp(temp) = expr {
            *temp = renaming_fn(*temp);
        }
        Ok(())
    })
    .unwrap();
    stmt.try_map_slot_inplace(&mut |slot| -> Result<(), Infallible> {
        if let Slot::Temp(temp) = slot {
            *temp = *renaming_fn(Temp(*temp));
        }
        Ok(())
    })
    .unwrap();
}
