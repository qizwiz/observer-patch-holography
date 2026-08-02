import Mathlib.Util.AssertNoSorry
import ObserverPatchHolography.YangMillsGap
import ObserverPatchHolography.YangMillsLemma72
import ObserverPatchHolography.YangMillsProp81
import ObserverPatchHolography.YangMillsGapWitness
import ObserverPatchHolography.RepairGapChain

/-!
# Yang-Mills repair-gap chain: theorem audit

The machine-checked counterpart of `EinsteinBranch/AxiomAudit.lean`, for the other branch.
That file guards 66 results with `assert_no_sorry`; this chain had ZERO such lines. It was NOT
unguarded, and the difference is worth stating exactly: these five files already carry 24
`#print axioms` receipts, and a `sorry` DOES surface there, as `sorryAx`. What was missing is
ENFORCEMENT. A receipt is an info line in a build log that a human has to read and notice; an
`assert_no_sorry` FAILS THE BUILD. This turns an observation nobody is obliged to look at into
a gate that cannot be walked past.

`assert_no_sorry` FAILS THE BUILD if the named constant depends on `sorryAx`, so these lines
are only worth anything when this module is built. The `#print axioms` receipts below are the
weaker but more informative half: they name every axiom each result actually rests on, so a
dependency outside {propext, Classical.choice, Quot.sound} is visible to review rather than
merely absent from a pass.

WHAT THIS DOES NOT CHECK, stated because a guard that is read as stronger than it is becomes
the very theatre it was added to prevent: `assert_no_sorry` says a proof is complete, NOT that
it proves the intended statement. `RepairGapChain.mass_gap` is explicitly conditional -- it
takes a `Certificate` whose fields BUNDLE "Lemma 7.4" (`c_star_pos`) and the continuum
transport of Prop 8.1 (`Lrep_gap`) as HYPOTHESES. Those remain assumed after every line here
passes. Sorry-freeness and unconditionality are different properties.
-/

namespace OPH.YangMillsAudit

/-! ## Lemma 7.2 -- commutant of the two-valued permutation action -/

assert_no_sorry ObserverPatchHolography.YangMillsLemma72.exists_perm_maps_two
assert_no_sorry ObserverPatchHolography.YangMillsLemma72.perm_conj_invariant
assert_no_sorry ObserverPatchHolography.YangMillsLemma72.commutant_perm_two_valued
assert_no_sorry ObserverPatchHolography.YangMillsLemma72.lemma_7_2

/-! ## Prop 8.1 -- finite commuting-color gap -/

assert_no_sorry ObserverPatchHolography.YangMillsProp81.two_proj_le
assert_no_sorry ObserverPatchHolography.YangMillsProp81.noncommProd_isStarProjection
assert_no_sorry ObserverPatchHolography.YangMillsProp81.one_sub_noncommProd_le_sum
assert_no_sorry ObserverPatchHolography.YangMillsProp81.prod_isStarProjection
assert_no_sorry ObserverPatchHolography.YangMillsProp81.prop_8_1
assert_no_sorry ObserverPatchHolography.YangMillsProp81.prop_8_1_gap

/-! ## Thm 7.3 -- finite repair gap, and the collar-rate floor -/

assert_no_sorry ObserverPatchHolography.YangMillsGap.lemma_7_2
assert_no_sorry ObserverPatchHolography.YangMillsGap.collar_rate_pos
assert_no_sorry ObserverPatchHolography.YangMillsGap.prop_8_1
assert_no_sorry ObserverPatchHolography.YangMillsGap.uniform_floor
assert_no_sorry ObserverPatchHolography.YangMillsGap.thm_7_3_finite_gap

/-! ## Non-vacuity witness -- Thm 7.3 has an inhabited instance -/

assert_no_sorry ObserverPatchHolography.YangMillsGapWitness.whne
assert_no_sorry ObserverPatchHolography.YangMillsGapWitness.whE
assert_no_sorry ObserverPatchHolography.YangMillsGapWitness.whc
assert_no_sorry ObserverPatchHolography.YangMillsGapWitness.wP0_eq_zero
assert_no_sorry ObserverPatchHolography.YangMillsGapWitness.whrate
assert_no_sorry ObserverPatchHolography.YangMillsGapWitness.thm_7_3_finite_gap_nonvacuous
assert_no_sorry ObserverPatchHolography.YangMillsGapWitness.repairGenerator_eq

/-! ## Conditional continuum assembly (Thm 11.1) -- COMPLETE, not unconditional -/

assert_no_sorry ObserverPatchHolography.RepairGapChain.mass_gap
assert_no_sorry ObserverPatchHolography.RepairGapChain.mass_gap_pos
assert_no_sorry ObserverPatchHolography.RepairGapChain.gap_eq
assert_no_sorry ObserverPatchHolography.RepairGapChain.spec_eq_of_conj
assert_no_sorry ObserverPatchHolography.RepairGapChain.Sdata_ne_Tdata
assert_no_sorry ObserverPatchHolography.RepairGapChain.Sdata_val_eq

/-! ## Axiom receipts -/

#print axioms ObserverPatchHolography.YangMillsLemma72.lemma_7_2
#print axioms ObserverPatchHolography.YangMillsProp81.prop_8_1
#print axioms ObserverPatchHolography.YangMillsProp81.prop_8_1_gap
#print axioms ObserverPatchHolography.YangMillsGap.thm_7_3_finite_gap
#print axioms ObserverPatchHolography.YangMillsGapWitness.thm_7_3_finite_gap_nonvacuous
#print axioms ObserverPatchHolography.RepairGapChain.mass_gap
#print axioms ObserverPatchHolography.RepairGapChain.mass_gap_pos
#print axioms ObserverPatchHolography.RepairGapChain.gap_eq

end OPH.YangMillsAudit
