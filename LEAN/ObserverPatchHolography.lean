import ObserverPatchHolography.AbstractRewriting
import ObserverPatchHolography.Primitives
import ObserverPatchHolography.Rule90
import ObserverPatchHolography.YangMillsLemma72
import ObserverPatchHolography.YangMillsProp81
import ObserverPatchHolography.YangMillsGap
import ObserverPatchHolography.RepairGapChain

/-!
# Observer-Patch Holography — Lean 4 library root

Re-exports the modules that make up the OPH formalisation effort.

## Yang–Mills finite repair-gap modules (Müller r1515, §§7–9)

`YangMillsLemma72` (keystone Lemma 7.2), `YangMillsProp81` (Prop 8.1 gap
engine), `YangMillsGap` (Thm 7.3 / Lemma 7.4 assembly), and `RepairGapChain`
(the conditional continuum chain). Machine-checked: the finite representation
gap Δ_rep ≥ c_* > 0 (Lemma 7.2 / Lemma 7.4 / Prop 8.1 / Thm 7.3 assembly) and
the conditional reduction "Assumption 9.2 + finite gap ⇒ Δ_YM ≥ c_*".
Assumption 9.2 itself is stated as an explicit hypothesis and is not touched.

**Current state is a preliminary skeleton, not a theorem-grade
formalisation of Proposition 4.2** from *Paradise as Fixed-Point
Consensus*. The `Primitives` module declares sorry-bearing signatures for
the OPH primitives (Records, Repair, Patch, Obs, Φ, gauge equivalence,
OPH-Confluence, OPH-Completeness) — these structurally depend on the
companion paper *Reality as a Consensus Protocol*.

See `README.md` and `PROOF_INDEX.md` for scope and completion tracking.
-/
