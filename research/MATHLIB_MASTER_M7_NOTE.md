# M7 rider — Mathlib MASTER re-check for the two candidate PR lemmas (2026-07-08)

**INTERNAL NOTE — never for an upstream branch.** Input to the H-M2 decision
(Mathlib PR yes/no), per MASTER_PLAN item M7 (downgraded to a grep rider on M1).

Scope, verbatim: Machine-checked: the finite representation gap Δ_rep ≥ c_* > 0
(Lemma 7.2 / Lemma 7.4 / Prop 8.1 / Thm 7.3 assembly) and the conditional
reduction "Assumption 9.2 + finite gap ⇒ Δ_YM ≥ c_*". Assumption 9.2 itself is
stated as an explicit hypothesis and is not touched.

## Question

Does Mathlib **master** (not just the v4.29.1 we pin) already have:

1. `noncommProd_isStarProjection` — the `Finset.noncommProd` of a pairwise-commuting
   family of star projections is a star projection
   (ours: `ObserverPatchHolography.YangMillsProp81.noncommProd_isStarProjection`);
2. `one_sub_noncommProd_le_sum` — `1 − ∏ₐ pₐ ≤ ∑ₐ (1 − pₐ)` for a commuting family
   of star projections (ours, stated on `E →L[ℝ] E` in the Loewner order).

## Verdict: BOTH ABSENT from master (verified 2026-07-08)

| Candidate | Master status | Evidence |
|---|---|---|
| Finset/noncommProd star-projection closure | **ABSENT** | Full read of raw master `Mathlib/Algebra/Star/StarProjection.lean` (146 lines, fetched 2026-07-08): only *pairwise* `IsStarProjection.mul` (commuting), `.add` (orthogonal, `p*q=0`), `.one_sub`, `.sub_of_mul_eq_left/right`, `.sub_iff_mul_eq_left/right`, `add_sub_mul_of_commute`. No `Finset`, no `noncommProd` anywhere in the file. |
| `1 − ∏ ≤ ∑ (1 − pₐ)` (any generality) | **ABSENT** | `gh search code` on master repo: `one_sub_noncommProd_le_sum` → 0 hits; `sub_noncommProd` → 0; `noncommProd_le` → 0 relevant (only `noncommProd_lemma` plumbing in `Data/Finset/NoncommProd.lean`); `noncommProd IsStarProjection` → 0; `noncommProd IsIdempotentElem` → 0; `isStarProjection_noncommProd` → 0; `one_sub_le_sum` → 0; `StarOrderedRing IsStarProjection` → 0. |

Caveat on method: gh code search indexes the default branch (= master) but absence
via search alone is weak; for candidate 1 the claim rests on the **full raw-file
read** of the one file where the `IsStarProjection` API lives, which is strong.
For candidate 2 there is no single canonical home, so the multi-query absence is
the best available evidence short of a full clone-grep. Confidence: high.

## Implication for H-M2 (JH decides)

- Both lemmas are genuinely missing upstream → a 2-lemma Mathlib PR is live.
- Natural generality to try (per MASTER_PLAN M7): candidate 1 sits in
  `Mathlib/Algebra/Star/StarProjection.lean` next to `.mul` — it needs only
  `NonUnitalSemiring R`/`StarRing R` + `Finset.noncommProd` (induction via
  `Finset.cons_induction` + `Finset.noncommProd_commute`, exactly our proof,
  which is already ring-generic in structure — the `E →L[ℝ] E` specialization
  is incidental).
- Candidate 2 needs an order: try `StarOrderedRing R` — `1 − p` is a star
  projection and star projections are `0 ≤ ·` in a StarOrderedRing
  (`IsStarProjection` → `star p * p = p` → `0 ≤ p`), and the two-projection step
  `(1−p)(1−q) = ((1−p)+(1−q)) − (1−p·q)` is pure ring algebra. If that works,
  the Loewner `E →L[ℝ] E` version we use is an instance.
- Cost if submitted: Mathlib review cycles (human-latency, weeks). Benefit:
  independent citable external review channel regardless of Bernhard.

Next action lives with JH (H-M2). No branch was cut, no build run for this rider.
