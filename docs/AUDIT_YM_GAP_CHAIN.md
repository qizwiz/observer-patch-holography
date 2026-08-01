# Independent audit — the OPH → Yang–Mills repair-gap chain

**Audited commit:** `25e29d12` (branch `ym-finite-gap`)
**Date:** 2026-08-01
**Auditor:** Claude Opus 5, at JH's request. Every gate below was run by the auditor on
`rule30box`; nothing in this document is relayed from a build receipt or from the authors.

**An audit is only valid for the commit it names.** If `Lean/` moves, this document is a
historical record, not a current verdict.

---

## Verdict

**PROVES-AS-CLAIMED**, for what it claims — which is a *conditional* chain, and says so in three
independent places (paper §11 title, `claims/claim_registry.yaml` tier, Lean module docstring).

No WEAKER-SIBLING, no MISSING, no aspirational naming. The failure mode this audit exists to
catch — a green build masking a substituted or weakened statement — is **not present**.

Two scoping limits are recorded in §4. Neither is a defect; both are places where the Lean
formalises less than the paper text, consistently with its own declared scope.

---

## Gate 1 — rebuilt from source

    cd /root/src/oph-lean/Lean          # NOT the repo root: no lakefile there
    lake build                          # toolchain v4.29.1, pinned by lean-toolchain

    Build completed successfully (8329 jobs).

*Note for future auditors:* the lake root is `Lean/`, not the repository root. Building from the
parent finds no `lakefile.lean`, and `elan` then downloads a **different** toolchain (v4.32.2) —
a build that fails for a reason unrelated to the mathematics. Getting this wrong is how a
"verified" build gets run against the wrong compiler.

## Gate 2 — axiom-clean

    sorry warnings ("declaration uses 'sorry'") : 0
    axiom reports  ("depends on axiom")         : 508
    reports outside {propext, Classical.choice, Quot.sound} : 0
    sorryAx                                      : 0

`RepairGapChain` goes further, and predicts this of itself in a comment
(*"expected axiom report: NONE (not even propext)"*). The compiler agrees:

    mass_gap'     does not depend on any axioms
    mass_gap_pos' does not depend on any axioms
    gap_eq'       does not depend on any axioms

`prop_8_1` and `prop_8_1_gap` report `[propext, Classical.choice, Quot.sound]` — the standard
three, nothing else.

## Gate 3 — no `sorry` / `admit` in source

    grep -rnE '^\s*(sorry|admit)\b|:=\s*(sorry|admit)\b' --include=*.lean  ->  0 real matches

**The `sorry_mentions=25` figure reported by tooling is a grep over prose and is not a proof
obligation count.** It matches docstrings that assert the *absence* of `sorry`, and
`assert_no_sorry` directives. The compiler is the only oracle that distinguishes a proof
obligation from prose about one. Do not quote the 25.

## Gate 4 — statement map (the one that catches the expensive bug)

Claim source located via `claims/claim_registry.yaml`, entry `OPH-YM-GAP`, which names
`owner_paper: extra/yang_mills_gap_clay_problem.tex` and tiers the claim
`branch_theorem_conditional_on_construction`.

Section numbering in that paper is real, not decorative: **§8** *Finite-Stage Gap*, **§11**
*Main Theorem*, **§12** *Exact Gap Accounting* — the three the Lean cites by number.

### §8, Prop 8.1 (`prop:finite-gap`) → `YangMillsProp81.prop_8_1` — **MATCH**

| paper                                            | Lean                                            |
|--------------------------------------------------|-------------------------------------------------|
| bounded-color decomposition, `q < ∞`              | `s : Finset ι`                                  |
| color expectations are orthogonal projections     | `hE : ∀ a ∈ s, IsStarProjection (Ec a)`         |
| exact gluing makes them **commute**               | `hc : Pairwise (Function.onFun Commute Ec)`     |
| repair completeness `⋂ₐ Ran(E_a) = ℂ·1`           | `hprod : s.noncommProd Ec hc = P0`              |
| `L_r^Rep ≥ c_*(I − P_{0,r})`   (5)                | `cstar • (1 - P0) ≤ ∑ a ∈ s, cstar • (1 - Ec a)` |

`L^Rep` is written out as the sum on the Lean side; the inequality is the same one.
`prop_8_1_gap` then gives the Rayleigh form `c_*‖x‖² ≤ ⟪L̃x, x⟫` on `P₀x = 0`, matching the
"gap ≥ c_*" as usually quoted.

### §11, Thm 11.1 (`thm:main`) → `RepairGapChain.mass_gap` — **MATCH**

The paper's theorem is titled *"**Conditional** positive four-dimensional compact-gauge
Yang–Mills mass gap"* and requires the continuum certificate (Assumption 9.2), the finite
transfer receipt, and the hypotheses of `thm:ec-law`, `lem:floor`, `prop:finite-gap`.

    theorem mass_gap (cert : Certificate H Lrep c_star zero) : GapAtLeast H c_star

The certificate is a **hypothesis**, exactly as the paper has it. `mass_gap_pos` gives
`Δ_YM ≥ c_* > 0`; `gap_eq` gives `Δ_YM = Δ_rep` (paper eq. 12).

### Non-vacuity — witnessed and exercised

`Certificate` is not an empty hypothesis. The file constructs a concrete branch over `ℤ`
(`c_* = 1`, nonzero spectrum `{x | 5 ≤ x}`) and then *applies* `mass_gap_pos` to it to derive
`lt 0 7`. The theorems are not vacuously true.

---

## §4 — Two limits, recorded rather than waved past

**(a) `gap_eq` is a projection of a hypothesis field.**

    theorem gap_eq (cert : …) : ∀ x, H.nonzeroSpec x ↔ Lrep.nonzeroSpec x := cert.spec_eq

The paper *derives* `Δ_YM = Δ_rep` (eq. 12) from `UHU⁻¹ = L^rep`. The Lean **assumes** it as a
`Certificate` field and restates it. That is consistent with the declared conditional scope, but
the Lean's §12 result carries strictly less than the paper's §12 does, and the docstring's
"**§12 (exact gap accounting)**" reads stronger than what is proved.

**(b) The non-vacuity witness is degenerate.**

The witness sets `H ≡ Lrep` (literally the same predicate), so `spec_eq := Iff.rfl` holds by
reflexivity. It establishes that `Certificate` is *satisfiable*. It does **not** exhibit a
non-trivial certified branch — one where `H ≠ Lrep` but their nonzero spectra coincide, which is
the situation the paper describes (there they are *unitarily conjugate*, `UHU⁻¹ = L^rep`).

A witness with `H` and `Lrep` distinct but spectrally matched would close this, and would be a
small, self-contained addition.

---

## What this audit does **not** establish

- **That Assumption 9.2 holds.** It is a hypothesis everywhere — paper, registry, and Lean all
  say so. Discharging Y1–Y6 (Mosco convergence, OS reconstruction, reflection positivity, the
  nontriviality variance floor) is the open frontier and is untouched here.
- **Anything about modules outside the chain.** 886 theorems build; this audit read four files.
- **That the paper's own proofs are correct.** Gate 4 compares the Lean *statement* to the paper
  *statement*. Whether the paper's §8 proof of (5) is sound is a mathematical question, not a
  formalisation one, and the Lean proof of `prop_8_1` is independent of it.
