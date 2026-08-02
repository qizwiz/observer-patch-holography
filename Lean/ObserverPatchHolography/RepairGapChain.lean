/-
  RepairGapChain.lean — the OPH → Yang–Mills CONDITIONAL CHAIN, machine-checked.

  Self-contained (core Lean 4, NO Mathlib import), so it compiles + checks standalone
  with plain `lean` — no heavy Mathlib build required.

  Formalizes the LOGICAL ARCHITECTURE of
    B. Müller, "Explaining the Yang–Mills Mass Gap with Observer-Patch Repair Dynamics":
      finite repair-gap (UNCONDITIONAL, Prop 8.1)  +  Assumption 9.2 (continuum certificate)
        ⟹  positive continuum mass gap  Δ_YM ≥ c_* > 0   (Thm 11.1),
        and  Δ_YM = Δ_rep   (§12, exact gap accounting).

  HONEST SCOPE (score-function discipline — do NOT overclaim):
    * Only the CHAIN is proved here: "IF the certificate holds, the mass gap follows."
    * The certificate's deep analysis (Assumption 9.2 items Y1–Y6: Mosco convergence of
      the transfer forms, OS reconstruction, reflection positivity, the nontriviality
      variance floor) is encoded as HYPOTHESES (the `Certificate` structure), NOT proved.
      Discharging them is the genuine open frontier (constructive QFT); this file does not
      touch it and does not claim to.
    * The finite gap (Prop 8.1: commuting-color projections ⟹ Δ_rep ≥ c_*) is the
      unconditional input; its operator-theoretic proof lives in the sibling
      Mathlib-typed modules (`YangMillsLemma72`, `YangMillsProp81`, `YangMillsGap`).
      Here it enters as the `Lrep_gap` hypothesis.

  What this file BUYS: a machine check that the paper's conditional claim is logically
  valid — the reduction of the mass-gap claim to Assumption 9.2 is sound.

  SCOPE, verbatim: Machine-checked: the finite representation gap Δ_rep ≥ c_* > 0
  (Lemma 7.2 / Lemma 7.4 / Prop 8.1 / Thm 7.3 assembly) and the conditional reduction
  "Assumption 9.2 + finite gap ⇒ Δ_YM ≥ c_*". Assumption 9.2 itself is stated as an
  explicit hypothesis and is not touched.
-/

namespace ObserverPatchHolography.RepairGapChain

/-- Minimal order structure — exactly the two order facts the mass-gap chain uses.
    (Kept self-contained instead of importing Mathlib's `Preorder`.) -/
class GapOrder (α : Type) where
  le : α → α → Prop
  lt : α → α → Prop
  le_trans : ∀ {a b c : α}, le a b → le b c → le a c
  lt_of_lt_of_le : ∀ {a b c : α}, lt a b → le b c → lt a c

open GapOrder

variable {α : Type} [GapOrder α]

/-- A self-adjoint operator, modeled by its nonzero spectrum (a predicate on gap-values).
    Faithful abstraction: all the mass-gap argument needs is which values are nonzero
    spectrum, since Δ(O) := inf(Spec(O) \ {0}). -/
structure Op (α : Type) where
  nonzeroSpec : α → Prop

/-- "The gap of `O` is at least `c`": every nonzero spectral value is ≥ c.
    This is exactly the paper's spectral statement  Spec(O) ∩ (0, c) = ∅,  i.e. Δ(O) ≥ c. -/
def GapAtLeast (O : Op α) (c : α) : Prop := ∀ x, O.nonzeroSpec x → le c x

/-- Assumption 9.2 (continuum certificate) together with the finite gap (Prop 8.1),
    bundled as the HYPOTHESES on which Müller's conditional theorem rests.
    `H` = continuum Yang–Mills Hamiltonian, `Lrep` = continuum repair generator. -/
structure Certificate (H Lrep : Op α) (c_star zero : α) : Prop where
  /-- Lemma 7.4 (uniform active-collar rate floor): the repair rate is strictly positive. -/
  c_star_pos : lt zero c_star
  /-- Prop 8.1 (finite commuting-color gap) transported to the continuum by Thm 9.3
      (the generalized Mosco limit — Assumption 9.2 item Y4): Δ_rep ≥ c_*. -/
  Lrep_gap : GapAtLeast Lrep c_star
  /-- §12 exact gap accounting: on the certified branch  H = U⁻¹ L^rep U  (Thm 9.3, eq. 9),
      and unitary conjugation preserves the spectrum, so H and L^rep share their nonzero
      spectrum. This is the certified form of  Δ_YM = Δ_rep. -/
  spec_eq : ∀ x, H.nonzeroSpec x ↔ Lrep.nonzeroSpec x

/-- **Theorem 11.1 (conditional positive mass gap).**
    Under the continuum certificate, the Yang–Mills Hamiltonian H has gap ≥ c_*. -/
theorem mass_gap {H Lrep : Op α} {c_star zero : α}
    (cert : Certificate H Lrep c_star zero) : GapAtLeast H c_star := by
  intro x hx
  exact cert.Lrep_gap x ((cert.spec_eq x).mp hx)

/-- The gap is **strictly positive** — the actual "mass gap": every nonzero spectral
    value of H exceeds 0.  `Spec(H) ∩ (0, c_*) = ∅` with `c_* > 0`. -/
theorem mass_gap_pos {H Lrep : Op α} {c_star zero : α}
    (cert : Certificate H Lrep c_star zero) :
    ∀ x, H.nonzeroSpec x → lt zero x := by
  intro x hx
  exact lt_of_lt_of_le cert.c_star_pos (mass_gap cert x hx)

/-- **§12 (exact gap accounting): Δ_YM = Δ_rep.**  H and L^rep have the same nonzero
    spectrum on the certified branch, so their gaps coincide. -/
theorem gap_eq {H Lrep : Op α} {c_star zero : α}
    (cert : Certificate H Lrep c_star zero) :
    ∀ x, H.nonzeroSpec x ↔ Lrep.nonzeroSpec x := cert.spec_eq

/- --------------------------------------------------------------------------
   NON-VACUITY: ℤ models the order and a concrete certified branch exists, so
   `Certificate` is satisfiable and the theorems above are not vacuously true.
   -------------------------------------------------------------------------- -/

instance : GapOrder Int where
  le := (· ≤ ·)
  lt := (· < ·)
  le_trans := by intro a b c h1 h2; omega
  lt_of_lt_of_le := by intro a b c h1 h2; omega

/-- A concrete certified branch over ℤ: repair rate `c_* = 1`, and both H and L^rep
    have nonzero spectrum `{ x | 5 ≤ x }` (gap 5 ≥ 1 > 0). Witnesses that the
    hypotheses are jointly satisfiable. -/
example : Certificate (α := Int) ⟨fun x => (5 : Int) ≤ x⟩ ⟨fun x => (5 : Int) ≤ x⟩ 1 0 where
  c_star_pos := by show (0 : Int) < 1; omega
  Lrep_gap := by
    intro x hx
    show (1 : Int) ≤ x
    have h5 : (5 : Int) ≤ x := hx
    omega
  spec_eq := fun _ => Iff.rfl

/-- Sanity: on that branch the mass gap is genuinely positive (a nonzero spectral
    value, say 7, is > 0). -/
example :
    lt (0 : Int) 7 :=
  mass_gap_pos
    (H := ⟨fun x => (5 : Int) ≤ x⟩) (Lrep := ⟨fun x => (5 : Int) ≤ x⟩)
    (c_star := 1) (zero := 0)
    { c_star_pos := by show (0 : Int) < 1; omega
      Lrep_gap := by intro x hx; show (1 : Int) ≤ x; have : (5:Int) ≤ x := hx; omega
      spec_eq := fun _ => Iff.rfl }
    7 (by show (5 : Int) ≤ 7; omega)


/-- **Non-degenerate certified branch** -- closes a limit this chain's own audit recorded
    (docs/AUDIT_YM_GAP_CHAIN.md section 4(b), 2026-08-01).

    The witness above establishes that `Certificate` is SATISFIABLE, but it sets H and Lrep
    to the *same term*, so `spec_eq` discharges by `Iff.rfl`. That is weaker than the
    situation the paper describes: there H and Lrep are DISTINCT operators related by
    H = U inv Lrep U (Thm 9.3, eq. 9), whose nonzero spectra coincide only because unitary
    conjugation preserves the spectrum. A witness in which the two coincide DEFINITIONALLY
    cannot exhibit that, and so cannot rule out a reading in which the chain is only ever
    applied to H identical to Lrep.

    Here the predicates are `0 < x - 4` and `5 <= x`: extensionally equal over the integers,
    but NOT definitionally equal, so `spec_eq` needs an actual arithmetic proof. Verified in
    BOTH directions before committing -- with `spec_eq := fun _ => Iff.rfl` the file fails to
    elaborate:

        error: Type mismatch
          Iff.rfl  has type  ?m <-> ?m
          but is expected to have type
          { nonzeroSpec := fun x => 0 < x - 4 }.nonzeroSpec x <->
          { nonzeroSpec := fun x => 5 <= x }.nonzeroSpec x

    so the non-degeneracy is enforced by the compiler, not asserted in a comment. This is
    the section-12 shape in miniature: ONE spectrum, TWO presentations. -/
example : Certificate (α := Int) ⟨fun x => (0 : Int) < x - 4⟩ ⟨fun x => (5 : Int) ≤ x⟩ 1 0 where
  c_star_pos := by show (0 : Int) < 1; omega
  Lrep_gap := by
    intro x hx
    show (1 : Int) ≤ x
    have h5 : (5 : Int) ≤ x := hx
    omega
  spec_eq := by
    intro x
    show (0 : Int) < x - 4 ↔ (5 : Int) ≤ x
    constructor <;> intro h <;> omega

/-- Sanity on the NON-degenerate branch: the chain still delivers a strictly positive gap,
    and the spectral value enters through H's own presentation (`0 < 7 - 4`) rather than
    Lrep's, so the transport across `spec_eq` is actually exercised. -/
example :
    lt (0 : Int) 7 :=
  mass_gap_pos
    (H := ⟨fun x => (0 : Int) < x - 4⟩) (Lrep := ⟨fun x => (5 : Int) ≤ x⟩)
    (c_star := 1) (zero := 0)
    { c_star_pos := by show (0 : Int) < 1; omega
      Lrep_gap := by intro x hx; show (1 : Int) ≤ x; have : (5:Int) ≤ x := hx; omega
      spec_eq := by
        intro x
        show (0 : Int) < x - 4 ↔ (5 : Int) ≤ x
        constructor <;> intro h <;> omega }
    7 (by show (0 : Int) < 7 - 4; omega)


/-! ## §12 DERIVED, not assumed — closing audit limit (a)

    `gap_eq` returns `cert.spec_eq`: the Lean ASSUMED the spectral equality and restated it,
    while the paper DERIVES eq. 12 from `U H U⁻¹ = L^rep` (unitary conjugation preserves the
    spectrum). The audit recorded that as carrying strictly less than §12 does.

    The honest fix is not to delete the field — `Certificate` is a hypothesis bundle and must
    stay one — but to show the field is DERIVABLE from data more primitive than itself, so a
    branch can discharge it by proof instead of by assumption.

    The hazard here is a tautology: "conjugate operators have equal spectra" is trivial if
    `conjugate` is *defined* as "equal spectra". So conjugation is modelled by REINDEXING —
    a bijection of basis indices carrying each eigenvalue to the same eigenvalue — and the
    equality of spectra is then a theorem whose proof uses both directions of that bijection. -/

/-- A bijection, spelled out because this file imports no Mathlib. -/
structure Reindex (β γ : Type) where
  to : β → γ
  inv : γ → β
  left_inv : ∀ b, inv (to b) = b
  right_inv : ∀ c, to (inv c) = c

/-- An operator presented by its spectral DATA: an index set (a basis) and the eigenvalue
    carried by each index. Strictly more information than `Op`, which records only the SET. -/
structure SpectralData (α : Type) where
  idx : Type
  val : idx → α

/-- The `Op` induced by spectral data, given the ambient "is a nonzero value" predicate. -/
def SpectralData.op (nz : α → Prop) (S : SpectralData α) : Op α :=
  ⟨fun x => nz x ∧ ∃ i, S.val i = x⟩

/-- **Eq. 12, derived.** If `S` and `T` are related by a reindexing that preserves every
    eigenvalue — the discrete shadow of `U H U⁻¹ = L^rep` — then they have the same nonzero
    spectrum. Both directions of the bijection are used, which is what makes this a proof
    rather than a restatement. -/
theorem spec_eq_of_conj {α : Type} {nz : α → Prop} {S T : SpectralData α}
    (e : Reindex S.idx T.idx) (hval : ∀ i, S.val i = T.val (e.to i)) :
    ∀ x, (SpectralData.op nz S).nonzeroSpec x ↔ (SpectralData.op nz T).nonzeroSpec x := by
  intro x
  constructor
  · intro h
    cases h with
    | intro hx hex =>
      cases hex with
      | intro i hi =>
        exact ⟨hx, e.to i, by rw [← hval i]; exact hi⟩
  · intro h
    cases h with
    | intro hx hex =>
      cases hex with
      | intro j hj =>
        refine ⟨hx, e.inv j, ?_⟩
        rw [hval (e.inv j), e.right_inv j]
        exact hj

/-! ### A branch where §12 is PROVED rather than assumed

    The two operators below carry the SAME two eigenvalues `{5, 7}` attached to the OPPOSITE
    basis indices, and the reindexing is `not` — genuinely not the identity. So `spec_eq` is
    obtained by transporting along a bijection, which is the discrete content of
    "unitary conjugation preserves the spectrum", rather than by hypothesis. -/

/-- Eigenvalue 5 at index `true`, 7 at index `false`. -/
def Sdata : SpectralData Int := ⟨Bool, fun b => if b then (5 : Int) else 7⟩

/-- The SAME eigenvalues, attached the other way round — a genuinely different assignment. -/
def Tdata : SpectralData Int := ⟨Bool, fun b => if b then (7 : Int) else 5⟩

/-- These are not the same operator DATA: they disagree at index `true`. Without this the
    "derivation" could be transporting along the identity and nobody would notice. -/
theorem Sdata_ne_Tdata : Sdata.val true ≠ Tdata.val true := by decide

/-- `not` as a reindexing: the basis permutation implementing the conjugation. -/
def swapBool : Reindex Bool Bool where
  to := not
  inv := not
  left_inv := by intro b; cases b <;> rfl
  right_inv := by intro b; cases b <;> rfl

/-- Every eigenvalue is preserved under the reindexing — the hypothesis `U H U⁻¹ = L^rep`
    supplies in the real setting. -/
theorem Sdata_val_eq : ∀ i, Sdata.val i = Tdata.val (swapBool.to i) := by
  intro i; cases i <;> rfl

/-- **The closure of audit limit (a).** A `Certificate` whose `spec_eq` field is DISCHARGED BY
    PROOF — `spec_eq_of_conj` applied to a non-identity basis permutation — instead of being
    assumed. `Certificate` still bundles it as a hypothesis, which is correct for a conditional
    theorem; what changes is that a branch can now supply it from more primitive data, exactly
    as the paper derives eq. 12 from `U H U⁻¹ = L^rep`. -/
example : Certificate (α := Int)
    (SpectralData.op (fun x => (5 : Int) ≤ x) Sdata)
    (SpectralData.op (fun x => (5 : Int) ≤ x) Tdata) 1 0 where
  c_star_pos := by show (0 : Int) < 1; omega
  Lrep_gap := by
    intro x hx
    show (1 : Int) ≤ x
    have h5 : (5 : Int) ≤ x := hx.1
    omega
  spec_eq := spec_eq_of_conj swapBool Sdata_val_eq

/-! ## Axiom self-audit (build-log visible)

`mass_gap` / `mass_gap_pos` / `gap_eq` are pure logic over the `Certificate`
hypotheses — expected axiom report: NONE (not even propext). -/

#print axioms mass_gap
#print axioms mass_gap_pos
#print axioms gap_eq
#print axioms spec_eq_of_conj

end ObserverPatchHolography.RepairGapChain
