import Mathlib

/-!
# Yang–Mills finite repair-gap — assembled finite keystone (Müller r1515, §§7–8)

Single-file assembly of the **finite, real, representation-theoretic** core of
B. Müller, *Explaining the Yang–Mills Mass Gap with Observer-Patch Repair
Dynamics* (r1515), §§7–8.  It bundles three drafted pieces into one coherent
artifact:

1. **Lemma 7.2** (`lemma_7_2`) — scalar relaxation on a uniform hidden fiber:
   a PSD Markov operator on `L²(F)` that commutes with the *full* symmetric
   group `S_F` and has kernel exactly the constants is a **positive scalar**
   multiple of `I − E_F`.  Proved concretely via the commutant of the
   permutation representation (two-valued form), no algebraically-closed-field
   Schur needed.
2. **Proposition 8.1** (`prop_8_1`) — commuting-color finite-stage gap:
   for a finite **commuting** family of star projections with joint projector
   `P₀`, `c_* · (I − P₀) ≤ ∑ c_* · (I − E_C)`.  Heart: `I − ∏ Eₐ ≤ ∑ (I − Eₐ)`.
3. **Theorem 7.3 / Lemma 7.4 assembly** (`thm_7_3_finite_gap`) — combine the
   per-collar positivity (Lemma 7.2), the commuting-color gap (Prop 8.1), and a
   uniform positive rate floor (Lemma 7.4) into `c_* · (I − P₀) ≤ L_r^rep` with
   `c_* > 0`: a strictly positive **finite-stage representation gap** `Δ_rep`.

## HONEST SCOPE — READ THIS FIRST (this is the FINITE gap, NOT the Clay problem)

Everything here is an **implication** `structure ⇒ finite gap`, nothing more.

* The premises are the paper's **physical modelling assumptions** and are
  discharged **NOWHERE**:
    - Lemma 7.2: `hComm` (full-`S_F` symmetry) and `hKer` (kernel = constants)
      are hypotheses about the relaxation operator's structure, not theorems.
    - Prop 8.1 / assembly: `hE` (each color a star projection), `hc` (colors
      pairwise commute), `hprod` (their non-commutative product = `P₀`), and the
      strictly-positive rates `hrate` are hypotheses about Yang–Mills' actual
      relaxation, not theorems.
* The deliverable is `Δ_rep`, the finite-stage **representation** gap.  It says
  **NOTHING** about `Δ_YM`, the physical Yang–Mills mass gap.
* The continuum certificate that would bridge `Δ_rep` to `Δ_YM` — Müller's
  **Assumption 9.2** (Schwinger-function convergence, reflection positivity,
  Osterwalder–Schrader reconstruction, non-triviality) — is the genuine open
  problem (constructive QFT).  It is **untouched, unassumed, unclaimed** here.
  The purely-logical reduction "Assumption 9.2 + finite gap ⇒ `Δ_YM ≥ c_* > 0`"
  is machine-checked *conditionally* in the sibling `RepairGapChain.lean`, where
  Assumption 9.2 is an explicit `Certificate` hypothesis — again NOT discharged.

The one physics-free residue this file actually proves is a clean
finite-dimensional operator fact: for any commuting family of orthogonal
projections, `I − ∏ Eₐ ≤ ∑ (I − Eₐ)`, together with the uniform-fiber scalar
form of Lemma 7.2.  **This is not, and does not claim to be, a proof of the
Yang–Mills mass gap.**

## Proof status (see the STATUS REPORT accompanying this file)

* Zero `sorry`, zero project-level `axiom`.  The two keystones (Lemma 7.2,
  Prop 8.1) carry their full proofs inline, so `thm_7_3_finite_gap` is
  discharged with no remaining obligations *modulo compilation*.
* **COMPILER-VERIFIED (2026-07-07):** elaborates green on Lean `v4.29.1` + Mathlib
  (built on the `rule30-lean` host).  `#print axioms` on `thm_7_3_finite_gap`,
  `lemma_7_2`, `prop_8_1`, `prop_8_1_gap` reports exactly `[propext,
  Classical.choice, Quot.sound]` — the three standard Mathlib axioms, **no
  `sorryAx`**.  Zero `sorry`, zero project-level `axiom`.
-/

open scoped Matrix RealInnerProductSpace
open Matrix

namespace ObserverPatchHolography.RepairGap

/-! ############################################################################
    # PART I — Lemma 7.2 (keystone): scalar relaxation on a uniform hidden fiber
    ############################################################################ -/

section Keystone

variable {F : Type*} [Fintype F] [DecidableEq F]

/-- `E_F` : orthogonal projection onto constants (the mean operator), as a matrix.
    Every entry is `1/|F|`. -/
noncomputable def EF (F : Type*) [Fintype F] : Matrix F F ℝ :=
  (Fintype.card F : ℝ)⁻¹ • Matrix.of (fun _ _ => (1 : ℝ))

@[simp] lemma EF_apply (i j : F) : EF F i j = (Fintype.card F : ℝ)⁻¹ := by
  simp [EF, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]

/-- **2-transitivity of the full symmetric group** (explicit witness).
    Given two distinct source points and two distinct target points, there is a permutation
    taking the first pair to the second.  Built as a two-swap composition, so no appeal to
    the packaged `isMultiplyPretransitive` machinery is needed. -/
theorem exists_perm_maps_two {i j i' j' : F} (hij : i ≠ j) (hij' : i' ≠ j') :
    ∃ σ : Equiv.Perm F, σ i = i' ∧ σ j = j' := by
  refine ⟨Equiv.swap (Equiv.swap i i' j) j' * Equiv.swap i i', ?_, ?_⟩
  · -- σ i = i'
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    -- goal: swap (swap i i' j) j' i' = i'
    refine Equiv.swap_apply_of_ne_of_ne ?_ hij'
    -- goal: i' ≠ swap i i' j
    intro h
    apply hij
    have h2 : Equiv.swap i i' i' = Equiv.swap i i' (Equiv.swap i i' j) :=
      congrArg (Equiv.swap i i') h
    rwa [Equiv.swap_apply_right, Equiv.swap_apply_self] at h2
  · -- σ j = j'
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]

/-- **Conjugation identity.**  A matrix commuting with every permutation matrix is invariant
    under simultaneous permutation of its row and column indices:
    `M (σ i) (σ j) = M i j`.  Proof: push the commutation `σP·M = M·σP` through `· *ᵥ eₖ`
    and read off columns. -/
theorem perm_conj_invariant (M : Matrix F F ℝ)
    (hM : ∀ σ : Equiv.Perm F, Commute (σ.permMatrix ℝ) M) :
    ∀ (σ : Equiv.Perm F) (i j : F), M (σ i) (σ j) = M i j := by
  intro σ i j
  -- `Commute a b` is definitionally `a * b = b * a`
  have hcomm : σ.permMatrix ℝ * M = M * σ.permMatrix ℝ := hM σ
  -- apply `· *ᵥ Pi.single (σ j) 1` to both sides
  have h : (σ.permMatrix ℝ * M) *ᵥ Pi.single (σ j) (1 : ℝ)
         = (M * σ.permMatrix ℝ) *ᵥ Pi.single (σ j) (1 : ℝ) := by rw [hcomm]
  rw [← mulVec_mulVec, ← mulVec_mulVec, permMatrix_mulVec, permMatrix_mulVec] at h
  -- h : (M *ᵥ e) ∘ σ = M *ᵥ (e ∘ σ)      where  e = Pi.single (σ j) 1
  -- simplify  e ∘ σ = Pi.single j 1   (σ injective)
  have hcomp : (Pi.single (σ j) (1 : ℝ)) ∘ σ = Pi.single j (1 : ℝ) := by
    funext l
    simp only [Function.comp_apply, Pi.single_apply, σ.injective.eq_iff]
  rw [hcomp, mulVec_single_one, mulVec_single_one] at h
  -- h : M.col (σ j) ∘ σ = M.col j
  have := congrFun h i
  simpa only [Function.comp_apply, Matrix.col_apply] using this

/-- **Commutant of the permutation representation, concretely.**
    A real matrix commuting with every permutation matrix is two-valued:
    a common diagonal value `a` and a common off-diagonal value `b`.
    (Diagonal-constant from transitivity; off-diagonal-constant from 2-transitivity,
    which needs `2 ≤ |F|`.) -/
theorem commutant_perm_two_valued
    (hF : 2 ≤ Fintype.card F) (M : Matrix F F ℝ)
    (hM : ∀ σ : Equiv.Perm F, Commute (σ.permMatrix ℝ) M) :
    ∃ a b : ℝ, ∀ i j, M i j = if i = j then a else b := by
  have hconj := perm_conj_invariant M hM
  obtain ⟨p, q, hpq⟩ := Fintype.one_lt_card_iff.mp (by omega : 1 < Fintype.card F)
  refine ⟨M p p, M p q, fun i j => ?_⟩
  by_cases h : i = j
  · subst h
    rw [if_pos rfl]
    have := hconj (Equiv.swap p i) p p
    rwa [Equiv.swap_apply_left] at this
  · rw [if_neg h]
    obtain ⟨σ, hσp, hσq⟩ := exists_perm_maps_two hpq h
    have := hconj σ p q
    rwa [hσp, hσq] at this

/-- **LEMMA 7.2 (keystone).**  Let `D` be positive semidefinite (this already bundles
    Hermitian), commuting with the full symmetric group's permutation action, with kernel
    exactly the constants.  Then `D = c_F · (I − E_F)` for some `c_F > 0`.

    Roles of the hypotheses (all genuinely used, none vacuous):
    * `hComm`  ⇒ `D` is two-valued: `D i j = if i=j then a else b`   (Schur / commutant step);
    * `hKer`   ⇒ constants ∈ ker gives `a + (|F|−1)·b = 0`, and ker = constants gives `b ≠ 0`;
    * `hPSD`   ⇒ the quadratic form on `e_p − e_q` equals `2(a−b) ≥ 0`, fixing the sign.
    Setting `c_F := a − b` yields `c_F > 0` and `D = c_F · (1 − E_F)` entrywise.

    HONEST: `hComm` and `hKer` are the paper's physical modelling assumptions, hypotheses
    here — this proves "uniform-fiber structure ⇒ scalar relaxation", nothing about `Δ_YM`. -/
theorem lemma_7_2
    (hF : 2 ≤ Fintype.card F) (D : Matrix F F ℝ)
    (hPSD  : D.PosSemidef)
    (hComm : ∀ σ : Equiv.Perm F, Commute (σ.permMatrix ℝ) D)
    (hKer  : ∀ v : F → ℝ, D.mulVec v = 0 ↔ ∃ c : ℝ, v = fun _ => c) :
    ∃ cF : ℝ, 0 < cF ∧ D = cF • (1 - EF F) := by
  -- Step 0: two distinct fiber points and the two-valued form of D.
  obtain ⟨p, q, hpq⟩ := Fintype.one_lt_card_iff.mp (by omega : 1 < Fintype.card F)
  obtain ⟨a, b, hab⟩ := commutant_perm_two_valued hF D hComm
  have hN0 : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  -- Step 1: constants in the kernel  ⇒  a + (N-1)·b = 0.
  have hconst_ker : D.mulVec (fun _ => (1 : ℝ)) = 0 := (hKer _).mpr ⟨1, rfl⟩
  have hrow : a + ((Fintype.card F : ℝ) - 1) * b = 0 := by
    have hp0 : ∑ j, D p j = 0 := by
      have h := congrFun hconst_ker p
      simpa [Matrix.mulVec, dotProduct, mul_one] using h
    have hsum : ∑ j, D p j = a + ((Fintype.card F : ℝ) - 1) * b := by
      have hshift : ∀ j, D p j = b + (if p = j then a - b else 0) := by
        intro j; rw [hab p j]; split_ifs <;> ring
      simp_rw [hshift]
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq]
      simp only [Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    rw [hsum] at hp0; linarith
  -- Step 2: positive-semidefiniteness on  e_p − e_q  gives  0 ≤ a − b.
  have hquad : (0 : ℝ) ≤ a - b := by
    have hpos := hPSD.dotProduct_mulVec_nonneg ((Pi.single p 1 : F → ℝ) - (Pi.single q 1 : F → ℝ))
    have hstar : star ((Pi.single p 1 : F → ℝ) - (Pi.single q 1 : F → ℝ))
               = (Pi.single p 1 : F → ℝ) - (Pi.single q 1 : F → ℝ) := by
      funext k; simp [Pi.star_apply, star_trivial]
    rw [hstar] at hpos
    have hval : ((Pi.single p 1 : F → ℝ) - (Pi.single q 1 : F → ℝ)) ⬝ᵥ
                (D *ᵥ ((Pi.single p 1 : F → ℝ) - (Pi.single q 1 : F → ℝ))) = 2 * (a - b) := by
      rw [mulVec_sub, mulVec_single_one, mulVec_single_one,
          sub_dotProduct, dotProduct_sub, dotProduct_sub,
          single_dotProduct, single_dotProduct, single_dotProduct, single_dotProduct]
      simp only [Matrix.col_apply, one_mul]
      rw [hab p p, hab p q, hab q p, hab q q,
          if_pos rfl, if_pos rfl, if_neg hpq, if_neg (Ne.symm hpq)]
      ring
    rw [hval] at hpos; linarith
  -- Step 3: ker = constants  ⇒  b ≠ 0  (else D = 0, contradicting kernel exactness).
  have hbne : b ≠ 0 := by
    intro hb0
    have ha0 : a = 0 := by rw [hb0] at hrow; simpa using hrow
    have hD0 : D.mulVec ((Pi.single p 1 : F → ℝ)) = 0 := by
      have hDeq : D = 0 := by ext i j; rw [hab i j, hb0, ha0]; simp
      rw [hDeq]; exact Matrix.zero_mulVec _
    obtain ⟨c, hc⟩ := (hKer ((Pi.single p 1 : F → ℝ))).mp hD0
    have h1 : ((Pi.single p 1 : F → ℝ)) p = c := by rw [hc]
    have h2 : ((Pi.single p 1 : F → ℝ)) q = c := by rw [hc]
    rw [Pi.single_eq_same] at h1
    rw [Pi.single_eq_of_ne (Ne.symm hpq)] at h2
    exact one_ne_zero (h1.trans h2.symm)
  -- Step 4: assemble.  cF := a − b > 0, and D = cF·(1 − E_F) entrywise.
  refine ⟨a - b, ?_, ?_⟩
  · -- 0 < a − b
    have hne : a - b ≠ 0 := by
      have hcf : a - b = (Fintype.card F : ℝ) * (-b) := by linear_combination hrow
      rw [hcf]; exact mul_ne_zero hN0 (neg_ne_zero.mpr hbne)
    exact lt_of_le_of_ne hquad (Ne.symm hne)
  · -- D = (a − b) • (1 − E_F)
    have ha_eq : a = (1 - (Fintype.card F : ℝ)) * b := by linear_combination hrow
    ext i j
    rw [hab i j]
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, EF_apply, smul_eq_mul]
    by_cases h : i = j
    · rw [if_pos h, if_pos h, ha_eq]; field_simp; ring
    · rw [if_neg h, if_neg h, ha_eq]; field_simp; ring

end Keystone

/-- The per-collar consequence of Lemma 7.2 that the assembly conceptually consumes:
    each active collar has a **strictly positive** relaxation rate. This genuinely invokes
    `lemma_7_2` (extracts its `0 < cF`), realising the "each `c_C > 0`" input.  (Note: the
    assembly `thm_7_3_finite_gap` takes positive rates as a hypothesis directly; this lemma
    is the justification for that hypothesis on the certified branch, not a wire into it.) -/
theorem collar_rate_pos {F : Type*} [Fintype F] [DecidableEq F]
    (hF : 2 ≤ Fintype.card F) (D : Matrix F F ℝ)
    (hPSD : D.PosSemidef)
    (hComm : ∀ σ : Equiv.Perm F, Commute (σ.permMatrix ℝ) D)
    (hKer : ∀ v : F → ℝ, D.mulVec v = 0 ↔ ∃ c : ℝ, v = fun _ => c) :
    ∃ cF : ℝ, 0 < cF :=
  let ⟨cF, hpos, _⟩ := lemma_7_2 hF D hPSD hComm hKer
  ⟨cF, hpos⟩

/-! ############################################################################
    # PART II — Proposition 8.1: commuting-color finite-stage gap
    #   (operators on a finite-dimensional real inner-product space)
    ############################################################################ -/

section GapEngine

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

/-! ## Loewner-order plumbing on `E →L[ℝ] E`
`E →L[ℝ] E` carries the Loewner partial order (`f ≤ g ↔ (g − f).IsPositive`). -/

/-- Left-add monotonicity for the Loewner order: `a ≤ b → c + a ≤ c + b`. -/
private lemma add_le_add_left_clm {a b : E →L[ℝ] E} (h : a ≤ b) (c : E →L[ℝ] E) :
    c + a ≤ c + b := by
  rw [ContinuousLinearMap.le_def] at h ⊢
  have e : (c + b) - (c + a) = b - a := by abel
  rwa [e]

/-- Nonnegative-scalar monotonicity for the Loewner order: `a ≤ b → 0 ≤ c → c • a ≤ c • b`. -/
private lemma smul_le_smul_clm {a b : E →L[ℝ] E} (h : a ≤ b) {c : ℝ} (hc : 0 ≤ c) :
    c • a ≤ c • b := by
  rw [ContinuousLinearMap.le_def] at h ⊢
  have e : c • b - c • a = c • (b - a) := by rw [smul_sub]
  rw [e]
  exact ContinuousLinearMap.IsPositive.smul_of_nonneg h hc

/-- **Two commuting projections.** For commuting orthogonal (star) projections
    `p, q`, `I − p·q ≤ (I − p) + (I − q)`.

    Proof: `((I−p)+(I−q)) − (I−p·q) = (I−p)·(I−q)`, and the product of the two
    commuting star projections `I−p`, `I−q` is again a star projection, hence positive. -/
theorem two_proj_le {p q : E →L[ℝ] E}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (h : Commute p q) :
    (1 - p * q) ≤ (1 - p) + (1 - q) := by
  rw [ContinuousLinearMap.le_def]
  have key : ((1 - p) + (1 - q)) - (1 - p * q) = (1 - p) * (1 - q) := by
    noncomm_ring
  rw [key]
  have hcomm : Commute (1 - p) (1 - q) :=
    (Commute.one_left (1 - q)).sub_left ((Commute.one_right p).sub_right h)
  exact ContinuousLinearMap.IsPositive.of_isStarProjection
    (hp.one_sub.mul hq.one_sub hcomm)

/-- The non-commutative product `∏_{a∈s} p a` of a **commuting** family of star
    projections is itself a star projection. Induction on `s` via `Finset.cons_induction`;
    each step is `IsStarProjection.mul`, with commutativity from `noncommProd_commute`. -/
theorem noncommProd_isStarProjection {ι : Type*} (p : ι → E →L[ℝ] E) :
    ∀ (s : Finset ι) (_hp : ∀ a ∈ s, IsStarProjection (p a))
      (hc : (↑s : Set ι).Pairwise (Function.onFun Commute p)),
      IsStarProjection (s.noncommProd p hc) := by
  intro s
  induction s using Finset.cons_induction with
  | empty =>
      intro _hp hc
      rw [Finset.noncommProd_empty]
      exact IsStarProjection.one _
  | cons a t hat ih =>
      intro hp hc
      have hcsub : (↑t : Set ι).Pairwise (Function.onFun Commute p) :=
        hc.mono fun _ => Finset.mem_cons.2 ∘ .inr
      have hpsub : ∀ x ∈ t, IsStarProjection (p x) :=
        fun x hx => hp x (Finset.mem_cons_of_mem hx)
      have hpa : IsStarProjection (p a) := hp a (Finset.mem_cons_self a t)
      have hcomm_aQ : Commute (p a) (t.noncommProd p hcsub) :=
        Finset.noncommProd_commute t p hcsub (p a)
          (fun x hx => hc (Finset.mem_cons_self a t) (Finset.mem_cons_of_mem hx)
            (by rintro rfl; exact hat hx))
      rw [Finset.noncommProd_cons]
      exact hpa.mul (ih hpsub hcsub) hcomm_aQ

/-- **Heart of Proposition 8.1.** For a finite **commuting** family of star projections `p`,
    `I − ∏_{a∈s} p a ≤ ∑_{a∈s} (I − p a)`.

    Induction on `s`: empty product is `I` (both sides `0`); the `cons a t` step factors
    `∏ = p a · ∏_t`, applies `two_proj_le` to the commuting pair `(p a, ∏_t)`, then the IH
    on the tail via left-add monotonicity. -/
theorem one_sub_noncommProd_le_sum {ι : Type*} (p : ι → E →L[ℝ] E) :
    ∀ (s : Finset ι) (hp : ∀ a ∈ s, IsStarProjection (p a))
      (hc : (↑s : Set ι).Pairwise (Function.onFun Commute p)),
      (1 - s.noncommProd p hc) ≤ ∑ a ∈ s, (1 - p a) := by
  intro s
  induction s using Finset.cons_induction with
  | empty =>
      intro _hp _hc
      simp only [Finset.noncommProd_empty, sub_self, Finset.sum_empty, le_refl]
  | cons a t hat ih =>
      intro hp hc
      have hcsub : (↑t : Set ι).Pairwise (Function.onFun Commute p) :=
        hc.mono fun _ => Finset.mem_cons.2 ∘ .inr
      have hpsub : ∀ x ∈ t, IsStarProjection (p x) :=
        fun x hx => hp x (Finset.mem_cons_of_mem hx)
      have hpa : IsStarProjection (p a) := hp a (Finset.mem_cons_self a t)
      have hQ : IsStarProjection (t.noncommProd p hcsub) :=
        noncommProd_isStarProjection p t hpsub hcsub
      have hcomm_aQ : Commute (p a) (t.noncommProd p hcsub) :=
        Finset.noncommProd_commute t p hcsub (p a)
          (fun x hx => hc (Finset.mem_cons_self a t) (Finset.mem_cons_of_mem hx)
            (by rintro rfl; exact hat hx))
      rw [Finset.noncommProd_cons, Finset.sum_cons]
      calc (1 : E →L[ℝ] E) - p a * t.noncommProd p hcsub
          ≤ (1 - p a) + (1 - t.noncommProd p hcsub) := two_proj_le hpa hQ hcomm_aQ
        _ ≤ (1 - p a) + ∑ x ∈ t, (1 - p x) :=
            add_le_add_left_clm (ih hpsub hcsub) (1 - p a)

/-- **The joint projector is a projection.** `P₀ = ∏ₐ Eₐ` is a star projection, so `I − P₀`
    is a genuine complementary orthogonal projection — this is what makes the
    "spectral gap on the orthogonal complement of the constants" reading honest. -/
theorem prod_isStarProjection {ι : Type*} (s : Finset ι) (Ec : ι → (E →L[ℝ] E))
    (P0 : E →L[ℝ] E) (hE : ∀ a ∈ s, IsStarProjection (Ec a))
    (hc : (↑s : Set ι).Pairwise (Function.onFun Commute Ec))
    (hprod : s.noncommProd Ec hc = P0) :
    IsStarProjection P0 := by
  rw [← hprod]
  exact noncommProd_isStarProjection Ec s hE hc

/-- **Proposition 8.1 (commuting-color finite-stage gap).** For a finite family of mutually
    commuting star projections `Ec` whose non-commutative product is the joint projector `P₀`,
    and any constant rate `c_* > 0`,  `c_* · (I − P₀) ≤ ∑ₐ c_* · (I − Eₐ)`.

    HONEST: `hE`, `hc`, `hprod` are physical modelling assumptions, hypotheses here. -/
theorem prop_8_1 {ι : Type*} (s : Finset ι) (Ec : ι → (E →L[ℝ] E)) (P0 : E →L[ℝ] E)
    (hE : ∀ a ∈ s, IsStarProjection (Ec a))
    (hc : (↑s : Set ι).Pairwise (Function.onFun Commute Ec))
    (hprod : s.noncommProd Ec hc = P0)
    {cstar : ℝ} (hcpos : 0 < cstar) :
    cstar • ((1 : E →L[ℝ] E) - P0) ≤ ∑ a ∈ s, cstar • ((1 : E →L[ℝ] E) - Ec a) := by
  rw [← hprod, ← Finset.smul_sum]
  exact smul_le_smul_clm (one_sub_noncommProd_le_sum Ec s hE hc) hcpos.le

/-- **Rayleigh form of Proposition 8.1 (the "gap ≥ c_*" as usually quoted).**
    On the orthogonal complement of the constants (`P₀ x = 0`), the constant-rate generator
    `L̃ = ∑ₐ c_* · (I − Eₐ)` satisfies `⟪L̃ x, x⟫ ≥ c_* · ‖x‖²`.  (Bonus corollary.) -/
theorem prop_8_1_gap {ι : Type*} (s : Finset ι) (Ec : ι → (E →L[ℝ] E)) (P0 : E →L[ℝ] E)
    (hE : ∀ a ∈ s, IsStarProjection (Ec a))
    (hc : (↑s : Set ι).Pairwise (Function.onFun Commute Ec))
    (hprod : s.noncommProd Ec hc = P0)
    {cstar : ℝ} (hcpos : 0 < cstar) (x : E) (hx : P0 x = 0) :
    cstar * ‖x‖ ^ 2 ≤ inner ℝ ((∑ a ∈ s, cstar • ((1 : E →L[ℝ] E) - Ec a)) x) x := by
  have hle : cstar • ((1 : E →L[ℝ] E) - P0) ≤ ∑ a ∈ s, cstar • ((1 : E →L[ℝ] E) - Ec a) :=
    prop_8_1 s Ec P0 hE hc hprod hcpos
  rw [ContinuousLinearMap.le_def] at hle
  have hnn := hle.inner_nonneg_left x
  have happ :
      ((∑ a ∈ s, cstar • ((1 : E →L[ℝ] E) - Ec a)) - cstar • ((1 : E →L[ℝ] E) - P0)) x
        = (∑ a ∈ s, cstar • ((1 : E →L[ℝ] E) - Ec a)) x - cstar • x := by
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, hx, sub_zero]
  rw [happ, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq] at hnn
  linarith

/-! ############################################################################
    # PART III — Theorem 7.3 / Lemma 7.4 assembly: the finite representation gap
    ############################################################################ -/

/-- **The repair generator** `L_r^rep = ∑_{C ∈ s} c_C · (I − E_C)` over a finite active-collar
    index set `s`, with per-collar orthogonal projections `Ec` and relaxation rates `rate`. -/
noncomputable def repairGenerator {ι : Type*} (s : Finset ι)
    (Ec : ι → (E →L[ℝ] E)) (rate : ι → ℝ) : E →L[ℝ] E :=
  ∑ a ∈ s, rate a • ((1 : E →L[ℝ] E) - Ec a)

/-- **Lemma 7.4 (uniform floor).** Finitely many strictly positive relaxation rates over a
    nonempty active-collar set have a strictly positive minimum `c_*` bounding them below. -/
theorem uniform_floor {ι : Type*} (s : Finset ι) (hne : s.Nonempty) (rate : ι → ℝ)
    (hpos : ∀ a ∈ s, 0 < rate a) :
    ∃ cstar : ℝ, 0 < cstar ∧ ∀ a ∈ s, cstar ≤ rate a := by
  obtain ⟨a₀, ha₀, hmin⟩ := s.exists_min_image rate hne
  exact ⟨rate a₀, hpos a₀ ha₀, hmin⟩

/-- **Theorem 7.3 / 7.4 (finite representation gap).** Combine Lemma 7.2 (each collar rate
    `rate a > 0`), Proposition 8.1 (commuting colors ⇒ constant-rate gap), and the uniform
    floor (Lemma 7.4): the repair generator dominates `c_* · (I − P₀)` with `c_* > 0`.

    This is `Δ_rep ≥ c_* > 0`, the finite-stage **representation** gap.  It says NOTHING
    about `Δ_YM`; the continuum bridge (Assumption 9.2) is not stated, not assumed, not proved
    here (see `RepairGapChain.lean` for the conditional reduction).

    Proof shape: `c_* · (I − P₀) ≤ ∑ c_* · (I − E_C) ≤ ∑ c_C · (I − E_C)`, where the first `≤`
    is Prop 8.1 and the second is rate-monotonicity (each summand grows because `c_C ≥ c_*`
    and `I − E_C ⪰ 0`). -/
theorem thm_7_3_finite_gap {ι : Type*} (s : Finset ι) (hne : s.Nonempty)
    (Ec : ι → (E →L[ℝ] E)) (P0 : E →L[ℝ] E)
    (hE : ∀ a ∈ s, IsStarProjection (Ec a))
    (hc : (↑s : Set ι).Pairwise (Function.onFun Commute Ec))
    (hprod : s.noncommProd Ec hc = P0)
    (rate : ι → ℝ) (hrate : ∀ a ∈ s, 0 < rate a) :
    ∃ cstar : ℝ, 0 < cstar ∧
      cstar • ((1 : E →L[ℝ] E) - P0) ≤ repairGenerator s Ec rate := by
  -- Lemma 7.4: a strictly positive uniform floor c_* = min_C c_C.
  obtain ⟨cstar, hcstar_pos, hfloor⟩ := uniform_floor s hne rate hrate
  refine ⟨cstar, hcstar_pos, ?_⟩
  -- Step 1 (Prop 8.1): the constant-rate gap  c_* (I − P₀) ≤ ∑ c_* (I − E_C).
  have step1 :
      cstar • ((1 : E →L[ℝ] E) - P0) ≤ ∑ a ∈ s, cstar • ((1 : E →L[ℝ] E) - Ec a) :=
    prop_8_1 s Ec P0 hE hc hprod hcstar_pos
  -- Step 2: actual rates dominate the floor rate collar-by-collar.
  have step2 :
      (∑ a ∈ s, cstar • ((1 : E →L[ℝ] E) - Ec a))
        ≤ ∑ a ∈ s, rate a • ((1 : E →L[ℝ] E) - Ec a) := by
    have hdiff :
        (∑ a ∈ s, (rate a - cstar) • ((1 : E →L[ℝ] E) - Ec a))
          = (∑ a ∈ s, rate a • ((1 : E →L[ℝ] E) - Ec a))
              - ∑ a ∈ s, cstar • ((1 : E →L[ℝ] E) - Ec a) := by
      simp only [sub_smul, Finset.sum_sub_distrib]
    refine (ContinuousLinearMap.le_def _ _).mpr ?_
    rw [← hdiff]
    refine ContinuousLinearMap.isPositive_sum s (fun a ha => ?_)
    exact ContinuousLinearMap.IsPositive.smul_of_nonneg
      (ContinuousLinearMap.IsPositive.of_isStarProjection (hE a ha).one_sub)
      (sub_nonneg.mpr (hfloor a ha))
  -- Assemble: c_* (I − P₀) ≤ ∑ c_* (I − E_C) ≤ ∑ c_C (I − E_C) = L_r^rep.
  show cstar • ((1 : E →L[ℝ] E) - P0) ≤ ∑ a ∈ s, rate a • ((1 : E →L[ℝ] E) - Ec a)
  exact le_trans step1 step2

end GapEngine



end ObserverPatchHolography.RepairGap
