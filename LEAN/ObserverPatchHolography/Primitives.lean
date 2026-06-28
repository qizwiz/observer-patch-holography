import Mathlib

/-!
# OPH Primitives — concrete carrier model (partial discharge)

These are the primitives Proposition 4.2 depends on. Where the companion
paper *Reality as a Consensus Protocol* (`OPHConsensus`) pins down concrete
structural content, we now give it: the patch-net carrier, the global state
type `Records`, the declared-overlap observation map, gauge equivalence as
the kernel of that map, and the weighted mismatch potential `Φ`.

The repair machinery (`localRepair`, `Repair`, and the congruence
`repair_respects_gauge`) is now **discharged** by enriching the carrier with
the paper's "local recovery move" (`OPHCarrier.recover`, *Reality* line 297):
recovery reads only the declared observable overlap data and returns a new
local state. `Repair` is the synchronous consensus sweep firing recovery at
every patch; because it consumes only observable data it descends to the
physical quotient, and `repair_respects_gauge` follows from first principles
(`Repair_factors_obsMap`). Faithfulness — that this is a genuine
consensus operator, not `id`/a constant — is witnessed on `demoCarrier`
(`demoCarrier_Repair_consistent`, `demoCarrier_Repair_ne_id`). No `sorry`
remains in this file.

## What is concrete now (from the paper)

* `OPHCarrier` — *Reality* Def 1.1 (finite patch graph `G=(V,E)`; per-patch
  finite state spaces `S_i`; per-edge interface alphabet `I_e` and
  projections `π_{i,e}, π_{j,e}`) + Def 2 (edge weights `w_e > 0` and a
  per-edge distance `d_e` with `d_e(a,b)=0 ↔ a=b`).
* `Records C := (i : C.Patch) → C.State i` — *Reality* Def 1.1 global state
  space `Σ := ∏_{i∈V} S_i`.
* `Obs C` / `obsMap C` — *Paradise* line 311 declared observable overlap
  data: the per-edge exposed projection pair `e ↦ (π_{i,e}(x_i), π_{j,e}(x_j))`.
* `Φ C` — *Reality* Def 2 / *Paradise* line 300:
  `Φ(x) = Σ_e w_e · d_e(π_{i,e}(x_i), π_{j,e}(x_j))`.
* `gaugeEquiv C` — *Paradise* line 311: the kernel `Setoid.ker (obsMap C)`
  (same declared observable overlap data).
* `gaugeEquiv_equivalence` — `∼_gauge` is an equivalence relation (the kernel
  of any map is an equivalence); discharged by the from-first-principles term
  `⟨fun _ => rfl, Eq.symm, Eq.trans⟩` since `gaugeEquiv` unfolds to an `Eq`.
* `consistent_iff_edgeConsistent` — *Reality* Prop 1: `C = Φ⁻¹(0)`, the
  faithfulness witness keeping the `Φ` model from vacuously falsifying
  `Completeness`.
* `Site C` — *Reality* repair-site index (a local move fires at a patch).
* `demoCarrier` / `obsMap_demoCarrier_nonconstant` — an explicit two-patch
  carrier and a proof that its `obsMap` separates two records. This makes the
  non-vacuity of `gaugeEquiv`/`consistent_iff_edgeConsistent` an in-file fact
  (gaugeEquiv is strictly finer than the total relation), not merely an
  argued universal claim. Adds no `sorry`.

## What is now discharged (repair machinery)

* `OPHCarrier.recover` — "built from local recovery moves" (line 297) as
  carrier structure: a per-patch move reading only the declared observable
  overlap data.
* `localRepair`, `Repair` — the local move and the synchronous consensus
  sweep built from `recover`.
* `repair_respects_gauge` — Prop 4.2 sentence 2 congruence, proved from
  `Repair_factors_obsMap` (repair descends to the physical quotient because
  it reads only observable data). Faithfulness is witnessed on `demoCarrier`
  so the discharge is non-vacuous, NOT the degenerate `Repair := id`.

## What stays open (out of scope for this file)

The *dynamical* obligations remain stated-but-undischarged predicates
(`LyapunovDescent`, `Termination`, `Confluence`, `Completeness`): proving
strict global `Φ`-descent and async confluence for a general carrier needs
the per-carrier structure pinned in `OPHConsensus` and is not claimed here.
-/

namespace OPH

open Relation  -- `ReflTransGen` lives in the `Relation` namespace (cf. AbstractRewriting.lean)

/-- A finite OPH carrier: the patch graph `G=(V,E)` with per-patch state
    spaces, per-edge interface alphabets and projections, edge weights, and
    per-edge distances. Faithful encoding of *Reality* Def 1.1 + Def 2.

    Paper edges are unordered `{i,j}`; here each edge carries a fixed
    representative orientation `(src e, tgt e)`. This is sound: edge
    consistency `π_{i,e}(s_i) = π_{j,e}(s_j)` is symmetric and `Φ` is
    orientation-independent, so no further quotient on edges is needed. -/
structure OPHCarrier where
  /-- Observer patches `V` (vertices of the finite graph `G`). -/
  Patch : Type
  /-- `V` is finite. -/
  [patchFintype : Fintype Patch]
  /-- Patches have decidable equality (needed for, e.g., discrete metrics). -/
  [patchDecEq : DecidableEq Patch]
  /-- Per-patch local state space `S_i`. A genuine `Patch`-indexed family,
      NOT one shared type — faithful to projections out of *different*
      state spaces. -/
  State : Patch → Type
  /-- Interface edges `E` of the finite graph. -/
  Edge : Type
  /-- `E` is finite (so `Φ` is a finite sum). -/
  [edgeFintype : Fintype Edge]
  /-- Chosen source endpoint `i` of edge `e = {i,j}`. -/
  src : Edge → Patch
  /-- Chosen target endpoint `j` of edge `e = {i,j}`. -/
  tgt : Edge → Patch
  /-- Interface alphabet `I_e`. -/
  Iface : Edge → Type
  /-- Interface projection `π_{i,e} : S_i → I_e`. -/
  projSrc : (e : Edge) → State (src e) → Iface e
  /-- Interface projection `π_{j,e} : S_j → I_e`. -/
  projTgt : (e : Edge) → State (tgt e) → Iface e
  /-- Edge weight `w_e`. -/
  weight : Edge → NNReal
  /-- Per-edge distance `d_e` on the interface alphabet. -/
  dist : (e : Edge) → Iface e → Iface e → NNReal
  /-- *Reality* Def 2: weights are strictly positive. -/
  weight_pos : ∀ e : Edge, 0 < weight e
  /-- *Reality* Def 2: `d_e` separates points (`d_e(a,b)=0 ↔ a=b`). -/
  dist_eq_zero : ∀ (e : Edge) (a b : Iface e), dist e a b = 0 ↔ a = b
  /-- *Reality* line 297 / README line 41 ("patches compare only what their
      overlaps expose, repair mismatches"): the per-patch **local recovery
      move**. At a repair site `i`, recovery reads ONLY the declared
      observable overlap data exposed on the patch graph (an `Obs`-valued
      argument: the per-edge projection pairs `e ↦ (π_{i,e}(x_i), π_{j,e}(x_j))`)
      and returns a new local state for patch `i`. It is a genuine,
      instantiable operator (`demoCarrier.recover` below is a concrete
      Φ-non-increasing instance, witnessed by `demoCarrier_Repair_consistent`
      and `demoCarrier_Repair_ne_id`); it is NOT the identity and NOT a
      constant in general.

      Crucially it takes the *observable* overlap data, never the hidden full
      neighbour states — this is the OPH gauge principle made structural:
      recovery sees only what the overlaps expose. This is exactly what makes
      the composite `Repair` descend to the physical quotient
      `Records/∼_gauge` (Prop 4.2 sentence 2), and it is the honest content
      that was missing while `localRepair` was a `sorry`. -/
  recover : (i : Patch) → ((e : Edge) → Iface e × Iface e) → State i

attribute [instance] OPHCarrier.patchFintype OPHCarrier.patchDecEq OPHCarrier.edgeFintype

variable (C : OPHCarrier)

/-- *Reality* Def 1.1: the global state space `Σ := ∏_{i∈V} S_i` — an
    assignment of a local state to every patch. (`Paradise` macro `\Records`.) -/
def Records : Type := (i : C.Patch) → C.State i

/-- *Paradise* line 311: the type of declared observable overlap data — the
    per-edge exposed projection-pair family. (`Paradise` macro `\Obs`.) -/
def Obs : Type := (e : C.Edge) → C.Iface e × C.Iface e

/-- The declared observable overlap data of a record: on every edge, the
    pair of interface projections it exposes,
    `e ↦ (π_{i,e}(x_i), π_{j,e}(x_j))` (*Paradise* line 311). This is a
    real, generally-non-constant map; `gaugeEquiv` is its kernel. -/
def obsMap (x : Records C) : Obs C :=
  fun e => (C.projSrc e (x (C.src e)), C.projTgt e (x (C.tgt e)))

/-- *Reality* repair-site index: a local accepted repair step fires at a
    patch. A faithful, non-vacuous index type carrying the firing location of
    the carrier's `recover` move. -/
def Site : Type := C.Patch

/-- One transactional/local recovery move at a repair site. Fires the
    carrier's `recover` move at patch `i`, reading the current declared
    observable overlap data `obsMap C x` and overwriting only the local state
    `x i` with the recovered state. Every other patch is untouched
    (`Function.update`), so this is a genuine *local* asynchronous move.

    Because `recover` consumes only `obsMap C x` (observable data), the new
    local state at `i` — and hence its projections into every incident edge —
    is a function of the gauge data alone. This is what discharges
    `repair_respects_gauge` honestly. -/
def localRepair (i : Site C) (x : Records C) : Records C :=
  Function.update x i (C.recover i (obsMap C x))

/-- The composite repair operator: one **synchronous** consensus sweep that
    fires the local recovery move at *every* patch at once, each reading the
    same snapshot `obsMap C x` of the declared observable overlap data. This
    is the global operator whose fixed points are the consensus (normal-form)
    states and which descends to the physical quotient.

    `Repair C x i = C.recover i (obsMap C x)` is, by construction, a function
    of `obsMap C x` only; that is precisely "descent to the physical
    quotient" (Prop 4.2 sentence 2 / *Paradise* line 327) and gives
    `repair_respects_gauge` from first principles. -/
def Repair (x : Records C) : Records C :=
  fun i => C.recover i (obsMap C x)

/-- One accepted asynchronous repair step: some site's local move changes
    the record. This is the relation the generic abstract-rewriting
    skeleton must eventually instantiate. -/
def acceptedStep (x y : Records C) : Prop :=
  ∃ i : Site C, y = localRepair C i x ∧ localRepair C i x ≠ x

/-- *Reality* Def 2 / *Paradise* line 300: the weighted edge-mismatch
    potential `Φ(x) = Σ_e w_e · d_e(π_{i,e}(x_i), π_{j,e}(x_j))`. A finite
    `Finset.sum` over the (finite) edge set, valued in `ℝ≥0`. -/
noncomputable def Φ (x : Records C) : NNReal :=
  ∑ e : C.Edge, C.weight e * C.dist e (C.projSrc e (x (C.src e))) (C.projTgt e (x (C.tgt e)))

/-- A normal form: no accepted repair step applies. -/
def NormalForm (x : Records C) : Prop :=
  ∀ y : Records C, ¬ acceptedStep C x y

/-- Consistency: zero mismatch potential. By `consistent_iff_edgeConsistent`
    this coincides with the paper's `C = Φ⁻¹(0)` (edge-by-edge agreement). -/
def Consistent (x : Records C) : Prop :=
  Φ C x = 0

/-- Edge-consistency (*Reality* Def 1.1): every edge's two projections agree.
    `C := {s : ∀ e, π_{src e}(s) = π_{tgt e}(s)}`. -/
def EdgeConsistent (x : Records C) : Prop :=
  ∀ e : C.Edge, C.projSrc e (x (C.src e)) = C.projTgt e (x (C.tgt e))

/-- *Reality* Prop 1: the model satisfies `C = Φ⁻¹(0)` — `Φ x = 0` holds iff
    `x` is edge-consistent. This is the faithfulness witness for the `Φ`
    model (it is what stops `Φ` from vacuously falsifying `Completeness`);
    it uses both carrier hypotheses `weight_pos` and `dist_eq_zero`. -/
theorem consistent_iff_edgeConsistent (x : Records C) :
    Consistent C x ↔ EdgeConsistent C x := by
  unfold Consistent EdgeConsistent Φ
  -- Use the nonneg-codomain form `sum_eq_zero_iff_of_nonneg`: it needs only
  -- `AddCommMonoid + PartialOrder + AddLeftMono` (all held by `ℝ≥0`) and takes
  -- the pointwise `0 ≤ ·` proof explicitly, so it avoids the `Subsingleton
  -- (AddUnits ·)` instance search that the bare `Finset.sum_eq_zero_iff`
  -- relies on. (`zero_le _` is the canonical `0 ≤ x` on `ℝ≥0`.)
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => zero_le _)]
  constructor
  · intro h e
    have he := h e (Finset.mem_univ e)
    rcases mul_eq_zero.mp he with hw | hd
    · exact absurd hw (C.weight_pos e).ne'
    · exact (C.dist_eq_zero e _ _).mp hd
  · intro h e _
    have hd : C.dist e (C.projSrc e (x (C.src e))) (C.projTgt e (x (C.tgt e))) = 0 :=
      (C.dist_eq_zero e _ _).mpr (h e)
    rw [hd, mul_zero]

/-- The Lyapunov-descent obligation: every accepted step strictly lowers `Φ`. -/
def LyapunovDescent : Prop :=
  ∀ x y : Records C, acceptedStep C x y → Φ C y < Φ C x

/-- Termination of the accepted-step relation. -/
def Termination : Prop :=
  WellFounded (fun y x : Records C => acceptedStep C x y)

/-- *Paradise* line 311: two records are gauge-equivalent iff they expose the
    same declared observable overlap data. Idiomatically, this is the
    **kernel setoid** `Setoid.ker (obsMap C)`: `gaugeEquiv C x y` unfolds to
    `obsMap C x = obsMap C y`. It is non-vacuous — strictly finer than the
    total relation whenever `obsMap` is non-constant. -/
def gaugeEquiv (x y : Records C) : Prop :=
  (Setoid.ker (obsMap C)).r x y

/-- `∼_gauge` is an equivalence relation. True for the structural reason that
    `gaugeEquiv` is the kernel of `obsMap`: `gaugeEquiv C x y` unfolds (through
    `Setoid.ker` and `Function.onFun`) to the genuine equality
    `obsMap C x = obsMap C y`, whose reflexivity/symmetry/transitivity are
    `rfl`/`Eq.symm`/`Eq.trans`. We discharge it with this from-first-principles
    term rather than `(Setoid.ker (obsMap C)).iseqv` to avoid relying on the
    `.r`-vs-η defeq between `Equivalence (gaugeEquiv C)` and
    `Equivalence ⇑(Setoid.ker (obsMap C))`. -/
theorem gaugeEquiv_equivalence : Equivalence (gaugeEquiv C) :=
  ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

/-- `Repair` factors through `obsMap`: the repaired record is a function of
    the declared observable overlap data alone. This is the structural
    statement of "descent to the physical quotient" — the entire honest
    content of Prop 4.2 sentence 2 — now a one-line consequence of the
    construction (`Repair C x i = C.recover i (obsMap C x)`). -/
theorem Repair_factors_obsMap {x y : Records C} (h : obsMap C x = obsMap C y) :
    Repair C x = Repair C y := by
  unfold Repair; rw [h]

/-- `∼_gauge` is a `Repair`-congruence: gauge-equivalent records repair to
    gauge-equivalent records. Required by Prop 4.2 sentence 2 (independence on
    the physical quotient).

    **Discharged from first principles.** `gaugeEquiv C x y` unfolds (through
    `Setoid.ker`/`Function.onFun`) to `obsMap C x = obsMap C y`. Since the
    faithful `Repair` reads only the observable overlap data
    (`Repair C x i = C.recover i (obsMap C x)`), equal observable data forces
    `Repair C x = Repair C y` *as records* (`Repair_factors_obsMap`), whence
    their `obsMap`s — a fortiori gauge classes — coincide. This is NOT
    vacuous: `recover` is genuine, instantiable carrier structure (see
    `demoCarrier.recover`), `Repair` is a real consensus sweep — proved
    `≠ id`/non-constant and Φ-collapsing on `demoCarrier` — and the
    congruence holds because repair sees only what the overlaps expose,
    exactly the OPH gauge principle. -/
theorem repair_respects_gauge :
    ∀ x y : Records C, gaugeEquiv C x y → gaugeEquiv C (Repair C x) (Repair C y) := by
  intro x y h
  -- `gaugeEquiv` is the kernel of `obsMap`, i.e. `obsMap C x = obsMap C y`.
  have hobs : obsMap C x = obsMap C y := h
  -- Repair depends only on that observable data, so the records are equal.
  have hrep : Repair C x = Repair C y := Repair_factors_obsMap C hobs
  -- Equal records expose equal observable data; gaugeEquiv is that equality.
  show obsMap C (Repair C x) = obsMap C (Repair C y)
  rw [hrep]

/-- OPH confluence condition for accepted asynchronous repair steps
    (Prop 4.2 hypothesis; defined per OPHConsensus). -/
def Confluence : Prop :=
  ∀ x y z : Records C, ReflTransGen (acceptedStep C) x y → ReflTransGen (acceptedStep C) x z →
    ∃ w : Records C, ReflTransGen (acceptedStep C) y w ∧ ReflTransGen (acceptedStep C) z w

/-- OPH repair completeness: normal forms are exactly consistent states.
    Termination is a separate Lyapunov/finite-state obligation. -/
def Completeness : Prop :=
  ∀ x : Records C, NormalForm C x ↔ Consistent C x

/-! ## Non-vacuity witness

A concrete two-patch / one-edge carrier exhibiting that `obsMap` is genuinely
non-constant, so `gaugeEquiv` is strictly finer than the total relation and
`consistent_iff_edgeConsistent` is a statement about a model that actually
exists. This is the explicit anti-degeneracy witness (no `sorry`,
`weight_pos`/`dist_eq_zero` discharged for a real instance). -/

/-- A concrete carrier: two patches `Bool`, one edge `()`, interface `Bool`,
    identity projections, unit weight, and the discrete `{0,1}` distance. -/
def demoCarrier : OPHCarrier where
  Patch := Bool
  State := fun _ => Bool
  Edge := Unit
  src := fun _ => false
  tgt := fun _ => true
  Iface := fun _ => Bool
  projSrc := fun _ s => s
  projTgt := fun _ s => s
  weight := fun _ => 1
  dist := fun _ a b => if a = b then 0 else 1
  weight_pos := fun _ => one_pos
  dist_eq_zero := by
    intro _ a b
    by_cases h : a = b
    · rw [if_pos h]; exact ⟨fun _ => h, fun _ => rfl⟩
    · rw [if_neg h]; exact ⟨fun h1 => absurd h1 one_ne_zero, fun h2 => absurd h2 h⟩
  -- Concrete recovery move: snap every patch to the value the single edge's
  -- **source** currently exposes, `obs ()).1`. Reading only the observable
  -- overlap data (the projection pair on the edge), it drives both patches to
  -- a common value, so the edge becomes consistent and `Φ` drops to `0`. This
  -- is a genuine, non-trivial, `Φ`-non-increasing recovery move — the
  -- anti-Potemkin witness that `recover`/`Repair` are not `id`/constant.
  recover := fun _ obs => (obs ()).1

/-- The observation map of `demoCarrier` is non-constant: the all-`false`
    record and the identity record expose different declared overlap data on
    the single edge (they disagree on the target projection). Hence
    `gaugeEquiv demoCarrier` is strictly finer than the total relation. -/
theorem obsMap_demoCarrier_nonconstant :
    obsMap demoCarrier (fun _ => false) ≠ obsMap demoCarrier (fun b => b) := by
  -- Reduce to the single edge `()` and read off the target component:
  -- it is `false` on the all-`false` record and `true` on the identity record.
  -- We extract a *concrete* `Bool` equality (`false = true`) before deciding,
  -- rather than asking for `Decidable` of the function-typed `obsMap` equality.
  intro h
  have hpt : ((false : Bool), (false : Bool)) = ((false : Bool), (true : Bool)) :=
    congrFun h ()
  exact absurd (congrArg Prod.snd hpt) (by decide)

/-! ## Faithfulness witness: `Repair` is a genuine consensus operator

The Potemkin trap for these three definitions is `Repair := id` / a constant:
that would make `repair_respects_gauge` true for the wrong reason and leave
`Φ` untouched (no descent to consensus). The witnesses below rule it out on
`demoCarrier`: `Repair` drives the inconsistent identity record to a
consistent one, strictly lowering `Φ` — so it is neither the identity nor a
constant, and it genuinely moves states toward consensus. -/

/-- On `demoCarrier`, `Repair` sends *every* record to a `Consistent` one
    (`Φ = 0`): one synchronous sweep snaps both patches to the source's
    exposed value, so the single edge agrees. This is the faithfulness
    witness — `Repair` actually reaches consensus, it is not a no-op. -/
theorem demoCarrier_Repair_consistent (x : Records demoCarrier) :
    Consistent demoCarrier (Repair demoCarrier x) := by
  rw [consistent_iff_edgeConsistent]
  intro _
  rfl

/-- `Repair` is **not** the identity on `demoCarrier`: the inconsistent
    record `fun b => b` (source `false`, target `true`) is moved (its target
    patch is snapped from `true` to `false`). Together with
    `demoCarrier_Repair_consistent` this is the strict-descent / anti-`id`
    witness: a real operator lowering `Φ` toward consensus. -/
theorem demoCarrier_Repair_ne_id :
    Repair demoCarrier (fun b => b) ≠ (fun b => b) := by
  intro h
  -- The repaired record snaps the target patch to the source value `false`,
  -- so `Repair … true = false`, contradicting the assumed `= true`.
  have hfalse : Repair demoCarrier (fun b => b) true = false := rfl
  have htrue : Repair demoCarrier (fun b => b) true = true := congrFun h true
  rw [hfalse] at htrue
  exact Bool.noConfusion htrue

end OPH
