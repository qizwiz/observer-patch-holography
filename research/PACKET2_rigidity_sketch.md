# Packet 2 — Rigidity metatheorem: "No holography without frustration"

Status: SKETCH (scope + Lean signature + adversarial pass). Not a proof.
Grounded in `LEAN/ObserverPatchHolography/Rule90.lean` (merged, PR #385).

## 0. What packet 1 actually proved (the seed)

`rule90_no_frustrationFree_repair`: no single-site local move `lr` satisfies all of
H1 (locality), H2 (fires iff an incident edge is broken), H3 (fixes incident edges).

The engine of that proof is ONE fact — a **conservation law**:

    rule90t_outer_eq : (rule90t s).1 = (rule90t s).2.2      -- outer cells always coincide

The record with bottom row `(0,0,1)` violates it → out-of-image for *every* seed →
edge broken → H2 fires the move → H1 pins the row → H3 demands a preimage of `(0,0,1)`
→ conservation law forbids it → ⊥.

The metatheorem's bet: **the `(0,0,1)`-specific argument is incidental; the conservation
law is the whole reason.** Abstract the law, keep the argument.

## 1. Scope (the abstract hypotheses)

Over an abstract `OPHCarrier C` with a step/observation map, assume:

- **(Conserve)** a decidable invariant `φ : Row → Prop` (or `Row → Q`) that is
  *constant on the image* of the step map (`∀ s, φ (step s)`) but *not constant
  overall* (`∃ r, ¬ φ r`).  ← Rule90: φ r := (r.1 = r.2.2); `rule90t_outer_eq` is `∀ s, φ (step s)`.
- **(Witness)** a record `x★` whose boundary row `r★` satisfies `¬ φ r★`
  (so `r★` is out-of-image), and whose broken edge is incident to a single patch.
- **(Holography)** the fiber/observation structure is nontrivial in the sense
  `rule90_Hfib_good` + `rule90_gauge_nontrivial` capture: the boundary determines
  the interior on the good fiber, and the gauge (kernel of the step map's outer
  reading) is nontrivial.

**Claim.** (Conserve) ∧ (Witness) ⟹ ¬∃ single-site frustration-free H1–H3 repair.

## 2. The "no holography WITHOUT frustration" title — the honest reading

The *provable* direction is: (Conserve)+(Witness) ⟹ frustration (no free local repair).
The *title's* direction is the contrapositive dressed up: a free local H1–H3 repair
⟹ ¬(Conserve) [no nontrivial conserved quantity] ⟹ the fiber is trivial ⟹ not
holographic. So "holography (nontrivial fiber, boundary-determines-interior) forces
frustration of local repair." The load-bearing link is (Holography) ⇔ (Conserve),
which is NOT yet proved — see §4, objection 2. That link is the real theorem.

## 3. Scope boundary (honoring Bernhard's merged review)

CLOSES: the single-site H1–H3 local-repair route, on any carrier meeting §1.
Does NOT close: transactional / multi-patch repair, a different repair-site carrier,
a relaxed H2. Same scope as packet 1 — the abstraction must not widen the claim.

## 4. Lean signature sketch (does NOT compile — GAPs marked)

```lean
/-- The obstruction data: a conserved quantity plus a witness that violates it. -/
structure ConservationObstruction (C : OPHCarrier) where
  φ            : Records C → Prop
  bridge       : ∀ (e : C.Edge) (x), edgeConsistentAt e x → φ x   -- consistency ⟹ invariant
  witness      : Records C
  witnessPatch : C.Patch
  witnessEdge  : C.Edge
  incident     : C.src witnessEdge = witnessPatch ∨ C.tgt witnessEdge = witnessPatch
  violates     : ¬ φ witness                                       -- witness is out-of-image
  pinned       : ∀ y, y witnessEdgeRow = witness witnessEdgeRow → ¬ φ y  -- GAP: row-pin ⟹ still violates

theorem no_holography_without_frustration
    (C : OPHCarrier) (O : ConservationObstruction C) :
    ¬ ∃ lr : C.Patch → Records C → Records C,
      (∀ i x j, j ≠ i → (lr i x) j = x j) ∧                                    -- H1
      (∀ i x, lr i x ≠ x ↔ ∃ e, (C.src e = i ∨ C.tgt e = i) ∧ ¬ edgeConsistentAt e x) ∧  -- H2
      (∀ i x, lr i x ≠ x → ∀ e, (C.src e = i ∨ C.tgt e = i) → edgeConsistentAt e (lr i x)) := by  -- H3
  rintro ⟨lr, H1, H2, H3⟩
  -- broken edge at the witness: ¬ edgeConsistentAt, from `violates` + `bridge` contrapositive
  have hbroken : ¬ edgeConsistentAt O.witnessEdge O.witness :=
    fun h => O.violates (O.bridge _ _ h)
  -- H2(⇐): broken incident edge forces the move to fire at witnessPatch
  have hfire := (H2 O.witnessPatch O.witness).mpr ⟨O.witnessEdge, O.incident, hbroken⟩
  -- H3: after firing, that edge is consistent → by bridge, φ holds of the repaired record
  have hcons := H3 O.witnessPatch O.witness hfire O.witnessEdge O.incident
  have hphi  : O.φ (lr O.witnessPatch O.witness) := O.bridge _ _ hcons
  -- H1: the repair left the witness edge's row untouched → still violates φ  -- GAP
  have hpin  := O.pinned (lr O.witnessPatch O.witness) (by
    -- GAP: derive row-equality from H1 locality (needs edge-row = single patch)
    sorry)
  exact hpin hphi
```

GAPs: (a) `pinned` — encoding "H1 leaves the boundary row fixed ⟹ φ still fails" needs
the carrier to expose which patch carries the witness edge's row (Rule90: the `true`
patch); (b) `bridge` must be a genuine hypothesis, true for Rule90 via `rule90t_outer_eq`,
and it is exactly the (Conserve) law in record form.

## 5. Adversarial pass (attacking §1–§4 in JH's own voice)

1. **VACUITY — is this just Rule90 relabelled?**  severity: minor / survivable.
   A *second* instance exists: any XOR/parity carrier whose step map lands only in the
   "checksum = 0" subspace — φ := "row satisfies the checksum", constant on the image,
   violated by an off-checksum boundary. Linear CAs with a non-surjective step map are a
   whole family. Not vacuous — but the honest name of the class is "**linear carriers with
   a conserved quantity**," and "holography" is doing rhetorical lifting.

2. **The title is unearned — Holography ⇔ Conserve is ASSUMED.**  severity: SERIOUS / fixable.
   What's *provable* uses only (Conserve)+(Witness). "No holography without frustration"
   needs nontrivial-fiber (Hfib) ⟺ nontrivial-conserved-quantity. For **finite/linear**
   carriers that IFF is rank–nullity: non-injective interior ⟺ non-surjective boundary ⟺
   a conserved quantity exists. So the slogan holds *for linear carriers* — state it that
   way; do NOT ship it as a universal metatheorem. This is the real theorem to prove.

3. **Rule90 facts smuggled in.**  severity: minor / fixable.
   Single edge, boolean rows, step-map-is-a-function. The abstraction survives if `bridge`
   + `pinned` are taken as carrier hypotheses (they hold for Rule90), but a carrier with
   many incident edges needs "the *witness* edge is the pinned one" — pushed into the
   structure. Honest, but it means the metatheorem is "carriers admitting this obstruction
   structure," which is close to assuming the conclusion's premise. Watch for near-tautology.

4. **Scope creep vs Bernhard.**  severity: none — PASSES.
   H1–H3 bound verbatim; conclusion is ¬∃ *single-site* lr. Transactional/multi-patch still
   open. Abstraction does not widen the merged claim. Good.

**Verdict.** Real and non-vacuous, but its honest form is narrower than the slogan:
*"On a linear OPH carrier, a nontrivial conserved quantity (⇔ nontrivial Hfib fiber, by
rank–nullity) obstructs every single-site frustration-free local repair."* The one genuine
new theorem to earn is objection 2's IFF; everything else is bookkeeping the Rule90 proof
already did. Next concrete step: prove the rank–nullity link on a 2-example (Rule90 +
one parity carrier) before abstracting.
