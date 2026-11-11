/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator

set_option backward.isDefEq.respectTransparency false

/-!
# Oracle problems with internal randomness (paper §3)

Formal model for Harrow–Rosenbaum, *Uselessness for an Oracle Model with Internal
Randomness*, arXiv:1111.1462v2 (23 Sep 2013), §3, pp. 4–7.

The paper's oracle has a control register `x ∈ [N]`, a target `y ∈ [M]`, and an
internal random seed `r` drawn from `R`.  For every `x` and `r` the oracle acts on
the target by a permutation `π_{x,r} ∈ S_M`; the promised set of oracles is `C`,
partitioned into classes `C_j`, with a prior `μ` over `C`.  A `k`-query classical
session draws one oracle `π ~ μ` and a seed vector `r ~ R^k` (Definition 8 of the
paper), and observes `π_{x_i,r_i}(y_i) = z_i` for `i < k`.

This file sets up:

* `OracleProblem` — the finite model of `(C, μ)`, the class partition, and `R`;
* `OracleProblem.joint` — the joint law of `(π, r)` for a `k`-query session
  (the product measure `μ ⊗ R^k`);
* `OracleProblem.classProb` / `classEventProb` / `probOfPred` — the elementary
  probabilities appearing in Definitions 6–8;
* `WeakUseless` (Definition 6), `PairwiseUseless` (Definition 8), and
  `WeakPairUseless` (the seed-independent `2k`-query form used in Corollary 10);
* `sigmaEntry` — the matrix element `tr(|x⟩⟨x'| ⊗ |y⟩⟨y'| ⊗ |z⟩⟨z'|) σ_j` of the
  class-averaged `k`-copy encoding `σ_j = E_{π ∈ C_j} ρ_π^k` (see `Encoding.lean`);
* `QuantumUseless` — the operational form of Definition 4: no matrix element of
  the encoding separates the classes (this is Corollary 16 of the paper, whose
  equivalence with Definition 4 is Theorem 15 + the standard fact that a density
  matrix is determined by its matrix elements);
* `ReadoutUseless` — the same statement tested against every linear read-out of
  the matrix-element family (i.e. every POVM element).

The main results proved in this file are the algebraic core of the paper:

* `readoutUseless_iff_quantumUseless` — Corollary 16 in read-out form;
* `quantumUseless_iff_pairwiseUseless` — Theorem 9 (p. 6);
* `corollary10` — Corollary 10 (p. 6), the deterministic specialisation.

Everything is finite real arithmetic on `FinDist`; no measure theory, no ``sorry``.
-/

namespace Qatlib.Papers.OracleUseless11.MainResults

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open scoped BigOperators

set_option autoImplicit false

/-- An oracle problem `(C, μ)` with internal randomness, paper §3, p. 4.

* `C` is the promised set of oracles, `classOf : C → J` the partition into the
  classes `C_j` (the paper's `{C_j}`);
* `R` is the type of internal random seeds with law `seedLaw` (the paper's `R`);
* `perm c x r` is the permutation `π_{x,r} ∈ S_M` applied to the target;
* `prior` is the distribution `μ` over `C`; it is positive on every oracle
  (the paper's proviso "provided the probability of each class is positive",
  p. 6, is enforced through `prior_pos` and `classOf_surj`). -/
structure OracleProblem (X Y : Type*) [Fintype X] [Fintype Y] where
  /-- Promised set of oracles. -/
  C : Type*
  [fintypeC : Fintype C]
  [decEqC : DecidableEq C]
  /-- Index type of the partition `{C_j}`. -/
  J : Type*
  [fintypeJ : Fintype J]
  [decEqJ : DecidableEq J]
  /-- Type of internal random seeds. -/
  R : Type*
  [fintypeR : Fintype R]
  [decEqR : DecidableEq R]
  [nonemptyR : Nonempty R]
  /-- The permutation `π_{x,r}` applied to the target on control `x` with seed `r`. -/
  perm : C → X → R → Equiv.Perm Y
  /-- Membership of an oracle in its class `C_j`. -/
  classOf : C → J
  /-- Prior `μ` over the promised set. -/
  prior : FinDist C
  /-- Law of the internal seeds. -/
  seedLaw : FinDist R
  /-- Every oracle has positive prior mass (paper p. 6). -/
  prior_pos : ∀ c, 0 < prior.prob c
  /-- Every class index is attained (we only index the nonempty classes). -/
  classOf_surj : Function.Surjective classOf

attribute [instance] OracleProblem.fintypeC OracleProblem.decEqC OracleProblem.fintypeJ
  OracleProblem.decEqJ OracleProblem.fintypeR OracleProblem.decEqR OracleProblem.nonemptyR

namespace OracleProblem

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- The joint law of `(π, r)` for a `k`-query session: `π ~ μ` and `r ~ R^k`
(paper p. 4: "if the oracle is queried `k` times, then `r = (r_1, …, r_k)` is
distributed according to `R^k`"). -/
noncomputable def joint (P : OracleProblem X Y) (k : ℕ) : FinDist (P.C × (Fin k → P.R)) where
  prob ω := P.prior.prob ω.1 * P.seedLaw.probOf ω.2
  nonneg ω := mul_nonneg (P.prior.nonneg ω.1) (Finset.prod_nonneg (fun i _ => P.seedLaw.nonneg (ω.2 i)))
  sum_one := by
    have h1 : ∑ ω : P.C × (Fin k → P.R), P.prior.prob ω.1 * P.seedLaw.probOf ω.2
        = ∑ c : P.C, ∑ r0 : Fin k → P.R, P.prior.prob c * P.seedLaw.probOf r0 := by
      rw [Fintype.sum_prod_type]
    have h2 : ∀ c : P.C,
        (∑ r0 : Fin k → P.R, P.prior.prob c * P.seedLaw.probOf r0) = P.prior.prob c := by
      intro c
      rw [← Finset.mul_sum, P.seedLaw.sum_probOf k, mul_one]
    rw [h1]
    simp_rw [h2]
    exact P.prior.sum_one

/-- Probability of a predicate on the `k`-query joint sample. -/
noncomputable def probOfPred (P : OracleProblem X Y) (k : ℕ)
    (E : P.C × (Fin k → P.R) → Prop) : ℝ :=
  by classical exact ∑ ω : P.C × (Fin k → P.R), if E ω then (P.joint k).prob ω else 0

/-- Prior probability of the class `C_j`. -/
noncomputable def classProb (P : OracleProblem X Y) (j : P.J) : ℝ :=
  by classical exact ∑ c : P.C, if P.classOf c = j then P.prior.prob c else 0

/-- Joint probability of "`π ∈ C_j` and the event `E`" under the `k`-query law. -/
noncomputable def classEventProb (P : OracleProblem X Y) (k : ℕ) (j : P.J)
    (E : P.C × (Fin k → P.R) → Prop) : ℝ :=
  by classical exact
    ∑ ω : P.C × (Fin k → P.R), if P.classOf ω.1 = j ∧ E ω then (P.joint k).prob ω else 0

/-- Every prior mass is positive. -/
theorem prior_prob_pos (P : OracleProblem X Y) (c : P.C) : 0 < P.prior.prob c :=
  P.prior_pos c

/-- Each class has positive prior probability (paper p. 6). -/
theorem classProb_pos (P : OracleProblem X Y) (j : P.J) : 0 < P.classProb j := by
  classical
  obtain ⟨c, hc⟩ := P.classOf_surj j
  unfold classProb
  have hmem : c ∈ Finset.univ.filter (fun c' => P.classOf c' = j) := by
    simp [hc]
  have hpos : 0 < ∑ c' ∈ Finset.univ.filter (fun c' => P.classOf c' = j), P.prior.prob c' :=
    Finset.sum_pos (fun c' _ => P.prior_pos c') ⟨c, hmem⟩
  have hrew : (∑ c' ∈ Finset.univ.filter (fun c' => P.classOf c' = j), P.prior.prob c')
      = ∑ c' : P.C, if P.classOf c' = j then P.prior.prob c' else 0 := by
    rw [Finset.sum_filter]
  rw [hrew] at hpos
  exact hpos

/-- The class probabilities sum to one: the `{C_j}` partition `C`. -/
theorem sum_classProb (P : OracleProblem X Y) : ∑ j : P.J, P.classProb j = 1 := by
  classical
  unfold classProb
  rw [Finset.sum_comm]
  have h : ∀ c : P.C,
      (∑ j : P.J, if P.classOf c = j then P.prior.prob c else 0) = P.prior.prob c := by
    intro c
    rw [Finset.sum_eq_single (P.classOf c)]
    · simp
    · intro j _ hj
      have : P.classOf c ≠ j := fun h => hj h.symm
      simp [this]
    · intro hcon
      exact absurd (Finset.mem_univ (P.classOf c)) hcon
  rw [Finset.sum_congr rfl (fun c _ => h c), P.prior.sum_one]

/-- The class-event probabilities sum to the event probability. -/
theorem sum_classEventProb (P : OracleProblem X Y) (k : ℕ)
    (E : P.C × (Fin k → P.R) → Prop) :
    ∑ j : P.J, P.classEventProb k j E = P.probOfPred k E := by
  classical
  unfold classEventProb probOfPred
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  by_cases hE : E ω
  · have : ∀ j : P.J, (if P.classOf ω.1 = j ∧ E ω then (P.joint k).prob ω else 0)
        = if P.classOf ω.1 = j then (P.joint k).prob ω else 0 := by
      intro j
      by_cases hj : P.classOf ω.1 = j
      · simp [hj, hE]
      · simp [hj]
    rw [Finset.sum_congr rfl (fun j _ => this j)]
    rw [Finset.sum_eq_single (P.classOf ω.1)]
    · simp [hE]
    · intro j _ hj
      have : P.classOf ω.1 ≠ j := fun h => hj h.symm
      simp [this]
    · intro hcon; exact absurd (Finset.mem_univ (P.classOf ω.1)) hcon
  · simp [hE]

/-- Probability of a conjunction of `j ≠ j'`-free statements: if `E` does not
occur, both sides vanish.  (Used only to unfold the definitions.) -/
theorem classEventProb_eq_zero_of_not (P : OracleProblem X Y) (k : ℕ) (j : P.J)
    (E : P.C × (Fin k → P.R) → Prop) (h : ∀ ω, ¬ E ω) :
    P.classEventProb k j E = 0 := by
  classical
  unfold classEventProb
  refine Finset.sum_eq_zero (fun ω _ => ?_)
  simp [h ω]

/-! ## Query events and the uselessness definitions -/

/-- The `k`-query classical answer event of Definitions 6–8:
`∀ i, π_{x_i,r_i}(y_i) = z_i`. -/
def answerEvent (P : OracleProblem X Y) (k : ℕ) (x : Fin k → X) (y z : Fin k → Y) :
    P.C × (Fin k → P.R) → Prop :=
  fun ω => ∀ i, P.perm ω.1 (x i) (ω.2 i) (y i) = z i

/-- The `2k`-query pairwise answer event of Definition 8 (p. 5): the two
coordinates of each pair share the seed `r_i`. -/
def pairAnswerEvent (P : OracleProblem X Y) (k : ℕ)
    (x x' : Fin k → X) (y y' z z' : Fin k → Y) :
    P.C × (Fin k → P.R) → Prop :=
  fun ω => ∀ i, P.perm ω.1 (x i) (ω.2 i) (y i) = z i ∧
    P.perm ω.1 (x' i) (ω.2 i) (y' i) = z' i

/-- Joint law of two independent `k`-query sessions, used for the "`2k`
classical queries" of Corollary 10 when seeds are irrelevant (deterministic
oracles). -/
noncomputable def jointPair (P : OracleProblem X Y) (k : ℕ) :
    FinDist (P.C × (Fin k → P.R) × (Fin k → P.R)) where
  prob ω := P.prior.prob ω.1 * P.seedLaw.probOf ω.2.1 * P.seedLaw.probOf ω.2.2
  nonneg ω :=
    mul_nonneg (mul_nonneg (P.prior.nonneg ω.1)
      (Finset.prod_nonneg (fun i _ => P.seedLaw.nonneg (ω.2.1 i))))
      (Finset.prod_nonneg (fun i _ => P.seedLaw.nonneg (ω.2.2 i)))
  sum_one := by
    have h1 : ∑ ω : P.C × (Fin k → P.R) × (Fin k → P.R),
        P.prior.prob ω.1 * P.seedLaw.probOf ω.2.1 * P.seedLaw.probOf ω.2.2
        = ∑ c : P.C, ∑ r1 : Fin k → P.R, ∑ r2 : Fin k → P.R,
            P.prior.prob c * P.seedLaw.probOf r1 * P.seedLaw.probOf r2 := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [Fintype.sum_prod_type]
    have h2 : ∀ c : P.C,
        (∑ r1 : Fin k → P.R, ∑ r2 : Fin k → P.R,
            P.prior.prob c * P.seedLaw.probOf r1 * P.seedLaw.probOf r2) = P.prior.prob c := by
      intro c
      have : ∀ r1 : Fin k → P.R,
          (∑ r2 : Fin k → P.R, P.prior.prob c * P.seedLaw.probOf r1 * P.seedLaw.probOf r2)
            = P.prior.prob c * P.seedLaw.probOf r1 := by
        intro r1
        rw [← Finset.mul_sum, P.seedLaw.sum_probOf k, mul_one]
      simp_rw [this]
      rw [← Finset.mul_sum, P.seedLaw.sum_probOf k, mul_one]
    rw [h1]
    simp_rw [h2]
    exact P.prior.sum_one

/-- Probability of a predicate on the two-session sample. -/
noncomputable def probOfPredPair (P : OracleProblem X Y) (k : ℕ)
    (E : P.C × (Fin k → P.R) × (Fin k → P.R) → Prop) : ℝ :=
  by classical exact
    ∑ ω : P.C × (Fin k → P.R) × (Fin k → P.R), if E ω then (P.jointPair k).prob ω else 0

/-- Joint probability of "`π ∈ C_j` and a two-session event". -/
noncomputable def classEventProbPair (P : OracleProblem X Y) (k : ℕ) (j : P.J)
    (E : P.C × (Fin k → P.R) × (Fin k → P.R) → Prop) : ℝ :=
  by classical exact
    ∑ ω : P.C × (Fin k → P.R) × (Fin k → P.R),
      if P.classOf ω.1 = j ∧ E ω then (P.jointPair k).prob ω else 0

/-- Definition 6 (weak classical uselessness, p. 5), division-free form:
`P(C_j ∧ E) = P(C_j)·P(E)` for every `k`-query answer event.  When `P(E) > 0`
this is exactly `Pr(π ∈ C_j | E) = Pr(π ∈ C_j)`. -/
def WeakUseless (P : OracleProblem X Y) (k : ℕ) : Prop :=
  ∀ (x : Fin k → X) (y z : Fin k → Y) (j : P.J),
    P.classEventProb k j (P.answerEvent k x y z)
      = P.classProb j * P.probOfPred k (P.answerEvent k x y z)

/-- Definition 8 (pairwise classical uselessness, p. 5), division-free form. -/
def PairwiseUseless (P : OracleProblem X Y) (k : ℕ) : Prop :=
  ∀ (x x' : Fin k → X) (y y' z z' : Fin k → Y) (j : P.J),
    P.classEventProb k j (P.pairAnswerEvent k x x' y y' z z')
      = P.classProb j * P.probOfPred k (P.pairAnswerEvent k x x' y y' z z')

/-- Weak classical uselessness of `2k` queries written in paired form with two
independent seed vectors (Corollary 10).  When the oracle is deterministic the
seed vectors are irrelevant, so this is the same condition as Definition 6 for
`2k` queries. -/
def WeakPairUseless (P : OracleProblem X Y) (k : ℕ) : Prop :=
  ∀ (x x' : Fin k → X) (y y' z z' : Fin k → Y) (j : P.J),
    P.classEventProbPair k j (fun ω => ∀ i : Fin k,
        (P.perm ω.1 (x i) (ω.2.1 i) (y i) = z i ∧
         P.perm ω.1 (x' i) (ω.2.2 i) (y' i) = z' i))
      = P.classProb j * P.probOfPredPair k (fun ω => ∀ i : Fin k,
        (P.perm ω.1 (x i) (ω.2.1 i) (y i) = z i ∧
         P.perm ω.1 (x' i) (ω.2.2 i) (y' i) = z' i))

/-! ## The class-averaged encoding matrix elements -/

/-- The matrix element `tr(|x⟩⟨x'| ⊗ |y⟩⟨y'| ⊗ |z⟩⟨z'|) σ_j` of the
class-averaged `k`-copy encoding `σ_j = E_{π ∈ C_j} ρ_π^k` (paper §3.3, p. 7).
By Definition 12/13 and Theorem 15 this equals the conditional probability of
the pairwise transcript given `π ∈ C_j`. -/
noncomputable def sigmaEntry (P : OracleProblem X Y) (k : ℕ) (j : P.J)
    (x x' : Fin k → X) (y y' z z' : Fin k → Y) : ℝ :=
  P.classEventProb k j (P.pairAnswerEvent k x x' y y' z z') / P.classProb j

/-- **Quantum uselessness** (Definition 4, p. 5) in the operational form supplied
by Theorem 15 and Corollary 16: no matrix element of the `k`-copy encoding
`ρ_π^k` distinguishes the classes, i.e. all `σ_j` coincide. -/
def QuantumUseless (P : OracleProblem X Y) (k : ℕ) : Prop :=
  ∀ (j j' : P.J) (x x' : Fin k → X) (y y' z z' : Fin k → Y),
    P.sigmaEntry k j x x' y y' z z' = P.sigmaEntry k j' x x' y y' z z'

/-- The index set of the matrix elements of the `k`-copy encoding. -/
abbrev PairIndex (k : ℕ) (X Y : Type*) :=
  (Fin k → X) × (Fin k → X) × (Fin k → Y) × (Fin k → Y) × (Fin k → Y) × (Fin k → Y)

/-- The matrix element of `σ_j` at a packaged index. -/
noncomputable def sigmaEntryAt (P : OracleProblem X Y) (k : ℕ) (j : P.J)
    (i : PairIndex k X Y) : ℝ :=
  P.sigmaEntry k j i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2.1 i.2.2.2.2.2

/-- No linear read-out of the matrix-element family can separate the classes;
this is the "any POVM measurement" of Definition 4, since a POVM element is a
linear functional `σ ↦ ∑ i, w i * σᵢ` of the matrix elements. -/
def ReadoutUseless (P : OracleProblem X Y) (k : ℕ) : Prop :=
  ∀ (w : PairIndex k X Y → ℝ) (j j' : P.J),
    ∑ i : PairIndex k X Y, w i * P.sigmaEntryAt k j i
      = ∑ i : PairIndex k X Y, w i * P.sigmaEntryAt k j' i

/-! ## Corollary 16 in read-out form -/

/-- **Corollary 16 (read-out form, p. 7).**  No POVM element of the `k`-copy
encoding separates the classes iff all the `σ_j` coincide.  The `←` direction is
immediate; the `→` direction uses the delta read-outs `w = e_i`, i.e. the
projector onto a single matrix element. -/
theorem readoutUseless_iff_quantumUseless (P : OracleProblem X Y) (k : ℕ) :
    P.ReadoutUseless k ↔ P.QuantumUseless k := by
  constructor
  · classical
    intro h j j' x x' y y' z z'
    let i : PairIndex k X Y := (x, x', y, y', z, z')
    have hsingle : ∀ (f : PairIndex k X Y → ℝ) (i : PairIndex k X Y),
        ∑ i' : PairIndex k X Y, (if i' = i then (1 : ℝ) else 0) * f i' = f i := by
      intro f i
      rw [Finset.sum_eq_single i]
      · simp
      · intro b _ hb
        simp [hb]
      · intro hcon
        exact absurd (Finset.mem_univ i) hcon
    have hi := h (fun i' => if i' = i then (1 : ℝ) else 0) j j'
    rw [hsingle, hsingle] at hi
    simpa [i, sigmaEntryAt] using hi
  · intro h w j j'
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [sigmaEntryAt]
    rw [h j j' i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2.1 i.2.2.2.2.2]

/-! ## Theorem 9: quantum uselessness iff pairwise classical uselessness -/

/-- The consistency identity behind Theorem 9: the `σ_j`-entries average (with
weights `P(C_j)`) to the unconditional event probability. -/
theorem sum_classProb_mul_sigmaEntry (P : OracleProblem X Y) (k : ℕ)
    (x x' : Fin k → X) (y y' z z' : Fin k → Y) :
    ∑ j : P.J, P.classProb j * P.sigmaEntry k j x x' y y' z z'
      = P.probOfPred k (P.pairAnswerEvent k x x' y y' z z') := by
  classical
  have h : ∀ j : P.J,
      P.classProb j * P.sigmaEntry k j x x' y y' z z'
        = P.classEventProb k j (P.pairAnswerEvent k x x' y y' z z') := by
    intro j
    unfold sigmaEntry
    exact mul_div_cancel₀ _ (ne_of_gt (P.classProb_pos j))
  rw [Finset.sum_congr rfl (fun j _ => h j), P.sum_classEventProb]

/-- **Theorem 9 (p. 6).**  For any oracle problem `(C, μ)`, `k` quantum queries
are useless if and only if `2k` classical queries are pairwise useless.

Paper proof (§3.3, pp. 7–8): `k` quantum queries can be simulated by preparing
`ρ_π^k` (Theorem 15), so their power is exactly the matrix elements
`tr(|x⟩⟨x'| ⊗ |y⟩⟨y'| ⊗ |z⟩⟨z'|) σ_j`; these are independent of `j` for all
`x, x', y, y', z, z'` iff all `σ_j` agree (Corollary 16), and by Bayes' rule this
is exactly the pairwise classical uselessness of Definition 8. -/
theorem quantumUseless_iff_pairwiseUseless (P : OracleProblem X Y) (k : ℕ) :
    P.QuantumUseless k ↔ P.PairwiseUseless k := by
  constructor
  · intro h x x' y y' z z' j
    have hsum := P.sum_classProb_mul_sigmaEntry k x x' y y' z z'
    have hconst : ∀ j' : P.J, P.classProb j' * P.sigmaEntry k j' x x' y y' z z'
        = P.classProb j' * P.sigmaEntry k j x x' y y' z z' :=
      fun j' => by rw [h j' j x x' y y' z z']
    rw [Finset.sum_congr rfl (fun j' _ => hconst j')] at hsum
    rw [← Finset.sum_mul, P.sum_classProb, one_mul] at hsum
    have hce : P.classEventProb k j (P.pairAnswerEvent k x x' y y' z z')
        = P.classProb j * P.sigmaEntry k j x x' y y' z z' := by
      unfold sigmaEntry
      exact (mul_div_cancel₀ _ (ne_of_gt (P.classProb_pos j))).symm
    rw [hce, hsum]
  · intro h j j' x x' y y' z z'
    have hj : P.sigmaEntry k j x x' y y' z z'
        = P.probOfPred k (P.pairAnswerEvent k x x' y y' z z') := by
      unfold sigmaEntry
      rw [h x x' y y' z z' j]
      exact mul_div_cancel_left₀ _ (ne_of_gt (P.classProb_pos j))
    have hj' : P.sigmaEntry k j' x x' y y' z z'
        = P.probOfPred k (P.pairAnswerEvent k x x' y y' z z') := by
      unfold sigmaEntry
      rw [h x x' y y' z z' j']
      exact mul_div_cancel_left₀ _ (ne_of_gt (P.classProb_pos j'))
    rw [hj, hj']

end OracleProblem

end Qatlib.Papers.OracleUseless11.MainResults
