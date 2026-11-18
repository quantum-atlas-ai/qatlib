/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.DecisionTrees97.ClassicalWord.LevelPred
public import Qatlib.Papers.DecisionTrees97.UniformQueryBound
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The adaptive recovery process and its expected-query budget (Section III, second slice)

Fixed source quant-ph/9706062v2, Section III (the classical algorithm attributed to
M. Sipser).  Having identified a correct prefix, the source recovers the next hidden
bit by *trials*: it queries words with that prefix until the level predicate returns
the informative answer, which certifies the next bit ("First try various inputs
until you find an example `x_1…x_{n-1}` such that `f_{n-1}` is 1 on this input.
Then you know that `w_1 = x_1`", and onwards from each known prefix).  The uniform-query analysis
(`UniformQueryBound.lean`) proved that a uniformly drawn trial query is informative
with probability at least `1/4` whenever two positions remain free.  This module
composes those stages into the global process and proves the source's budget:

* `trialPMF`: the exact law of one trial — the joint distribution of the first
  informative query and the number of preceding failures; every outcome in its
  support stops at an informative query (`trialPMF_support`);
* `uniformQueryPMF`, `trialStep`, `trialPMF_step`: the operational uniform-draw
  repeat-until step and its fixed-point equation against the closed-form law;
* `countSeries`: the count-weighted geometric series identity, the analytic core of
  the budget;
* `stageTrial_exp_le`: geometric amplification of the uniform-query quarter bound — for any
  stage satisfying `IsUniformQueryStage` the expected number of queries of one trial
  is at most `4`;
* `tailStage`/`tailQuarter`: the two-free-position stage of the level predicate
  satisfies `IsUniformQueryStage` directly on the tail space, via the uniform-query
  cylinder counting lemma `cylinderCard`;
* `lvlAuxF_full_eq_staged`, `staged_eq_full_of_mem`: on correct-prefix inputs,
  the full-word level predicate is exactly the staged suffix oracle;
* `trialRecover`: the stage-by-stage recovery state machine — at each stage with two
  or more free positions it runs one trial, reads off the certified bit, and recurses
  on the tail with the flipped flag (the flag bookkeeping matches `flagAt` by
  `flagAt_step`; the tail step is the uniform-query analysis’s `tail_suf`);
* `trialRecover_correct`: every stopping run recovers all bits of the hidden word
  except possibly the last — a random trial can only stop at an informative answer,
  and an informative answer certifies the bit;
* `fullRecover`: the endpoint — after `m` trial stages the last bit is fixed by two
  evaluations of the final predicate under its one-hot promise (`twoEval_iff`
  decides the corresponding existence question by `endpoint_decides`), giving
  `fullRecover_correct`: the whole hidden word is recovered;
* `trialRecover_exp`, `fullRecover_exp`: the expected-query budget — at most
  `4 * m + 2` queries in expectation for a word of length `m + 1`: `m` trial stages,
  each of expected cost at most `4`, plus the two final evaluations.

Boundaries (deliberately not covered here): the staged quarter bound needs two free
positions, so the last bit is never read off a trial but from the promised two final
evaluations; the process is a `PMF`-level model with unbounded stopping time, not a
compiled finite-depth deterministic `QueryTree` computation, and the deterministic depth
lower bounds are not lifted to this randomized model; per-stage optimality (`1 / p`
instead of the amplified `4`) and the random walk of the source's separation result
are out of scope.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Qatlib.Papers.DecisionTrees97.AdaptiveRecovery

open Qatlib.Papers.DecisionTrees97.ClassicalWord.LevelPred
open Qatlib.Papers.DecisionTrees97.UniformQueryBound

open scoped ENNReal

/-! ### Expectation of extended-nonnegative random variables -/

/-- Expected value of an `ℝ≥0∞`-valued random variable under a probability mass
function: the mass-weighted total. -/
noncomputable def pexp {α : Type} (μ : PMF α) (X : α → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' a, X a * μ a

/-- Expectation under a point mass. -/
theorem pexp_pure {α : Type} [DecidableEq α] (a : α) (X : α → ℝ≥0∞) :
    pexp (PMF.pure a) X = X a := by
  have h1 : ∑ b ∈ ({a} : Finset α), (if b = a then X b else 0) = X a := by
    rw [Finset.sum_singleton]
    simp
  have h2 : ∑' b : ↥((( {a} : Finset α) : Set α)ᶜ), (if (b : α) = a then X b else 0) = 0 := by
    refine ENNReal.tsum_eq_zero.mpr fun b => ?_
    have hfalse : ((b : α) = a) = False :=
      propext ⟨fun h => b.2 (Finset.mem_singleton.mpr h), fun h => h.elim⟩
    simp only [hfalse, ite_false]
  have hkey : ∑' b : α, (if b = a then X b else 0) = X a := by
    calc ∑' b : α, (if b = a then X b else 0)
        = (∑ b ∈ ({a} : Finset α), (if b = a then X b else 0)) +
          (∑' b : ↥((( {a} : Finset α) : Set α)ᶜ), (if (b : α) = a then X b else 0)) :=
          (ENNReal.sum_add_tsum_compl _ _).symm
      _ = X a + 0 := by rw [h1, h2]
      _ = X a := add_zero _
  simpa only [pexp, PMF.pure_apply, mul_ite, mul_one, mul_zero] using hkey

/-- The expectation of a bind is the mass-weighted expectation of the continuation. -/
theorem pexp_bind {α β : Type} (μ : PMF α) (η : α → PMF β) (X : β → ℝ≥0∞) :
    pexp (μ.bind η) X = ∑' a, μ a * pexp (η a) X := by
  simp only [pexp, PMF.bind_apply]
  have h1 : ∀ b : β, X b * ∑' a : α, μ a * η a b = ∑' a : α, X b * (μ a * η a b) :=
    fun b => (ENNReal.tsum_mul_left (a := X b) (f := fun a => μ a * η a b)).symm
  simp only [h1]
  rw [ENNReal.tsum_comm (f := fun (b : β) (a : α) => X b * (μ a * η a b))]
  have key : ∀ a : α, ∑' b : β, X b * (μ a * η a b) = μ a * ∑' b : β, X b * η a b := by
    intro a
    rw [← ENNReal.tsum_mul_left]
    rw [show (fun b : β => X b * (μ a * η a b)) = (fun b : β => μ a * (X b * η a b)) from
      funext fun b => mul_left_comm (X b) (μ a) (η a b)]
  simp only [key]

/-! ### The general random trial and its law -/

/-- The number of queries in the query space that return the marker answer. -/
def informCard {Ω : Type} [Fintype Ω] (g : Ω → Bool) (marker : Bool) : ℕ :=
  (Finset.univ.filter fun q => g q = marker).card

/-- The uniform success mass of one trial: the fraction of the query space that
returns the marker answer. -/
noncomputable def trialSuccess {Ω : Type} [Fintype Ω] (g : Ω → Bool) (marker : Bool) :
    ℝ≥0∞ :=
  (informCard g marker : ℝ≥0∞) * (Fintype.card Ω : ℝ≥0∞)⁻¹

/-- The failure mass of one trial: the complementary fraction of the success mass. -/
noncomputable def trialFail {Ω : Type} [Fintype Ω] (g : Ω → Bool) (marker : Bool) :
    ℝ≥0∞ :=
  1 - trialSuccess g marker

/-- The success mass never exceeds one. -/
theorem trialSuccess_le_one {Ω : Type} [Fintype Ω] (g : Ω → Bool) (marker : Bool)
    (hS : ∃ q : Ω, g q = marker) : trialSuccess g marker ≤ 1 := by
  have hne : (Fintype.card Ω : ℝ≥0∞) ≠ 0 := by
    have hemp : Nonempty Ω := ⟨hS.choose⟩
    have hcz := Fintype.card_ne_zero (α := Ω)
    exact_mod_cast hcz
  have hle : (informCard g marker : ℝ≥0∞) ≤ (Fintype.card Ω : ℝ≥0∞) :=
    Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _))
  calc trialSuccess g marker
      = (informCard g marker : ℝ≥0∞) * (Fintype.card Ω : ℝ≥0∞)⁻¹ := rfl
    _ ≤ (Fintype.card Ω : ℝ≥0∞) * (Fintype.card Ω : ℝ≥0∞)⁻¹ := by gcongr
    _ = 1 := ENNReal.mul_inv_cancel hne (ENNReal.natCast_ne_top _)

/-- With an informative query present, the success mass is positive. -/
theorem trialSuccess_ne_zero {Ω : Type} [Fintype Ω] (g : Ω → Bool) (marker : Bool)
    (hS : ∃ q : Ω, g q = marker) : trialSuccess g marker ≠ 0 := by
  obtain ⟨q, hq⟩ := hS
  have hmem : q ∈ Finset.univ.filter (fun q => g q = marker) :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, hq⟩
  have hpos : 0 < informCard g marker := Finset.card_pos.2 ⟨q, hmem⟩
  have hne : 0 < (Fintype.card Ω : ℝ≥0∞) := by
    have hemp : Nonempty Ω := ⟨q⟩
    have hcz := Fintype.card_ne_zero (α := Ω)
    exact_mod_cast Nat.pos_of_ne_zero hcz
  exact (ENNReal.mul_pos (Nat.cast_pos.mpr hpos).ne'
    (ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top _)).ne').ne'

/-- With an informative query present, the success mass is finite. -/
theorem trialSuccess_ne_top {Ω : Type} [Fintype Ω] (g : Ω → Bool) (marker : Bool)
    (hS : ∃ q : Ω, g q = marker) : trialSuccess g marker ≠ ∞ := by
  have hlt : trialSuccess g marker < ∞ :=
    ENNReal.mul_lt_top (ENNReal.natCast_lt_top _)
      (ENNReal.inv_lt_top.mpr (by
        obtain ⟨q, hq⟩ := hS
        have hemp : Nonempty Ω := ⟨q⟩
        have hcz := Fintype.card_ne_zero (α := Ω)
        exact_mod_cast Nat.pos_of_ne_zero hcz))
  exact hlt.ne

/-- Removing the failure mass recovers the success mass. -/
theorem sub_trialFail {Ω : Type} [Fintype Ω] (g : Ω → Bool) (marker : Bool)
    (hS : ∃ q : Ω, g q = marker) : 1 - trialFail g marker = trialSuccess g marker :=
  ENNReal.sub_sub_cancel ENNReal.one_ne_top (trialSuccess_le_one g marker hS)

/-- Repeated addition converts to the cast product. -/
theorem nat_smul_eq_cast_mul (n : ℕ) (c : ℝ≥0∞) : n • c = (n : ℝ≥0∞) * c := by
  induction n with
  | zero => simp
  | succ n ih => rw [add_nsmul, one_nsmul, ih, Nat.cast_succ]; ring

/-- The uniform probability mass function on a nonempty finite query space. -/
noncomputable def uniformQueryPMF {Ω : Type} [Fintype Ω] [Nonempty Ω] : PMF Ω :=
  PMF.ofFintype (fun _ => (Fintype.card Ω : ℝ≥0∞)⁻¹) (by
    rw [Finset.sum_const, Finset.card_univ, nat_smul_eq_cast_mul]
    exact ENNReal.mul_inv_cancel (by exact_mod_cast Fintype.card_ne_zero (α := Ω))
      (ENNReal.natCast_ne_top _))

/-- Every uniform query has mass equal to the inverse query-space cardinality. -/
theorem uniformQueryPMF_apply {Ω : Type} [Fintype Ω] [Nonempty Ω] (q : Ω) :
    uniformQueryPMF q = (Fintype.card Ω : ℝ≥0∞)⁻¹ := rfl

/-- The number of queries that do not return the marker answer. -/
def failCard {Ω : Type} [Fintype Ω] (g : Ω → Bool) (marker : Bool) : ℕ :=
  (Finset.univ.filter fun q => g q ≠ marker).card

/-- Informative and non-informative query counts add up to the whole query space. -/
theorem informCard_add_failCard {Ω : Type} [Fintype Ω] (g : Ω → Bool) (marker : Bool) :
    informCard g marker + failCard g marker = Fintype.card Ω := by
  simpa only [informCard, failCard, Finset.card_univ] using
    (Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset Ω)) (fun q => g q = marker))

/-- The failure mass is the uniform mass of all non-informative queries. -/
theorem trialFail_eq_failCard {Ω : Type} [Fintype Ω] (g : Ω → Bool) (marker : Bool)
    (hS : ∃ q : Ω, g q = marker) :
    trialFail g marker = (failCard g marker : ℝ≥0∞) * (Fintype.card Ω : ℝ≥0∞)⁻¹ := by
  have hemp : Nonempty Ω := ⟨hS.choose⟩
  have hne : (Fintype.card Ω : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := Ω)
  have hsum : trialSuccess g marker +
      (failCard g marker : ℝ≥0∞) * (Fintype.card Ω : ℝ≥0∞)⁻¹ = 1 := by
    calc trialSuccess g marker +
          (failCard g marker : ℝ≥0∞) * (Fintype.card Ω : ℝ≥0∞)⁻¹
        = ((informCard g marker + failCard g marker : ℕ) : ℝ≥0∞) *
            (Fintype.card Ω : ℝ≥0∞)⁻¹ := by
          rw [Nat.cast_add, add_mul]
          rfl
      _ = (Fintype.card Ω : ℝ≥0∞) * (Fintype.card Ω : ℝ≥0∞)⁻¹ := by
          rw [informCard_add_failCard]
      _ = 1 := ENNReal.mul_inv_cancel hne (ENNReal.natCast_ne_top _)
  rw [trialFail]
  exact ENNReal.sub_eq_of_eq_add (trialSuccess_ne_top g marker hS)
    (hsum.symm.trans (add_comm _ _))

/-- One operational step of a repeat-until trial: draw a uniform query, stop with
zero preceding failures if it is informative, and otherwise run the continuation
and increment its preceding-failure count. -/
noncomputable def trialStep {Ω : Type} [Fintype Ω]
    (g : Ω → Bool) (marker : Bool) (hS : ∃ q : Ω, g q = marker)
    (μ : PMF (Ω × ℕ)) : PMF (Ω × ℕ) :=
  (@uniformQueryPMF Ω _ ⟨hS.choose⟩).bind fun q =>
    if g q = marker then PMF.pure (q, 0)
    else μ.map fun p => (p.1, p.2 + 1)

/-- The mass function of one Sipser-style trial: the process fails through `t`
non-informative queries (each with the uniform failure mass) and then stops at the
informative query `q`. -/
noncomputable def trialMass {Ω : Type} [Fintype Ω] (g : Ω → Bool) (marker : Bool) :
    Ω × ℕ → ℝ≥0∞ :=
  fun p => if g p.1 = marker then
    trialFail g marker ^ p.2 * (Fintype.card Ω : ℝ≥0∞)⁻¹ else 0

/-- The total of a constant over the informative queries, in mass form. -/
theorem sum_indicator_inform {Ω : Type} [Fintype Ω] (g : Ω → Bool) (marker : Bool)
    (c : ℝ≥0∞) :
    ∑ q ∈ Finset.univ, (if g q = marker then c else 0) =
      (informCard g marker : ℝ≥0∞) * c := by
  have h1 : ∑ q ∈ Finset.univ, (if g q = marker then c else 0) =
      ∑ q ∈ Finset.univ.filter (fun q => g q = marker), c := (Finset.sum_filter _ _).symm
  rw [h1, Finset.sum_const, informCard, nat_smul_eq_cast_mul]

/-- The total of a constant over the non-informative queries, in mass form. -/
theorem sum_indicator_fail {Ω : Type} [Fintype Ω] (g : Ω → Bool) (marker : Bool)
    (c : ℝ≥0∞) :
    ∑ q ∈ Finset.univ, (if g q = marker then 0 else c) =
      (failCard g marker : ℝ≥0∞) * c := by
  have h1 : ∑ q ∈ Finset.univ, (if g q = marker then 0 else c) =
      ∑ q ∈ Finset.univ.filter (fun q => g q ≠ marker), c := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro q _
    by_cases hq : g q = marker <;> simp [hq]
  rw [h1, Finset.sum_const, failCard, nat_smul_eq_cast_mul]

/-- The trial mass is a probability distribution whenever an informative query
exists: the failure mass telescopes against the geometric tail. -/
theorem trialMass_total {Ω : Type} [Fintype Ω] (g : Ω → Bool) (marker : Bool)
    (hS : ∃ q : Ω, g q = marker) : ∑' p, trialMass g marker p = 1 := by
  have hgeo : (∑' t : ℕ, trialFail g marker ^ t) = (trialSuccess g marker)⁻¹ := by
    rw [ENNReal.tsum_geometric, sub_trialFail g marker hS]
  have hq : ∀ q : Ω, ∑' t : ℕ, trialMass g marker (q, t) =
      (if g q = marker then
        (∑' t : ℕ, trialFail g marker ^ t) * (Fintype.card Ω : ℝ≥0∞)⁻¹ else 0) := by
    intro q
    by_cases hq2 : g q = marker
    · have htr : (g q = marker) = True := propext ⟨fun _ => trivial, fun _ => hq2⟩
      have hf : (fun t : ℕ => trialMass g marker (q, t)) =
          (fun t : ℕ => trialFail g marker ^ t * (Fintype.card Ω : ℝ≥0∞)⁻¹) := by
        funext t
        simp only [trialMass, htr, ite_true]
      rw [hf, ENNReal.tsum_mul_right]
      simp only [htr, ite_true]
    · have hfa : (g q = marker) = False :=
        propext ⟨fun h => hq2 h, fun h => h.elim⟩
      have hf : (fun t : ℕ => trialMass g marker (q, t)) = (fun _ => (0 : ℝ≥0∞)) := by
        funext t
        simp only [trialMass, hfa, ite_false]
      rw [hf]
      simp [hfa]
  calc ∑' p, trialMass g marker p
      = ∑' q : Ω, ∑' t : ℕ, trialMass g marker (q, t) := ENNReal.tsum_prod'
    _ = ∑' q : Ω, (if g q = marker then
          (∑' t : ℕ, trialFail g marker ^ t) * (Fintype.card Ω : ℝ≥0∞)⁻¹ else 0) := by
        simp only [hq]
    _ = (informCard g marker : ℝ≥0∞) *
          ((∑' t : ℕ, trialFail g marker ^ t) * (Fintype.card Ω : ℝ≥0∞)⁻¹) := by
        rw [tsum_fintype (f := fun q : Ω =>
          (if g q = marker then
            (∑' t : ℕ, trialFail g marker ^ t) * (Fintype.card Ω : ℝ≥0∞)⁻¹ else 0))]
        exact sum_indicator_inform g marker _
    _ = trialSuccess g marker * (∑' t : ℕ, trialFail g marker ^ t) := by
        rw [show trialSuccess g marker = (informCard g marker : ℝ≥0∞) *
          (Fintype.card Ω : ℝ≥0∞)⁻¹ from rfl]
        ring
    _ = 1 := by
        rw [hgeo, ENNReal.mul_inv_cancel (trialSuccess_ne_zero g marker hS)
          (trialSuccess_ne_top g marker hS)]

/-- The exact law of one Sipser-style trial: the joint distribution of the first
informative query and the number of preceding failed queries. -/
noncomputable def trialPMF {Ω : Type} [Fintype Ω] (g : Ω → Bool) (marker : Bool)
    (hS : ∃ q : Ω, g q = marker) : PMF (Ω × ℕ) :=
  ⟨trialMass g marker, ENNReal.summable.hasSum_iff.mpr (trialMass_total g marker hS)⟩

/-- Every outcome in the trial support stops at an informative query: the random
trial cannot stop anywhere else. -/
theorem trialPMF_support {Ω : Type} [Fintype Ω] (g : Ω → Bool) (marker : Bool)
    (hS : ∃ q : Ω, g q = marker) {p : Ω × ℕ} (hp : p ∈ (trialPMF g marker hS).support) :
    g p.1 = marker := by
  have hp0 : trialMass g marker p ≠ 0 := by
    rw [trialPMF] at hp
    exact hp
  simp only [trialMass] at hp0
  split at hp0
  · assumption
  · exact absurd rfl hp0

/-- Incrementing the failure count has zero mass at zero. -/
theorem map_succ_apply_zero {Ω : Type} (μ : PMF (Ω × ℕ)) (q : Ω) :
    (μ.map fun p => (p.1, p.2 + 1)) (q, 0) = 0 := by
  classical
  rw [PMF.map_apply]
  refine ENNReal.tsum_eq_zero.mpr fun p => ?_
  have hne : (q, 0) ≠ (p.1, p.2 + 1) := by
    intro h
    have hn := congrArg Prod.snd h
    dsimp only at hn
    omega
  simp only [hne, ite_false]

/-- Incrementing the failure count shifts the mass at `(q,t)` to `(q,t+1)`. -/
theorem map_succ_apply_succ {Ω : Type} (μ : PMF (Ω × ℕ)) (q : Ω) (t : ℕ) :
    (μ.map fun p => (p.1, p.2 + 1)) (q, t + 1) = μ (q, t) := by
  classical
  rw [PMF.map_apply]
  refine (tsum_eq_single (q, t) ?_).trans ?_
  · intro p hp
    have hne : (q, t + 1) ≠ (p.1, p.2 + 1) := by
      intro h
      apply hp
      apply Prod.ext
      · exact (congrArg Prod.fst h).symm
      · have hn := congrArg Prod.snd h
        dsimp only at hn
        omega
    simp only [hne, ite_false]
  · simp

/-- The closed-form trial law is exactly the operational repeat-until loop: after
one uniform query, an informative answer stops at `(q,0)`, while a failure runs
the same trial law again and increments the number of preceding failures. -/
theorem trialPMF_step {Ω : Type} [Fintype Ω] (g : Ω → Bool) (marker : Bool)
    (hS : ∃ q : Ω, g q = marker) :
    trialPMF g marker hS = trialStep g marker hS (trialPMF g marker hS) := by
  classical
  have hemp : Nonempty Ω := ⟨hS.choose⟩
  apply PMF.ext
  rintro ⟨q, t⟩
  change trialMass g marker (q, t) =
    trialStep g marker hS (trialPMF g marker hS) (q, t)
  cases t with
  | zero =>
      rw [trialStep, PMF.bind_apply]
      have hstep : ∀ a : Ω,
          uniformQueryPMF a *
              ((if g a = marker then PMF.pure (a, 0)
                else (trialPMF g marker hS).map fun p => (p.1, p.2 + 1)) (q, 0)) =
            if a = q then
              (if g q = marker then (Fintype.card Ω : ℝ≥0∞)⁻¹ else 0) else 0 := by
        intro a
        by_cases ha : a = q
        · subst a
          by_cases hq : g q = marker <;>
            simp [hq, uniformQueryPMF_apply]
        · by_cases hga : g a = marker <;>
            simp [ha, Ne.symm ha, hga, uniformQueryPMF_apply]
      simp only [hstep]
      rw [tsum_ite_eq]
      by_cases hq : g q = marker <;> simp [trialMass, hq]
  | succ t =>
      rw [trialStep, PMF.bind_apply]
      have hstep : ∀ a : Ω,
          uniformQueryPMF a *
              ((if g a = marker then PMF.pure (a, 0)
                else (trialPMF g marker hS).map fun p => (p.1, p.2 + 1)) (q, t + 1)) =
            if g a = marker then 0
            else (Fintype.card Ω : ℝ≥0∞)⁻¹ * trialPMF g marker hS (q, t) := by
        intro a
        by_cases ha : g a = marker
        · simp [ha, uniformQueryPMF_apply]
        · simp only [ha, ite_false]
          rw [map_succ_apply_succ, uniformQueryPMF_apply]
      simp only [hstep]
      rw [tsum_fintype, sum_indicator_fail, ← mul_assoc,
        ← trialFail_eq_failCard g marker hS]
      change (if g q = marker then
          trialFail g marker ^ (t + 1) * (Fintype.card Ω : ℝ≥0∞)⁻¹ else 0) =
        trialFail g marker * trialMass g marker (q, t)
      by_cases hq : g q = marker
      · simp only [trialMass, hq, ite_true, pow_succ]
        ring
      · simp [trialMass, hq]

/-! ### Geometric amplification of the quarter bound -/

/-- Forward map of the diagonal pairing: a pair of a length and an index below it
becomes the index and the length defect. -/
def diagEncode (p : Σ t : ℕ, Fin (t + 1)) : ℕ × ℕ := (p.2, p.1 - (p.2 : ℕ))

/-- Reverse map of the diagonal pairing. -/
def diagDecode (q : ℕ × ℕ) : Σ t : ℕ, Fin (t + 1) := ⟨q.1 + q.2, ⟨q.1, by omega⟩⟩

/-- The forward diagonal map is injective. -/
theorem diagEncode_injective : Function.Injective diagEncode := by
  intro p p' hp
  rcases p with ⟨t, k⟩
  rcases p' with ⟨t', k'⟩
  have hk : (k : ℕ) = (k' : ℕ) := by
    have hc := congrArg (fun q : ℕ × ℕ => q.1) hp
    simpa [diagEncode] using hc
  have h2 : t - (k : ℕ) = t' - (k' : ℕ) := by
    have hc := congrArg (fun q : ℕ × ℕ => q.2) hp
    simpa [diagEncode] using hc
  have hlt : (k : ℕ) < t + 1 := k.isLt
  have hlt' : (k' : ℕ) < t' + 1 := k'.isLt
  have ht : t = t' := by omega
  subst ht
  exact congrArg (Sigma.mk _) (Fin.val_inj.mp hk)

/-- The reverse diagonal map is injective. -/
theorem diagDecode_injective : Function.Injective diagDecode := by
  intro q q' hq
  rcases q with ⟨a, b⟩
  rcases q' with ⟨a', b'⟩
  have h1 : a + b = a' + b' := congrArg (fun p : Σ t : ℕ, Fin (t + 1) => (p.1 : ℕ)) hq
  have h2 : a = a' := congrArg (fun p : Σ t : ℕ, Fin (t + 1) => (p.2 : ℕ)) hq
  simp only [Prod.mk.injEq]
  exact ⟨h2, by omega⟩

/-- The count-weighted geometric series identity: the expected number of queries of
a trial with failure mass `r` factors as the square of the geometric series.  This
is the diagonal identity `∑' t, (t + 1) * r ^ t = (∑' k, r ^ k) ^ 2`, proved by the
pairing bijection between `Σ t, Fin (t + 1)` and `ℕ × ℕ`. -/
theorem countSeries (r : ℝ≥0∞) :
    ∑' t : ℕ, ((t : ℝ≥0∞) + 1) * r ^ t = (∑' k : ℕ, r ^ k) * (∑' j : ℕ, r ^ j) := by
  have hA : ∀ t : ℕ, ((t : ℝ≥0∞) + 1) * r ^ t = ∑' k : Fin (t + 1), r ^ t := by
    intro t
    have h1 : ∑' k : Fin (t + 1), r ^ t = ((t + 1 : ℕ) : ℝ≥0∞) * r ^ t := by
      rw [tsum_fintype (f := fun _ : Fin (t + 1) => r ^ t)]
      simp [Finset.sum_const]
    rw [h1, Nat.cast_add, Nat.cast_one]
  have h2 : ∑' t : ℕ, ((t : ℝ≥0∞) + 1) * r ^ t
      = ∑' p : Σ t : ℕ, Fin (t + 1), r ^ (p.1 : ℕ) := by
    rw [show (fun t : ℕ => ((t : ℝ≥0∞) + 1) * r ^ t) =
      (fun t : ℕ => ∑' k : Fin (t + 1), r ^ t) from funext hA]
    exact (ENNReal.tsum_sigma' (fun p : Σ t : ℕ, Fin (t + 1) => r ^ (p.1 : ℕ))).symm
  have hfwd : ∀ p : Σ t : ℕ, Fin (t + 1),
      ((diagEncode p).1 + (diagEncode p).2 : ℕ) = (p.1 : ℕ) := by
    intro p
    rcases p with ⟨t, k⟩
    simp only [diagEncode]
    have hlt : (k : ℕ) < t + 1 := k.isLt
    omega
  have h1 : ∑' p : Σ t : ℕ, Fin (t + 1), r ^ (p.1 : ℕ)
      ≤ ∑' q : ℕ × ℕ, r ^ (q.1 + q.2) :=
      le_trans (le_of_eq (by simp only [hfwd]))
        (ENNReal.tsum_comp_le_tsum_of_injective diagEncode_injective
          (fun q : ℕ × ℕ => r ^ (q.1 + q.2)))
  have hbwd : ∀ q : ℕ × ℕ, ((diagDecode q).1 : ℕ) = (q.1 + q.2 : ℕ) := by
    intro q
    rfl
  have h3 : ∑' q : ℕ × ℕ, r ^ (q.1 + q.2)
      ≤ ∑' p : Σ t : ℕ, Fin (t + 1), r ^ (p.1 : ℕ) :=
      le_trans (le_of_eq (by simp only [hbwd]))
        (ENNReal.tsum_comp_le_tsum_of_injective diagDecode_injective
          (fun p : Σ t : ℕ, Fin (t + 1) => r ^ (p.1 : ℕ)))
  have hR : ∑' q : ℕ × ℕ, r ^ (q.1 + q.2) = (∑' k : ℕ, r ^ k) * (∑' j : ℕ, r ^ j) := by
    have hstep : ∀ a : ℕ, ∑' b : ℕ, r ^ (a + b) = r ^ a * (∑' j : ℕ, r ^ j) := by
      intro a
      rw [show (fun b : ℕ => r ^ (a + b)) = (fun b : ℕ => r ^ a * r ^ b) from
        funext fun b => pow_add r a b, ENNReal.tsum_mul_left]
    calc ∑' q : ℕ × ℕ, r ^ (q.1 + q.2)
        = ∑' a : ℕ, ∑' b : ℕ, r ^ (a + b) := ENNReal.tsum_prod'
      _ = (∑' k : ℕ, r ^ k) * (∑' j : ℕ, r ^ j) := by
          simp only [hstep]
          exact ENNReal.tsum_mul_right
  rw [h2]
  exact le_antisymm (h1.trans (le_of_eq hR)) ((le_of_eq hR.symm).trans h3)

/-- Geometric amplification of the uniform-query quarter bound: for any stage, the expected
number of queries of one trial is the inverse success mass. -/
theorem trialPMF_exp_eq {Ω : Type} [Fintype Ω] (g : Ω → Bool) (marker : Bool)
    (hS : ∃ q : Ω, g q = marker) :
    pexp (trialPMF g marker hS) (fun p => ((p.2 : ℕ) + 1 : ℝ≥0∞)) =
      (trialSuccess g marker)⁻¹ := by
  have hgeo : (∑' t : ℕ, trialFail g marker ^ t) = (trialSuccess g marker)⁻¹ := by
    rw [ENNReal.tsum_geometric, sub_trialFail g marker hS]
  have hq : ∀ q : Ω, ∑' t : ℕ, (((t : ℕ) + 1 : ℝ≥0∞)) * trialMass g marker (q, t) =
      (if g q = marker then
        (∑' t : ℕ, ((t : ℝ≥0∞) + 1) * trialFail g marker ^ t) *
          (Fintype.card Ω : ℝ≥0∞)⁻¹ else 0) := by
    intro q
    by_cases hq2 : g q = marker
    · have htr : (g q = marker) = True := propext ⟨fun _ => trivial, fun _ => hq2⟩
      have hf : (fun t : ℕ => (((t : ℕ) + 1 : ℝ≥0∞)) * trialMass g marker (q, t)) =
          (fun t : ℕ => ((t : ℝ≥0∞) + 1) * trialFail g marker ^ t *
            (Fintype.card Ω : ℝ≥0∞)⁻¹) := by
        funext t
        simp only [trialMass, htr, ite_true, ← mul_assoc]
      rw [hf, ENNReal.tsum_mul_right]
      simp only [htr, ite_true]
    · have hfa : (g q = marker) = False :=
        propext ⟨fun h => hq2 h, fun h => h.elim⟩
      have hf : (fun t : ℕ => (((t : ℕ) + 1 : ℝ≥0∞)) * trialMass g marker (q, t)) =
          (fun _ => (0 : ℝ≥0∞)) := by
        funext t
        simp only [trialMass, hfa, ite_false, mul_zero]
      rw [hf]
      simp [hfa]
  calc pexp (trialPMF g marker hS) (fun p => ((p.2 : ℕ) + 1 : ℝ≥0∞))
      = ∑' q : Ω, ∑' t : ℕ, (((t : ℕ) + 1 : ℝ≥0∞)) * trialMass g marker (q, t) := by
        rw [pexp, ENNReal.tsum_prod']
        rfl
    _ = ∑' q : Ω, (if g q = marker then
          (∑' t : ℕ, ((t : ℝ≥0∞) + 1) * trialFail g marker ^ t) *
            (Fintype.card Ω : ℝ≥0∞)⁻¹ else 0) := by
        simp only [hq]
    _ = (informCard g marker : ℝ≥0∞) *
          ((∑' t : ℕ, ((t : ℝ≥0∞) + 1) * trialFail g marker ^ t) *
            (Fintype.card Ω : ℝ≥0∞)⁻¹) := by
        rw [tsum_fintype (f := fun q : Ω =>
          (if g q = marker then
            (∑' t : ℕ, ((t : ℝ≥0∞) + 1) * trialFail g marker ^ t) *
              (Fintype.card Ω : ℝ≥0∞)⁻¹ else 0))]
        exact sum_indicator_inform g marker _
    _ = (trialSuccess g marker) * ((trialSuccess g marker)⁻¹ *
          (trialSuccess g marker)⁻¹) := by
        simp only [countSeries (trialFail g marker), hgeo]
        rw [show trialSuccess g marker = (informCard g marker : ℝ≥0∞) *
          (Fintype.card Ω : ℝ≥0∞)⁻¹ from rfl]
        ring
    _ = (trialSuccess g marker)⁻¹ := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel (trialSuccess_ne_zero g marker hS)
          (trialSuccess_ne_top g marker hS), one_mul]

/-- A quarter condition on the query space produces an informative query. -/
theorem inform_nonempty_of_quarter {Ω : Type} [Fintype Ω] [Nonempty Ω] {g : Ω → Bool}
    {marker : Bool} (hquarter : Fintype.card Ω ≤ 4 * informCard g marker) :
    ∃ q : Ω, g q = marker := by
  by_contra hcon
  have hf : informCard g marker = 0 := by
    rw [informCard, Finset.card_eq_zero, Finset.filter_eq_empty_iff.mpr
      (fun x _ hx => hcon ⟨x, hx⟩)]
  have hzero : Fintype.card Ω = 0 := by omega
  exact Fintype.card_ne_zero hzero

/-- The expected number of queries of one trial is at most `4`: geometric
amplification of the uniform informative-query bound. -/
theorem stageTrial_exp_le {Ω : Type} [Fintype Ω] [Nonempty Ω] {g : Ω → Bool}
    {marker : Bool} {guess : Ω → Bool} {target : Bool}
    (st : IsUniformQueryStage g marker guess target) :
    pexp (trialPMF g marker (inform_nonempty_of_quarter st.quarter))
      (fun p => ((p.2 : ℕ) + 1 : ℝ≥0∞)) ≤ 4 := by
  have hS := inform_nonempty_of_quarter st.quarter
  have hcardle : (Fintype.card Ω : ℝ≥0∞) ≤ 4 * (informCard g marker : ℝ≥0∞) := by
    rw [informCard]
    exact_mod_cast st.quarter
  have hne : (Fintype.card Ω : ℝ≥0∞) ≠ 0 := by
    have hcz := Fintype.card_ne_zero (α := Ω)
    exact_mod_cast hcz
  have hone : (1 : ℝ≥0∞) ≤ 4 * trialSuccess g marker := by
    calc (1 : ℝ≥0∞) = (Fintype.card Ω : ℝ≥0∞) * (Fintype.card Ω : ℝ≥0∞)⁻¹ :=
          (ENNReal.mul_inv_cancel hne (ENNReal.natCast_ne_top _)).symm
      _ ≤ (4 * (informCard g marker : ℝ≥0∞)) * (Fintype.card Ω : ℝ≥0∞)⁻¹ := by gcongr
      _ = 4 * trialSuccess g marker := by
          rw [show trialSuccess g marker = (informCard g marker : ℝ≥0∞) *
            (Fintype.card Ω : ℝ≥0∞)⁻¹ from rfl]
          ring
  calc pexp (trialPMF g marker hS) (fun p => ((p.2 : ℕ) + 1 : ℝ≥0∞))
      = (trialSuccess g marker)⁻¹ := trialPMF_exp_eq g marker hS
    _ ≤ (trialSuccess g marker)⁻¹ * (4 * trialSuccess g marker) :=
          le_mul_of_one_le_right (by positivity) hone
    _ = ((trialSuccess g marker)⁻¹ * trialSuccess g marker) * 4 := by ring
    _ = 4 := by
          rw [ENNReal.inv_mul_cancel (trialSuccess_ne_zero g marker hS)
            (trialSuccess_ne_top g marker hS)]
          norm_num

/-! ### The tail stages of the level predicate -/

/-- Receiving the flipped answer at position zero certifies the zeroth bit: the
zero-level case of the source's identification step. -/
theorem identBit_zero {r : ℕ} (b : Bool) (v x : Fin (r + 1) → Bool)
    (h : lvlAuxF b v x = !b) : v ⟨0, by omega⟩ = x ⟨0, by omega⟩ := by
  by_cases hd : v ⟨0, by omega⟩ = x ⟨0, by omega⟩
  · exact hd
  · rw [lvlAuxF_step] at h
    split at h
    · exact absurd ‹_› hd
    · cases b <;> simp at h

/-- Two free positions force the flipped answer: an agreeing zeroth bit followed by
a differing first bit — the zero-level case of the forcing event. -/
theorem force_zero {r : ℕ} (b : Bool) (v t : Fin (r + 2) → Bool)
    (h0 : v ⟨0, by omega⟩ = t ⟨0, by omega⟩)
    (h1 : v ⟨1, by omega⟩ ≠ t ⟨1, by omega⟩) :
    lvlAuxF b v t = !b := by
  rw [lvlAuxF_step]
  split
  · rw [lvlAuxF_step]
    split
    · exact absurd ‹_› h1
    · rfl
  · exact absurd h0 ‹_›

/-- The parity flag flips at every position. -/
theorem flagAt_step (k : ℕ) : flagAt (k + 1) = !(flagAt k) := by
  simp only [flagAt]
  by_cases hk : k % 2 = 1
  · have h1 : (k + 1) % 2 = 0 := by omega
    simp [hk, h1]
  · have h0 : k % 2 = 0 := by omega
    have h2 : (k + 1) % 2 = 1 := by omega
    simp [h0, h2]

/-- The flag obtained by flipping an initial flag once for each stripped prefix
position. -/
def flipFlag : ℕ → Bool → Bool
  | 0, b => b
  | k + 1, b => flipFlag k (!b)

/-- Flipping the input flag commutes with stripping prefix positions. -/
theorem flipFlag_not (k : ℕ) (b : Bool) : flipFlag k (!b) = !(flipFlag k b) := by
  induction k generalizing b with
  | zero => rfl
  | succ k ih => simp [flipFlag, ih]

/-- Stripping `k` positions from the initial level-predicate flag gives `flagAt k`. -/
theorem flipFlag_flagAt (k : ℕ) : flipFlag k (flagAt 0) = flagAt k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change flipFlag k (!(flagAt 0)) = flagAt (k + 1)
      rw [flipFlag_not, ih, ← flagAt_step]

/-- The suffix determined by an explicit decomposition of the total word length. -/
def suffixFromEq {m k r : ℕ} (h : m = k + r) (w : Fin m → Bool) : Fin r → Bool :=
  fun i => w ⟨k + i.val, by have := i.isLt; omega⟩

/-- Taking the transported suffix after dropping a bit gives the next stage's suffix. -/
theorem suffixFromEq_tail {m k r : ℕ} (h : m + 1 = k + 1 + r) (hm : m = k + r)
    (w : Fin (m + 1) → Bool) :
    suffixFromEq hm (Fin.tail w) = suffixFromEq h w := by
  funext i
  apply congrArg w
  apply Fin.ext
  show k + i.val + 1 = k + 1 + i.val
  omega

/-- The full-word level predicate agrees with the staged suffix predicate after
any correct prefix.  The explicit length decomposition lets induction pass directly
to the tail without transporting reassociated `Fin` types. -/
theorem lvlAuxF_suf_transport {m k r : ℕ} (h : m = k + r) (b : Bool)
    (w x : Fin m → Bool) (hprefix : ∀ i : Fin m, (i : ℕ) < k → w i = x i) :
    lvlAuxF b w x =
      lvlAuxF (flipFlag k b) (suffixFromEq h w) (suffixFromEq h x) := by
  induction m generalizing k r b with
  | zero =>
      have hk : k = 0 := by omega
      have hr : r = 0 := by omega
      subst k
      subst r
      rfl
  | succ m ih =>
      cases k with
      | zero =>
          have hr : r = m + 1 := by omega
          subst r
          have hw : suffixFromEq h w = w := by
            funext i
            apply congrArg w
            apply Fin.ext
            simp
          have hx : suffixFromEq h x = x := by
            funext i
            apply congrArg x
            apply Fin.ext
            simp
          rw [hw, hx]
          rfl
      | succ k =>
          have hm : m = k + r := by omega
          rw [lvlAuxF_step]
          have h0 : w ⟨0, by omega⟩ = x ⟨0, by omega⟩ :=
            hprefix ⟨0, by omega⟩ (by change (0 : ℕ) < k + 1; omega)
          simp only [h0, ite_true]
          have htail : ∀ i : Fin m, (i : ℕ) < k → Fin.tail w i = Fin.tail x i := by
            intro i hi
            exact hprefix i.succ (by simp only [Fin.val_succ]; omega)
          simpa only [flipFlag, suffixFromEq_tail h hm] using
            (ih hm (!b) (Fin.tail w) (Fin.tail x) htail)

/-- The full-word level predicate agrees with the staged suffix predicate after
any correct prefix, with the initial flag flipped once per stripped position. -/
theorem lvlAuxF_suf_of_prefix (k r : ℕ) (b : Bool) (w x : Fin (k + r) → Bool)
    (hprefix : ∀ i : Fin (k + r), (i : ℕ) < k → w i = x i) :
    lvlAuxF b w x = lvlAuxF (flipFlag k b) (suf k r w) (suf k r x) :=
  lvlAuxF_suf_transport (m := k + r) rfl b w x hprefix

/-- On a correct-prefix input, evaluating the full-word level predicate from the
initial flag is exactly evaluating the staged oracle on the remaining suffix. -/
theorem lvlAuxF_full_eq_staged (k r : ℕ) (w x : Fin (k + r) → Bool)
    (hprefix : ∀ i : Fin (k + r), (i : ℕ) < k → w i = x i) :
    lvlAuxF (flagAt 0) w x =
      lvlAuxF (flagAt k) (suf k r w) (suf k r x) := by
  rw [← flipFlag_flagAt k]
  exact lvlAuxF_suf_of_prefix k r (flagAt 0) w x hprefix

/-- The staged tail oracle and the full-word predicate give the same answer on
every member of the correct-prefix query space. -/
theorem staged_eq_full_of_mem {k r : ℕ} {w x : Fin (k + r) → Bool}
    (hx : x ∈ prefixFixed k r w) :
    lvlAuxF (flagAt k) (suf k r w) (suf k r x) = lvlAuxF (flagAt 0) w x :=
  (lvlAuxF_full_eq_staged k r w x fun i hi => (mem_prefixFixed.mp hx i hi).symm).symm

/-- Quarter bound for tail stages: at least a quarter of all tails return the
flipped answer. -/
theorem tailQuarter {r : ℕ} (b : Bool) (v : Fin (r + 2) → Bool) :
    Fintype.card (Fin (r + 2) → Bool) ≤
      4 * (Finset.univ.filter fun t : Fin (r + 2) → Bool => lvlAuxF b v t = !b).card := by
  have hne : ∀ b2 : Bool, b2 ≠ !b2 := by decide
  have hsub : (Finset.univ.filter fun t : Fin (r + 2) → Bool =>
        t ⟨0, by omega⟩ = v ⟨0, by omega⟩ ∧ t ⟨1, by omega⟩ = !(v ⟨1, by omega⟩)) ⊆
      Finset.univ.filter fun t : Fin (r + 2) → Bool => lvlAuxF b v t = !b := by
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    refine force_zero b v t ht.1.symm ?_
    rw [ht.2]
    exact hne _
  have h1 := Finset.card_le_card hsub
  have h2 := cylinderCard r (v ⟨0, by omega⟩) (!(v ⟨1, by omega⟩))
  have h3 : Fintype.card (Fin (r + 2) → Bool) = 2 ^ (r + 2) := by simp
  have h4 : 2 ^ (r + 2) = 4 * 2 ^ r := by rw [pow_add, Nat.pow_two]; ring
  calc Fintype.card (Fin (r + 2) → Bool) = 2 ^ (r + 2) := h3
    _ = 4 * 2 ^ r := h4
    _ ≤ 4 * (Finset.univ.filter fun t : Fin (r + 2) → Bool =>
          lvlAuxF b v t = !b).card := Nat.mul_le_mul_left 4 (h2 ▸ h1)

/-- The two-free-position tail stage of the level predicate satisfies the uniform-query
uniform informative-query predicate. -/
theorem tailStage {r : ℕ} (b : Bool) (v : Fin (r + 2) → Bool) :
    IsUniformQueryStage (lvlAuxF b v) (!b)
      (fun t : Fin (r + 2) → Bool => t ⟨0, by omega⟩) (v ⟨0, by omega⟩) where
  certifies q h := (identBit_zero b v q h).symm
  quarter := tailQuarter b v

/-- A tail stage always has an informative query: the forcing cylinder is
nonempty. -/
theorem tailNonempty {r : ℕ} (b : Bool) (v : Fin (r + 2) → Bool) :
    ∃ t : Fin (r + 2) → Bool, lvlAuxF b v t = !b := by
  refine ⟨(Fin.cons (v ⟨0, by omega⟩)
      (Fin.cons (!(v ⟨1, by omega⟩)) (Fin.tail (Fin.tail v))) : Fin (r + 2) → Bool), ?_⟩
  refine force_zero b v _ rfl ?_
  exact (by decide : ∀ b2 : Bool, b2 ≠ !b2) (v ⟨1, by omega⟩)

/-- The expected number of queries of one tail stage is at most `4`. -/
theorem tailTrial_exp_le {r : ℕ} (b : Bool) (v : Fin (r + 2) → Bool) :
    pexp (trialPMF (lvlAuxF b v) (!b) (tailNonempty b v))
      (fun p => ((p.2 : ℕ) + 1 : ℝ≥0∞)) ≤ 4 :=
  stageTrial_exp_le (tailStage b v)

/-! ### The recovery state machine -/

/-- Two-step induction on the naturals: base cases zero and one, step from `r + 1`
to `r + 2`. -/
theorem twoStepInd {P : ℕ → Prop} (h0 : P 0) (h1 : P 1)
    (hs : ∀ r : ℕ, P (r + 1) → P (r + 2)) : ∀ r : ℕ, P r := by
  have H : ∀ N : ℕ, P N ∧ P (N + 1) := by
    intro N
    induction N with
    | zero => exact ⟨h0, h1⟩
    | succ N ih => exact ⟨ih.2, hs N ih.2⟩
  intro r
  exact (H r).1

/-- The stage-by-stage recovery process.  With two or more free positions, one
Sipser trial is run against the current tail oracle `lvlAuxF b v`; the stopped query
supplies the next bit, and the process recurses on the tail with the flipped flag.
With fewer than two free positions no trial is run (the last bit is supplied by the
promised two-evaluation endpoint of `fullRecover`).  The process accesses the hidden
word only through the stage oracles. -/
noncomputable def trialRecover : (r : ℕ) → Bool → (Fin r → Bool) → PMF ((Fin r → Bool) × ℕ)
  | 0, _, v => PMF.pure (v, 0)
  | 1, _, v => PMF.pure (v, 0)
  | r + 2, b, v =>
      (trialPMF (lvlAuxF b v) (!b) (tailNonempty b v)).bind fun p =>
        (trialRecover (r + 1) (!b) (Fin.tail v)).bind fun s =>
          PMF.pure (Fin.cons (p.1 ⟨0, by omega⟩) s.1, p.2 + 1 + s.2)
termination_by r => r

/-- Reading the tail at an index reads the original word at the successor index. -/
theorem tail_apply {r : ℕ} (v : Fin (r + 2) → Bool) (j : Fin (r + 1)) :
    Fin.tail v j = v j.succ := rfl

/-- Every stopping run of the trial recovery process recovers all bits of the
hidden word except possibly the last: a trial can only stop at an informative
answer, and an informative answer certifies the bit.  Correctness is claimed at
every position that is not the final one, i.e. at every index with a successor. -/
theorem trialRecover_correct : ∀ (r : ℕ) (b : Bool) (v : Fin r → Bool),
    ∀ o ∈ (trialRecover r b v).support, ∀ i : Fin r, (i : ℕ) + 1 < r → o.1 i = v i := by
  intro r
  induction r using twoStepInd with
  | h0 => intro b v o _ i hi; omega
  | h1 =>
      intro b v o _ i hi; omega
  | hs r ih =>
      intro b v o ho i hi
      simp only [trialRecover] at ho
      rw [PMF.mem_support_bind_iff] at ho
      obtain ⟨p, hp, ho'⟩ := ho
      rw [PMF.mem_support_bind_iff] at ho'
      obtain ⟨s, hs, ho''⟩ := ho'
      rw [PMF.mem_support_pure_iff] at ho''
      rw [ho'']
      have hpq : lvlAuxF b v p.1 = !b := trialPMF_support _ _ _ hp
      have hbit : v ⟨0, by omega⟩ = p.1 ⟨0, by omega⟩ := identBit_zero b v p.1 hpq
      have key : ∀ j : Fin (r + 1), (j : ℕ) + 1 < r + 1 → s.1 j = v j.succ := by
        intro j hj
        have hsub := ih (!b) (Fin.tail v) s hs j hj
        rw [hsub]
        exact tail_apply v j
      rcases Nat.eq_zero_or_pos (i : ℕ) with hi0 | hi0
      · have hi0e : i = (⟨0, by omega⟩ : Fin (r + 2)) := by
          simpa using hi0
        rw [hi0e]
        exact hbit.symm
      · obtain ⟨jv, hjv⟩ : ∃ jv : ℕ, (i : ℕ) = jv + 1 :=
          ⟨(i : ℕ) - 1, by omega⟩
        have hj : (⟨jv, by omega⟩ : Fin (r + 1)).succ = i :=
          Fin.ext (by simp only [Fin.val_succ]; omega)
        have hjlt : (jv : ℕ) + 1 < r + 1 := by omega
        rw [← hj]
        exact key ⟨jv, by omega⟩ hjlt

/-- The expected number of queries of the trial stages: at most `4` per stage with
two or more free positions, none below that. -/
theorem trialRecover_exp : ∀ (r : ℕ) (b : Bool) (v : Fin r → Bool),
    pexp (trialRecover r b v) (fun s => (s.2 : ℝ≥0∞)) ≤ ((4 * (r - 1) : ℕ) : ℝ≥0∞) := by
  intro r
  induction r using twoStepInd with
  | h0 =>
      intro b v
      simp [trialRecover, pexp]
  | h1 =>
      intro b v
      simp [trialRecover, pexp]
  | hs r ih =>
      intro b v
      have hinner : ∀ p : (Fin (r + 2) → Bool) × ℕ,
          pexp ((trialRecover (r + 1) (!b) (Fin.tail v)).bind fun s =>
              PMF.pure ((Fin.cons (p.1 ⟨0, by omega⟩) s.1 : Fin (r + 2) → Bool),
                p.2 + 1 + s.2))
            (fun s => (s.2 : ℝ≥0∞)) =
            (((p.2 : ℕ) + 1 : ℕ) : ℝ≥0∞) +
              pexp (trialRecover (r + 1) (!b) (Fin.tail v)) (fun s => (s.2 : ℝ≥0∞)) := by
        intro p
        have hcast : ∀ s : (Fin (r + 1) → Bool) × ℕ,
            (((p.2 : ℕ) + 1 + s.2 : ℕ) : ℝ≥0∞) =
              (((p.2 : ℕ) + 1 : ℕ) : ℝ≥0∞) + (s.2 : ℝ≥0∞) := by
          intro s
          rw [Nat.cast_add, Nat.cast_add, Nat.cast_one]
        rw [pexp_bind]
        have hcast : ∀ s : (Fin (r + 1) → Bool) × ℕ,
            (((p.2 : ℕ) + 1 + s.2 : ℕ) : ℝ≥0∞) =
              (((p.2 : ℕ) + 1 : ℕ) : ℝ≥0∞) + (s.2 : ℝ≥0∞) := by
          intro s
          rw [Nat.cast_add, Nat.cast_add, Nat.cast_one]
        have h1 : ∀ s : (Fin (r + 1) → Bool) × ℕ,
            pexp (PMF.pure ((Fin.cons (p.1 ⟨0, by omega⟩) s.1 : Fin (r + 2) → Bool),
                p.2 + 1 + s.2)) (fun s => (s.2 : ℝ≥0∞)) =
              (((p.2 : ℕ) + 1 + s.2 : ℕ) : ℝ≥0∞) :=
          fun s => pexp_pure _ _
        simp only [h1]
        have hdistr : ∀ s : (Fin (r + 1) → Bool) × ℕ,
            (trialRecover (r + 1) (!b) (Fin.tail v)) s *
                (((p.2 : ℕ) + 1 + s.2 : ℕ) : ℝ≥0∞) =
              (trialRecover (r + 1) (!b) (Fin.tail v)) s *
                (((p.2 : ℕ) + 1 : ℕ) : ℝ≥0∞) +
              (trialRecover (r + 1) (!b) (Fin.tail v)) s * (s.2 : ℝ≥0∞) :=
          fun s => by rw [hcast s]; ring
        simp only [hdistr]
        rw [ENNReal.tsum_add]
        have hleft : (∑' s : (Fin (r + 1) → Bool) × ℕ,
              (trialRecover (r + 1) (!b) (Fin.tail v)) s *
                (((p.2 : ℕ) + 1 : ℕ) : ℝ≥0∞)) =
            (((p.2 : ℕ) + 1 : ℕ) : ℝ≥0∞) := by
          rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
        have hright : (∑' s : (Fin (r + 1) → Bool) × ℕ,
              (trialRecover (r + 1) (!b) (Fin.tail v)) s * (s.2 : ℝ≥0∞)) =
            pexp (trialRecover (r + 1) (!b) (Fin.tail v)) (fun s => (s.2 : ℝ≥0∞)) := by
          simp only [pexp, mul_comm]
        rw [hleft, hright]
      calc pexp (trialRecover (r + 2) b v) (fun s => (s.2 : ℝ≥0∞))
          = ∑' p : (Fin (r + 2) → Bool) × ℕ,
              (trialPMF (lvlAuxF b v) (!b) (tailNonempty b v)) p *
                ((((p.2 : ℕ) + 1 : ℕ) : ℝ≥0∞) +
                  pexp (trialRecover (r + 1) (!b) (Fin.tail v)) (fun s => (s.2 : ℝ≥0∞))) := by
            simp only [trialRecover]
            rw [pexp_bind]
            simp only [hinner]
        _ = (∑' p : (Fin (r + 2) → Bool) × ℕ,
              (trialPMF (lvlAuxF b v) (!b) (tailNonempty b v)) p *
                (((p.2 : ℕ) + 1 : ℕ) : ℝ≥0∞)) +
            (pexp (trialRecover (r + 1) (!b) (Fin.tail v)) (fun s => (s.2 : ℝ≥0∞)) *
              ∑' p : (Fin (r + 2) → Bool) × ℕ,
                (trialPMF (lvlAuxF b v) (!b) (tailNonempty b v)) p) := by
            have hdistr : ∀ p : (Fin (r + 2) → Bool) × ℕ,
                (trialPMF (lvlAuxF b v) (!b) (tailNonempty b v)) p *
                  ((((p.2 : ℕ) + 1 : ℕ) : ℝ≥0∞) +
                    pexp (trialRecover (r + 1) (!b) (Fin.tail v)) (fun s => (s.2 : ℝ≥0∞))) =
                  (trialPMF (lvlAuxF b v) (!b) (tailNonempty b v)) p *
                    (((p.2 : ℕ) + 1 : ℕ) : ℝ≥0∞) +
                  (trialPMF (lvlAuxF b v) (!b) (tailNonempty b v)) p *
                    pexp (trialRecover (r + 1) (!b) (Fin.tail v))
                      (fun s => (s.2 : ℝ≥0∞)) :=
              fun p => mul_add _ _ _
            simp only [hdistr]
            rw [ENNReal.tsum_add]
            have hright : (∑' p : (Fin (r + 2) → Bool) × ℕ,
                (trialPMF (lvlAuxF b v) (!b) (tailNonempty b v)) p *
                  pexp (trialRecover (r + 1) (!b) (Fin.tail v)) (fun s => (s.2 : ℝ≥0∞))) =
                pexp (trialRecover (r + 1) (!b) (Fin.tail v)) (fun s => (s.2 : ℝ≥0∞)) *
                  ∑' p : (Fin (r + 2) → Bool) × ℕ,
                    (trialPMF (lvlAuxF b v) (!b) (tailNonempty b v)) p := by
              rw [ENNReal.tsum_mul_right]
              exact mul_comm _ _
            rw [hright]
        _ ≤ pexp (trialPMF (lvlAuxF b v) (!b) (tailNonempty b v))
              (fun p => ((p.2 : ℕ) + 1 : ℝ≥0∞)) +
            (pexp (trialRecover (r + 1) (!b) (Fin.tail v)) (fun s => (s.2 : ℝ≥0∞)) * 1) := by
            have hleft : (∑' p : (Fin (r + 2) → Bool) × ℕ,
                (trialPMF (lvlAuxF b v) (!b) (tailNonempty b v)) p *
                  (((p.2 : ℕ) + 1 : ℕ) : ℝ≥0∞)) =
                pexp (trialPMF (lvlAuxF b v) (!b) (tailNonempty b v))
                  (fun p => ((p.2 : ℕ) + 1 : ℝ≥0∞)) := by
              simp only [pexp, Nat.cast_add, Nat.cast_one, mul_comm]
            refine add_le_add (le_of_eq hleft) ?_
            rw [PMF.tsum_coe]
        _ = pexp (trialPMF (lvlAuxF b v) (!b) (tailNonempty b v))
              (fun p => ((p.2 : ℕ) + 1 : ℝ≥0∞)) +
            pexp (trialRecover (r + 1) (!b) (Fin.tail v)) (fun s => (s.2 : ℝ≥0∞)) := by
            rw [mul_one]
        _ ≤ ((4 : ℕ) : ℝ≥0∞) + ((4 * ((r + 1) - 1) : ℕ) : ℝ≥0∞) := by
            exact_mod_cast add_le_add (tailTrial_exp_le b v) (ih (!b) (Fin.tail v))
        _ = ((4 * (r + 2 - 1) : ℕ) : ℝ≥0∞) := by
            have hnat : (4 : ℕ) + 4 * ((r + 1) - 1) = 4 * (r + 2 - 1) := by omega
            rw [← Nat.cast_add]
            exact_mod_cast hnat

/-! ### The endpoint and the full recovery process -/

/-- Assembling a word from a recovered prefix and a recovered last bit. -/
theorem snoc_eq_of_prefix {m : ℕ} {v : Fin (m + 1) → Bool} (pre : Fin m → Bool)
    (bit : Bool) (hpre : ∀ i : Fin m, pre i = v i.castSucc)
    (hlast : bit = v (Fin.last m)) :
    Fin.snoc pre bit = v := by
  funext j
  by_cases hj : j = Fin.last m
  · rw [hj, Fin.snoc_last]
    exact hlast
  · obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.mpr hj
    rw [Fin.snoc_castSucc, hpre i]

/-- The complete adaptive recovery: `m` Sipser trial stages recover the first `m`
bits of the hidden word, then two evaluations of the final predicate `fn` fix the
last bit.  The process accesses the hidden word only through the stage oracles and
`fn`. -/
noncomputable def fullRecover {m : ℕ} (fn : ((Fin m → Bool) × Bool) → Bool)
    (w : Fin (m + 1) → Bool) : PMF ((Fin (m + 1) → Bool) × ℕ) :=
  (trialRecover (m + 1) (flagAt 0) w).bind fun s =>
    PMF.pure (Fin.snoc (fun i : Fin m => s.1 i.castSucc)
      (if fn ((fun i : Fin m => s.1 i.castSucc), false) then false else true), s.2 + 2)

/-- The two final evaluations decide the level-`n` question: the one-hot endpoint
lemma, instantiated at the hidden prefix. -/
theorem endpoint_decides {m : ℕ} (fn : ((Fin m → Bool) × Bool) → Bool)
    (w : Fin (m + 1) → Bool)
    (hpromise : ∀ p : (Fin m → Bool) × Bool, fn p = true →
      ∀ i : Fin m, p.1 i = w i.castSucc) :
    (∃ p : (Fin m → Bool) × Bool, fn p = true) ↔
      fn ((fun i : Fin m => w i.castSucc), false) = true ∨
      fn ((fun i : Fin m => w i.castSucc), true) = true :=
  twoEval_iff m (fun i : Fin m => w i.castSucc) fn hpromise

/-- The full recovery process recovers the hidden word: every stopping run outputs
`w` exactly, under the one-hot promise on the final predicate. -/
theorem fullRecover_correct {m : ℕ} (fn : ((Fin m → Bool) × Bool) → Bool)
    (w : Fin (m + 1) → Bool)
    (honehot : ∀ p : (Fin m → Bool) × Bool, fn p = true →
      (∀ i : Fin m, p.1 i = w i.castSucc) ∧ p.2 = w (Fin.last m))
    (hw : fn ((fun i : Fin m => w i.castSucc), w (Fin.last m)) = true) :
    ∀ o ∈ (fullRecover fn w).support, o.1 = w := by
  intro o ho
  simp only [fullRecover, PMF.mem_support_bind_iff] at ho
  obtain ⟨s, hs, ho2⟩ := ho
  rw [PMF.mem_support_pure_iff] at ho2
  rw [ho2]
  have hpre : (fun i : Fin m => s.1 i.castSucc) = (fun i : Fin m => w i.castSucc) := by
    funext i
    exact trialRecover_correct (m + 1) (flagAt 0) w s hs i.castSucc (by
      have hi : (i : ℕ) < m := i.isLt
      simp only [Fin.val_castSucc]
      omega)
  by_cases hff : fn ((fun i : Fin m => s.1 i.castSucc), false) = true
  · refine snoc_eq_of_prefix (fun i : Fin m => s.1 i.castSucc) _ (fun i => congrFun hpre i) ?_
    have htr : (fn ((fun i : Fin m => s.1 i.castSucc), false) = true) = True :=
      propext ⟨fun _ => trivial, fun _ => hff⟩
    simp only [htr, ite_true]
    exact (honehot _ hff).2
  · refine snoc_eq_of_prefix (fun i : Fin m => s.1 i.castSucc) _ (fun i => congrFun hpre i) ?_
    have hfa : (fn ((fun i : Fin m => s.1 i.castSucc), false) = true) = False :=
      propext ⟨fun h => hff h, fun h => h.elim⟩
    have hwf : fn ((fun i : Fin m => w i.castSucc), false) ≠ true := by
      rw [← hpre]
      exact hff
    simp only [hfa, ite_false]
    by_cases hwl : w (Fin.last m) = true
    · exact hwl.symm
    · exfalso
      have hwf2 : w (Fin.last m) = false := by
        cases hh : w (Fin.last m) with
        | false => rfl
        | true => exact absurd hh hwl
      rw [hwf2] at hw
      exact absurd hw hwf

/-- The expected-query budget of the full recovery process: at most `4 * m + 2`
queries in expectation for a hidden word of length `m + 1` — `m` trial stages, each
of expected cost at most `4` by geometric amplification of the uniform-query quarter
bound, plus the two final evaluations. -/
theorem fullRecover_exp {m : ℕ} (fn : ((Fin m → Bool) × Bool) → Bool)
    (w : Fin (m + 1) → Bool) :
    pexp (fullRecover fn w) (fun s => (s.2 : ℝ≥0∞)) ≤ ((4 * m + 2 : ℕ) : ℝ≥0∞) := by
  have h1 : ∀ s : (Fin (m + 1) → Bool) × ℕ,
      (trialRecover (m + 1) (flagAt 0) w) s * (((s.2 : ℕ) + 2 : ℕ) : ℝ≥0∞) =
        (trialRecover (m + 1) (flagAt 0) w) s * (s.2 : ℝ≥0∞) +
          (trialRecover (m + 1) (flagAt 0) w) s * ((2 : ℕ) : ℝ≥0∞) := by
    intro s
    rw [Nat.cast_add, Nat.cast_two]
    ring
  have hstep : pexp (fullRecover fn w) (fun s => (s.2 : ℝ≥0∞)) =
      pexp (trialRecover (m + 1) (flagAt 0) w) (fun s => (s.2 : ℝ≥0∞)) +
        ((2 : ℕ) : ℝ≥0∞) := by
    rw [fullRecover, pexp_bind]
    simp only [pexp_pure]
    simp only [h1]
    rw [ENNReal.tsum_add]
    have hleft : (∑' s : (Fin (m + 1) → Bool) × ℕ,
          (trialRecover (m + 1) (flagAt 0) w) s * ((2 : ℕ) : ℝ≥0∞)) =
        ((2 : ℕ) : ℝ≥0∞) := by
      rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    have hright : (∑' s : (Fin (m + 1) → Bool) × ℕ,
          (trialRecover (m + 1) (flagAt 0) w) s * (s.2 : ℝ≥0∞)) =
        pexp (trialRecover (m + 1) (flagAt 0) w) (fun s => (s.2 : ℝ≥0∞)) := by
      simp only [pexp, mul_comm]
    rw [hleft, hright]
  rw [hstep]
  calc pexp (trialRecover (m + 1) (flagAt 0) w) (fun s => (s.2 : ℝ≥0∞)) +
        ((2 : ℕ) : ℝ≥0∞)
      ≤ ((4 * ((m + 1) - 1) : ℕ) : ℝ≥0∞) + ((2 : ℕ) : ℝ≥0∞) :=
          add_le_add (trialRecover_exp (m + 1) (flagAt 0) w) (le_refl _)
    _ = ((4 * m + 2 : ℕ) : ℝ≥0∞) := by
          have hnat : 4 * ((m + 1) - 1) + 2 = 4 * m + 2 := by omega
          rw [← Nat.cast_add]
          exact_mod_cast hnat

end Qatlib.Papers.DecisionTrees97.AdaptiveRecovery
