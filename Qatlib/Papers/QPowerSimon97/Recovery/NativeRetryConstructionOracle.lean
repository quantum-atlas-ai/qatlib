/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
import Qatlib.Papers.QPowerSimon97.Recovery.NativeRetryConstructionDefs
import Qatlib.Concepts.HspRecovery.Distinguisher.BoundedErrorNearPeriodSimo
import Qatlib.Papers.QPowerSimon97.Recovery.NativeRetryConstructionAmplification

/-!
# Oracle transcript bounds for Simon's separation

This module analyzes classical query transcripts for Simon's oracle construction [Simon1997]. It
bounds period hits by a birthday estimate and compares the laws of two-to-one functions and
uniformly random permutations on transcripts that avoid the hidden period.

The comparison culminates in `simon_good_observation_mass` and
`simon_twoToOne_true_le_reference`, which control a query tree's acceptance probability through
its period-hit probability.

## Main statements

* `queries_period_hit`: Among the first `q` positions of a random input list, the probability
  that a distinct pair sums to an independently uniform mask is at most `q * q` times the
  reciprocal of the domain size.
* `simonTwoToOneDist_restrict_eq`: On an injective input family avoiding pairs whose sum is a
  nonzero mask, the Simon oracle law and uniform permutation law have identical restrictions.
* `simon_twoToOne_true_le_reference`: For positive width and nonzero mask, a tree's true-output
  probability under the Simon law is bounded by its true-output and period-hit probabilities
  under the permutation law.

## References

* [Simon, 1997][Simon1997]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Papers.QPowerSimon97.Recovery.SimonQueryTree
open Qatlib.Concepts.PauliClifford.ExactRank
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw
open Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelian
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.HspRecovery.Distinguisher

set_option autoImplicit false

open Qatlib.Concepts.AbelianDecoders.SimonDecoding Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelian Qatlib.Concepts.HspRecovery.Distinguisher
open Qatlib.Foundations.StandardDefs.WindowSim
open Qatlib.Concepts.QtmSimulation.Phi3Compilation
open Qatlib.Concepts.UniformBqp.Phi3Compile
open Qatlib.Concepts.CircuitImpl.Phi3Universal
open Matrix
open scoped Classical BigOperators ENNReal

namespace Qatlib.Papers.QPowerSimon97.Recovery
noncomputable section

/-- For positive input width, there exists a function satisfying `SimonStrictTwoToOne s` for
every mask `s`. -/
lemma simonStrictTwoToOne_nonempty {n : ℕ} (hn : 1 ≤ n) (s : BooleanVec n) :
    Nonempty {f : BooleanVec n → BooleanVec n // SimonStrictTwoToOne s f} := by
  classical
  let i0 : Fin n := ⟨0, by omega⟩
  let t : BooleanVec n := if s = 0 then Pi.single i0 (1 : ZMod 2) else s
  have ht : t ≠ 0 := by
    by_cases hs : s = 0
    · intro h0
      have := congr_fun h0 i0
      simp [t, hs, Pi.single_eq_same] at this
    · intro h0
      simp [t, hs] at h0
  have hbit : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by
    intro a
    fin_cases a
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hex : ∃ i, t i = 1 := by
    by_contra hnone
    simp only [not_exists] at hnone
    apply ht
    ext j
    rcases hbit (t j) with h0 | h1
    · exact h0
    · exact (hnone j h1).elim
  have hdouble : t + t = 0 := by
    ext j
    rcases hbit (t j) with h0 | h1
    · simp [Pi.add_apply, h0]
    · simp [Pi.add_apply, h1]; decide
  let i : Fin n := Classical.choose hex
  have hi : t i = 1 := Classical.choose_spec hex
  let f : BooleanVec n → BooleanVec n := fun x => if x i = 0 then x else x + t
  have hperiod : ∀ x, f x = f (x + s) := by
    intro x
    by_cases hs : s = 0
    · simp [hs]
    · have hts : t = s := by simp [t, hs]
      rw [← hts]
      by_cases hx : x i = 0
      · have hxt : (x + t) i = 1 := by simp [Pi.add_apply, hx, hi]
        simp [f, hx, hxt, hdouble, add_assoc]
      · have hx1 : x i = 1 := by
          rcases hbit (x i) with h0 | h1
          · exact (hx h0).elim
          · exact h1
        have hxt : (x + t) i = 0 := by
          simp [Pi.add_apply, hx1, hi]
          decide
        simp [f, hx, hxt]
  refine ⟨⟨f, hperiod, ?_⟩⟩
  intro y
  by_cases hy : y i = 0
  · left
    have hpair : {x : BooleanVec n | f x = y} = {y, y + t} := by
      ext x
      constructor
      · intro hx
        by_cases hxi : x i = 0
        · have hxeq : x = y := by simpa [f, hxi] using! hx
          simp [hxeq]
        · have hxeq : x + t = y := by simpa [f, hxi] using! hx
          have : x = y + t := by
            calc
              x = x + (t + t) := by simp [hdouble]
              _ = (x + t) + t := by simp [add_assoc]
              _ = y + t := by rw [hxeq]
          simp [this]
      · intro hx
        rcases hx with rfl | rfl
        · simp [f, hy]
        · have hyt : (y + t) i = 1 := by simp [hy, hi]
          simp [f, hyt, hdouble, add_assoc]
    have hne : y ≠ y + t := by
      intro h
      have := congr_fun h i
      simp [hy, hi] at this
    rw [hpair]
    change ({y, y + t} : Set (BooleanVec n)).ncard = 2
    exact Set.ncard_pair hne
  · right
    have hempty : IsEmpty {x : BooleanVec n | f x = y} := by
      refine ⟨?_⟩
      intro x
      have hfi : (f x.1) i = 0 := by
        by_cases hx : x.1 i = 0
        · simp [f, hx]
        · have hx1 : x.1 i = 1 := by
            rcases hbit (x.1 i) with h0 | h1
            · exact (hx h0).elim
            · exact h1
          simp [f, hx1, hi]
          decide
      exact hy ((hfi.symm.trans (congr_fun x.property i)).symm)
    exact Nat.card_eq_zero.mpr (Or.inl hempty)
end
end Qatlib.Papers.QPowerSimon97.Recovery
namespace Qatlib.Papers.QPowerSimon97.Recovery.SimonQueryTree
variable {n : ℕ}
noncomputable section

/-- The list of inputs queried along the execution path of a Simon query tree with oracle `f`. -/
def asked (f : BooleanVec n → BooleanVec n) : SimonQueryTree n → List (BooleanVec n)
  | .halt _ => []
  | .ask x next => x :: asked f (next (f x))
end
noncomputable section

/-- The number of inputs queried on any execution path is at most the tree's maximum query
count. -/
lemma asked_length_le_maxQueries (f : BooleanVec n → BooleanVec n) :
    ∀ τ : SimonQueryTree n, (asked f τ).length ≤ τ.maxQueries
  | .halt _ => by simp [asked, maxQueries]
  | .ask x next => by
      have hsub := asked_length_le_maxQueries f (next (f x))
      have hle : (next (f x)).maxQueries ≤
          Finset.sup (Finset.univ : Finset (BooleanVec n)) fun y => (next y).maxQueries :=
        Finset.le_sup (f := fun y => (next y).maxQueries) (Finset.mem_univ (f x))
      simp only [asked, maxQueries, List.length_cons]
      omega
end
noncomputable section

/-- The event that two distinct queried inputs have the same oracle value. -/
def valueCollision (f : BooleanVec n → BooleanVec n) (τ : SimonQueryTree n) : Prop :=
  ∃ a ∈ asked f τ, ∃ b ∈ asked f τ, a ≠ b ∧ f a = f b
end
noncomputable section

/-- An injective oracle produces no value collision along any query-tree execution. -/
lemma not_valueCollision_of_injective {f : BooleanVec n → BooleanVec n}
    (hf : Function.Injective f) (τ : SimonQueryTree n) : ¬ valueCollision f τ := by
  intro ⟨a, _, b, _, hne, heq⟩
  exact hne (hf heq)
end
end Qatlib.Papers.QPowerSimon97.Recovery.SimonQueryTree
namespace Qatlib.Papers.QPowerSimon97.Recovery.NativeRetryConstruction
variable {n : ℕ}
noncomputable section

/-- The oracle law obtained by drawing a uniform mask and then drawing from its Simon two-to-one
distribution. -/
noncomputable def twoToOneLaw (n : ℕ) : PMF (BooleanVec n → BooleanVec n) :=
  PMF.bind (PMF.uniformOfFintype' (BooleanVec n)) simonTwoToOneDist
end
noncomputable section

/-- The probability of an event under a bound distribution equals the expected conditional event
probability. -/
lemma event_bind {α β : Type*} (p : PMF α) (q : α → PMF β) (E : β → Prop) :
    event (p.bind q) E = expectation p fun a => event (q a) E := by
  unfold event
  rw [expectation_bind]
end
noncomputable section

/-- For positive width, every function with nonzero mass under `simonTwoToOneDist s` satisfies
`SimonStrictTwoToOne s`. -/
lemma simonTwoToOneDist_of_pos {n : ℕ} (hn : 1 ≤ n) (s : BooleanVec n)
    {f : BooleanVec n → BooleanVec n} (hpos : simonTwoToOneDist s f ≠ 0) :
    SimonStrictTwoToOne s f := by
  classical
  have hne : Nonempty {g : BooleanVec n → BooleanVec n // SimonStrictTwoToOne s g} :=
    simonStrictTwoToOne_nonempty hn s
  have happly := PMF.map_apply
    (fun g : {g : BooleanVec n → BooleanVec n // SimonStrictTwoToOne s g} =>
      (g : BooleanVec n → BooleanVec n))
    (@PMF.uniformOfFintype' {g : BooleanVec n → BooleanVec n // SimonStrictTwoToOne s g}
      (Fintype.ofFinite _) hne) f
  have hlink : simonTwoToOneDist s f =
      (PMF.map
        (fun g : {g : BooleanVec n → BooleanVec n // SimonStrictTwoToOne s g} =>
          (g : BooleanVec n → BooleanVec n))
        (@PMF.uniformOfFintype' _ (Fintype.ofFinite _) hne)) f := by
    unfold simonTwoToOneDist
    rw [dif_pos hne]
    simp [PMF.map, PMF.bind_apply, PMF.pure_apply, Function.comp_def,
      PMF.monad_map_eq_map, PMF.uniformOfFintype'_apply]
  rw [hlink, happly, ne_eq, ENNReal.tsum_eq_zero] at hpos
  simp only [not_forall] at hpos
  obtain ⟨u, hu⟩ := hpos
  by_cases heq : f = (u : BooleanVec n → BooleanVec n)
  · rw [heq]
    exact u.property
  · rw [if_neg heq] at hu
    exact absurd rfl hu
end
noncomputable section

/-- Every element of `ZMod 2` is zero or one. -/
lemma zmod2_bit (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl
end
noncomputable section

/-- For a nonzero strict Simon mask, the sum of two distinct inputs with equal outputs is the
mask. -/
lemma strict_collision_period {n : ℕ} {s x x' : BooleanVec n}
    {f : BooleanVec n → BooleanVec n} (hf : SimonStrictTwoToOne s f)
    (hs : s ≠ 0) (hneq : x ≠ x') (heq : f x = f x') : s = x + x' := by
  by_contra hsx
  have add_self (a : BooleanVec n) : a + a = 0 := by
    ext i
    rcases zmod2_bit (a i) with h0 | h1
    · simp [Pi.add_apply, h0]
    · simp [Pi.add_apply, h1]; decide
  have hxs : x ≠ x + s := by
    intro h
    apply hs
    have : x + 0 = x + s := by simpa [add_zero] using! h
    exact add_left_cancel this.symm
  have hx's : x' ≠ x + s := by
    intro h
    apply hsx
    calc
      s = (x + x) + s := by rw [add_self x, zero_add]
      _ = x + (x + s) := by rw [add_assoc]
      _ = x + x' := by rw [← h]
  classical
  let S : Set (BooleanVec n) := {z | f z = f x}
  let T : Finset (BooleanVec n) := {x, x + s, x'}
  have hxmem : x ∉ ({x + s, x'} : Finset (BooleanVec n)) := by simp [hxs, hneq]
  have hsmem : x + s ∉ ({x'} : Finset (BooleanVec n)) := by
    intro hz
    simp only [Finset.mem_singleton] at hz
    exact hx's hz.symm
  have hcardT : T.card = 3 := by
    simp [T, Finset.card_insert_of_notMem, hxmem, hsmem]
  have hsub : T ⊆ S.toFinset := by
    intro z hz
    simp [T] at hz
    rw [Set.mem_toFinset]
    rcases hz with rfl | rfl | rfl
    · simp [S]
    · simpa [S] using! (hf.1 x).symm
    · rw [Set.mem_setOf]
      exact heq.symm
  have hthree : 3 ≤ Nat.card S := by
    rw [Nat.card_eq_fintype_card, ← Set.toFinset_card S]
    exact le_trans (by simp [hcardT]) (Finset.card_le_card hsub)
  have hcard : Nat.card S = 2 ∨ Nat.card S = 0 := hf.2 (f x)
  rcases hcard with h2 | h0
  · omega
  · omega
end
noncomputable section

/-- Under `twoToOneLaw n` at positive width, the collision probability for two fixed distinct
inputs is at most the reciprocal of `2 ^ (n - 1)`. -/
lemma twoToOneLaw_pair_le {n : ℕ} (hn : 1 ≤ n) {x x' : BooleanVec n} (hneq : x ≠ x') :
    event (twoToOneLaw n) (fun f => f x = f x') ≤ (2 ^ (n - 1) : ℝ≥0∞)⁻¹ := by
  classical
  rw [show twoToOneLaw n = PMF.bind (PMF.uniformOfFintype' (BooleanVec n)) simonTwoToOneDist from rfl,
    event_bind]
  unfold expectation
  rw [tsum_fintype]
  simp only [PMF.uniformOfFintype'_apply]
  have hcard : Fintype.card (BooleanVec n) = 2 ^ n := by
    simp [BooleanVec, ZMod.card, Fintype.card_fin]
  have hshift : x + x' ≠ 0 := by
    intro h
    apply hneq
    ext i
    have hi := congr_fun h i
    rw [Pi.add_apply] at hi
    rcases zmod2_bit (x i) with hx0 | hx1 <;> rcases zmod2_bit (x' i) with hx'0 | hx'1
    · simp [hx0, hx'0]
    · simp [hx0, hx'1] at hi
    · simp [hx1, hx'0] at hi
    · simp [hx1, hx'1]
  let bad : Finset (BooleanVec n) := {0, x + x'}
  have hdisj : (0 : BooleanVec n) ≠ x + x' := hshift.symm
  have houtside : ∀ s, s ∉ bad →
      event (simonTwoToOneDist s) (fun f => f x = f x') = 0 := by
    intro s hs
    unfold event expectation
    refine (tsum_congr fun f => ?_).trans tsum_zero
    by_cases hpos : simonTwoToOneDist s f = 0
    · simp [hpos]
    · have hf := simonTwoToOneDist_of_pos hn s hpos
      have hs0 : s ≠ 0 := by
        intro h0
        exact hs (by simp [bad, h0])
      have hsx : s ≠ x + x' := by
        intro hx
        exact hs (by simp [bad, hx])
      beta_reduce
      by_cases heq : f x = f x'
      · exact (hsx (strict_collision_period hf hs0 hneq heq)).elim
      · rw [if_neg heq, mul_zero]
  have hsum : ∑ s : BooleanVec n,
      event (simonTwoToOneDist s) (fun f => f x = f x') ≤ 2 := by
    have hsubset : bad ⊆ Finset.univ := Finset.subset_univ bad
    calc
      ∑ s, event (simonTwoToOneDist s) (fun f => f x = f x')
          = ∑ s ∈ bad, event (simonTwoToOneDist s) (fun f => f x = f x') := by
            symm
            refine Finset.sum_subset hsubset ?_
            intro s _ hs
            exact houtside s hs
      _ ≤ ∑ s ∈ bad, (1 : ℝ≥0∞) :=
            Finset.sum_le_sum fun s _ => event_le_one _ _
      _ = bad.card := by simp
      _ = 2 := by simp [bad, Finset.card_pair hdisj]
  rw [← Finset.mul_sum, hcard]
  refine le_trans (mul_le_mul_of_nonneg_left hsum bot_le) ?_
  have hnat : 2 ^ n = 2 ^ (n - 1) * 2 := by
    have hn0 : n = (n - 1) + 1 := by omega
    conv_lhs => rw [hn0]
    rw [pow_succ]
  rw [hnat, Nat.cast_mul,
    ENNReal.mul_inv (Or.inl (by simp : ((2 ^ (n - 1) : ℕ) : ℝ≥0∞) ≠ 0))
      (Or.inr (by simp : ((2 : ℕ) : ℝ≥0∞) ≠ 0))]
  calc
    (((2 ^ (n - 1) : ℕ) : ℝ≥0∞)⁻¹ * ((2 : ℕ) : ℝ≥0∞)⁻¹) * (2 : ℝ≥0∞)
        = ((2 ^ (n - 1) : ℕ) : ℝ≥0∞)⁻¹ * (((2 : ℕ) : ℝ≥0∞)⁻¹ * 2) := by rw [mul_assoc]
    _ = ((2 ^ (n - 1) : ℕ) : ℝ≥0∞)⁻¹ * 1 := by
          have htwo : (2 : ℝ≥0∞) = ((2 : ℕ) : ℝ≥0∞) := rfl
          rw [← htwo]
          rw [ENNReal.inv_mul_cancel (by simp) (by simp)]
    _ = ((2 ^ (n - 1) : ℕ) : ℝ≥0∞)⁻¹ := by rw [mul_one]
  rw [Nat.cast_pow]
  exact le_rfl
end
noncomputable section

/-- There are exactly `2 ^ n` Boolean vectors of length `n`. -/
lemma booleanVec_card (n : ℕ) : Fintype.card (BooleanVec n) = 2 ^ n := by
  simp [BooleanVec, ZMod.card, Fintype.card_fin]
end
noncomputable section

/-- An independently uniform mask equals the sum of a random distinct input pair with
probability at most the reciprocal of the number of Boolean vectors. -/
lemma uniform_period_hit {n : ℕ} (μ : PMF (BooleanVec n × BooleanVec n)) :
    event (μ.bind fun ab => (PMF.uniformOfFintype' (BooleanVec n)).map fun s => (ab, s))
      (fun p => p.1.1 ≠ p.1.2 ∧ p.1.1 + p.1.2 = p.2) ≤
      (Fintype.card (BooleanVec n) : ℝ≥0∞)⁻¹ := by
  classical
  rw [event_bind]
  have hinner : ∀ ab : BooleanVec n × BooleanVec n,
      event ((PMF.uniformOfFintype' (BooleanVec n)).map fun s => (ab, s))
        (fun p => p.1.1 ≠ p.1.2 ∧ p.1.1 + p.1.2 = p.2) ≤
        (Fintype.card (BooleanVec n) : ℝ≥0∞)⁻¹ := by
    intro ab
    rw [event_map]
    by_cases hne : ab.1 ≠ ab.2
    · have hpt : ∀ s, (ab.1 ≠ ab.2 ∧ ab.1 + ab.2 = s) ↔ s = ab.1 + ab.2 := by
        intro s
        constructor
        · rintro ⟨_, hs⟩
          exact hs.symm
        · intro hs
          exact ⟨hne, hs.symm⟩
      rw [event_congr hpt]
      unfold event expectation
      rw [tsum_eq_single (ab.1 + ab.2)]
      · simp [PMF.uniformOfFintype'_apply]
      · intro s hs
        beta_reduce
        rw [if_neg hs, mul_zero]
    · have hfalse : ∀ s, ¬ (ab.1 ≠ ab.2 ∧ ab.1 + ab.2 = s) := by
        intro s hs
        exact hne hs.1
      rw [event_zero _ _ hfalse]
      exact bot_le
  unfold expectation
  refine le_trans (ENNReal.tsum_le_tsum fun ab =>
    mul_le_mul_of_nonneg_left (hinner ab) bot_le) ?_
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
end
noncomputable section

/-- Among the first `q` positions of a random input list, the probability that a distinct pair
sums to an independently uniform mask is at most `q * q` times the reciprocal of the domain
size. -/
lemma queries_period_hit {n q : ℕ} (μ : PMF (List (BooleanVec n))) :
    event (μ.bind fun l => (PMF.uniformOfFintype' (BooleanVec n)).map fun s => (l, s))
      (fun p => ∃ i j : Fin q,
        ∃ (hi : i.1 < p.1.length) (hj : j.1 < p.1.length),
          p.1.get ⟨i.1, hi⟩ ≠ p.1.get ⟨j.1, hj⟩ ∧
            p.1.get ⟨i.1, hi⟩ + p.1.get ⟨j.1, hj⟩ = p.2) ≤
      (q * q : ℕ) * (Fintype.card (BooleanVec n) : ℝ≥0∞)⁻¹ := by
  classical
  let ν := μ.bind fun l => (PMF.uniformOfFintype' (BooleanVec n)).map fun s => (l, s)
  let E : Fin q × Fin q → List (BooleanVec n) × BooleanVec n → Prop := fun ij p =>
    ∃ (hi : ij.1.1 < p.1.length) (hj : ij.2.1 < p.1.length),
      p.1.get ⟨ij.1.1, hi⟩ ≠ p.1.get ⟨ij.2.1, hj⟩ ∧
        p.1.get ⟨ij.1.1, hi⟩ + p.1.get ⟨ij.2.1, hj⟩ = p.2
  have hcover : ∀ p,
      (∃ i j : Fin q, ∃ (hi : i.1 < p.1.length) (hj : j.1 < p.1.length),
        p.1.get ⟨i.1, hi⟩ ≠ p.1.get ⟨j.1, hj⟩ ∧
          p.1.get ⟨i.1, hi⟩ + p.1.get ⟨j.1, hj⟩ = p.2) ↔ ∃ ij, E ij p := by
    intro p
    constructor
    · rintro ⟨i, j, h⟩
      exact ⟨(i, j), h⟩
    · rintro ⟨ij, h⟩
      exact ⟨ij.1, ij.2, h⟩
  rw [show μ.bind (fun l => (PMF.uniformOfFintype' (BooleanVec n)).map fun s => (l, s)) = ν from rfl,
    event_congr hcover]
  have hsum : event ν (fun p => ∃ ij, E ij p) ≤
      ∑ ij : Fin q × Fin q, event ν (E ij) := by
    classical
    unfold event expectation
    let mid : (List (BooleanVec n) × BooleanVec n) → ℝ≥0∞ := fun p =>
      ν p * ∑ ij : Fin q × Fin q, if E ij p then 1 else 0
    apply le_trans (b := ∑' p, mid p)
    · apply ENNReal.tsum_le_tsum
      intro p
      apply mul_le_mul_of_nonneg_left
      · beta_reduce
        by_cases hex : ∃ ij : Fin q × Fin q, E ij p
        · rw [if_pos hex]
          obtain ⟨ij, hij⟩ := hex
          refine le_trans ?_ (Finset.single_le_sum
            (fun _ _ => by split_ifs <;> exact bot_le) (Finset.mem_univ ij))
          simp [hij]
        · rw [if_neg hex]
          exact bot_le
      · exact bot_le
    · have hswap := expectation_sum ν Finset.univ
        (fun ij p => if E ij p then (1 : ℝ≥0∞) else 0)
      simpa [mid, expectation, event] using! hswap.le
  apply le_trans hsum
  apply le_trans
  · apply Finset.sum_le_sum
    intro ij _
    let push : List (BooleanVec n) → BooleanVec n × BooleanVec n := fun l =>
      if h : ij.1.1 < l.length ∧ ij.2.1 < l.length then
        (l.get ⟨ij.1.1, h.1⟩, l.get ⟨ij.2.1, h.2⟩)
      else
        (0, 0)
    have hagree : ∀ l s, E ij (l, s) ↔
        (push l).1 ≠ (push l).2 ∧ (push l).1 + (push l).2 = s := by
      intro l s
      by_cases h : ij.1.1 < l.length ∧ ij.2.1 < l.length
      · simp [E, push, h]
      · constructor
        · intro hex
          rcases hex with ⟨hi, hj, _⟩
          exact (h ⟨hi, hj⟩).elim
        · intro hpair
          simp [push, h] at hpair
    have heq : event ν (E ij) =
        event ((μ.map push).bind fun ab =>
            (PMF.uniformOfFintype' (BooleanVec n)).map fun s => (ab, s))
          (fun p => p.1.1 ≠ p.1.2 ∧ p.1.1 + p.1.2 = p.2) := by
      rw [event_bind, event_bind]
      have hpush : expectation (μ.map push) (fun ab =>
          event ((PMF.uniformOfFintype' (BooleanVec n)).map fun s => (ab, s))
            (fun p => p.1.1 ≠ p.1.2 ∧ p.1.1 + p.1.2 = p.2)) =
          expectation μ (fun l =>
            event ((PMF.uniformOfFintype' (BooleanVec n)).map fun s => (push l, s))
              (fun p => p.1.1 ≠ p.1.2 ∧ p.1.1 + p.1.2 = p.2)) := by
        exact expectation_map μ push _
      rw [hpush]
      refine expectation_congr fun l => ?_
      rw [event_map, event_map]
      exact event_congr fun s => hagree l s
    exact heq.trans_le (uniform_period_hit (μ.map push))
  · rw [Finset.sum_const, Finset.card_univ]
    simp [Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
end
noncomputable section

/-- If `q ≤ 2 ^ (n / 4)`, then the birthday ratio `q² / 2ⁿ` is at most `2 ^ (-(n : ℝ) / 2)`. -/
lemma birthday_query_le (n q : ℕ) (hq : q ≤ 2 ^ (n / 4)) :
    ((q * q : ℕ) : ℝ) / (2 ^ n : ℝ) ≤ (2 : ℝ) ^ (-(n : ℝ) / 2) := by
  have hdiv : 2 * (n / 4) ≤ n / 2 := by omega
  have hexp : ((2 * (n / 4) : ℕ) : ℝ) ≤ (n : ℝ) / 2 := by
    have h1 : ((2 * (n / 4) : ℕ) : ℝ) ≤ ((n / 2 : ℕ) : ℝ) := by exact_mod_cast hdiv
    have h2 : ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) / 2 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      exact_mod_cast Nat.div_mul_le_self n 2
    exact le_trans h1 h2
  have hqR : (q : ℝ) ≤ Nat.cast (2 ^ (n / 4)) := by exact_mod_cast hq
  have hbase : Nat.cast (2 ^ (n / 4)) = (2 : ℝ) ^ (n / 4) := by
    simp [Nat.cast_pow]
  calc
    ((q * q : ℕ) : ℝ) / (2 ^ n : ℝ) = (q : ℝ) ^ 2 / (2 : ℝ) ^ n := by
      conv_lhs =>
        arg 1
        rw [Nat.cast_mul, ← pow_two]
    _ ≤ (Nat.cast (2 ^ (n / 4))) ^ 2 / (2 : ℝ) ^ n := by
      gcongr
    _ = ((2 : ℝ) ^ (n / 4)) ^ 2 / (2 : ℝ) ^ n := by rw [hbase]
    _ = (2 : ℝ) ^ ((n / 4) * 2) / (2 : ℝ) ^ n := by rw [pow_mul]
    _ = (2 : ℝ) ^ (2 * (n / 4)) / (2 : ℝ) ^ n := by rw [mul_comm]
    _ = (2 : ℝ) ^ ((2 * (n / 4) : ℕ) : ℝ) / (2 : ℝ) ^ (n : ℝ) := by
      rw [Real.rpow_natCast, Real.rpow_natCast]
    _ ≤ (2 : ℝ) ^ ((n : ℝ) / 2) / (2 : ℝ) ^ (n : ℝ) := by
      gcongr
      norm_num
    _ = (2 : ℝ) ^ ((n : ℝ) / 2 - n) := by
      rw [← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
    _ = (2 : ℝ) ^ (-(n : ℝ) / 2) := by congr 1; ring
end
end Qatlib.Papers.QPowerSimon97.Recovery.NativeRetryConstruction
namespace Qatlib.Papers.QPowerSimon97.Recovery.SimonQueryTree
variable {n : ℕ}
noncomputable section

/-- Oracles agreeing on all inputs queried along one execution give the same query-tree result. -/
lemma run_eq_of_agree_on_asked (f g : BooleanVec n → BooleanVec n) :
    ∀ τ : SimonQueryTree n,
      (∀ x ∈ asked f τ, f x = g x) → run f τ = run g τ
  | .halt _, _ => rfl
  | .ask x next, h => by
      have hx : f x = g x := h x (by simp [asked])
      have ht : ∀ z ∈ asked f (next (f x)), f z = g z := by
        intro z hz
        exact h z (by simp [asked, hz])
      simp only [run, ← hx]
      rw [run_eq_of_agree_on_asked f g (next (f x)) ht]
end
noncomputable section

/-- Oracles agreeing on the queried inputs give the same list of queried inputs. -/
lemma asked_eq_of_agree_on_asked (f g : BooleanVec n → BooleanVec n) :
    ∀ τ : SimonQueryTree n,
      (∀ x ∈ asked f τ, f x = g x) → asked f τ = asked g τ
  | .halt _, _ => rfl
  | .ask x next, h => by
      have hx : f x = g x := h x (by simp [asked])
      have ht : ∀ z ∈ asked f (next (f x)), f z = g z := by
        intro z hz
        exact h z (by simp [asked, hz])
      simp only [asked, ← hx]
      rw [asked_eq_of_agree_on_asked f g (next (f x)) ht]
end
noncomputable section

/-- The event that two distinct queried inputs sum to the specified mask. -/
def periodHit (s : BooleanVec n) (τ : SimonQueryTree n)
    (f : BooleanVec n → BooleanVec n) : Prop :=
  ∃ a ∈ asked f τ, ∃ b ∈ asked f τ, a ≠ b ∧ a + b = s
end
noncomputable section

/-- For a strict Simon oracle with nonzero mask, a queried value collision is equivalent to a
period hit. -/
lemma valueCollision_iff_periodHit {s : BooleanVec n}
    {f : BooleanVec n → BooleanVec n} (hf : SimonStrictTwoToOne s f)
    (hs : s ≠ 0) (τ : SimonQueryTree n) :
    valueCollision f τ ↔ periodHit s τ f := by
  constructor
  · rintro ⟨a, ha, b, hb, hne, heq⟩
    exact ⟨a, ha, b, hb, hne,
        (Qatlib.Papers.QPowerSimon97.Recovery.NativeRetryConstruction.strict_collision_period hf hs hne heq).symm⟩
  · rintro ⟨a, ha, b, hb, hne, hab⟩
    refine ⟨a, ha, b, hb, hne, ?_⟩
    have haa : a + a = 0 := by
      ext i
      rcases Qatlib.Papers.QPowerSimon97.Recovery.NativeRetryConstruction.zmod2_bit (a i) with h | h
      · simp [Pi.add_apply, h]
      · simp only [Pi.add_apply, Pi.zero_apply, h]
        decide
    have hshift : a + s = b := by rw [← hab, ← add_assoc, haa, zero_add]
    simpa only [hshift] using! hf.1 a
end
noncomputable section

/-- For a tree with at most `q` queries, a period hit is equivalent to a pair of valid list
indices bounded by `q` whose distinct inputs sum to the mask. -/
lemma periodHit_iff_indices {q : ℕ} (s : BooleanVec n) (τ : SimonQueryTree n)
    (f : BooleanVec n → BooleanVec n) (hq : τ.maxQueries ≤ q) :
    periodHit s τ f ↔ ∃ i j : Fin q,
      ∃ (hi : i.1 < (asked f τ).length) (hj : j.1 < (asked f τ).length),
        (asked f τ).get ⟨i.1, hi⟩ ≠ (asked f τ).get ⟨j.1, hj⟩ ∧
          (asked f τ).get ⟨i.1, hi⟩ + (asked f τ).get ⟨j.1, hj⟩ = s := by
  have hlen := (asked_length_le_maxQueries f τ).trans hq
  constructor
  · rintro ⟨a, ha, b, hb, hne, hab⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp ha
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp hb
    refine ⟨⟨i.1, lt_of_lt_of_le i.2 hlen⟩,
      ⟨j.1, lt_of_lt_of_le j.2 hlen⟩, i.2, j.2, ?_⟩
    simpa only [hi, hj] using! And.intro hne hab
  · rintro ⟨i, j, hi, hj, hne, hab⟩
    exact ⟨_, List.get_mem _ _, _, List.get_mem _ _, hne, hab⟩
end
end Qatlib.Papers.QPowerSimon97.Recovery.SimonQueryTree
namespace Qatlib.Papers.QPowerSimon97.Recovery.NativeRetryConstruction
variable {n : ℕ}
noncomputable section

/-- A query tree with at most `q` queries hits an independently uniform mask with probability at
most `q²` divided by the domain size. -/
lemma independent_path_period_hit {n q : ℕ}
    (ρ : PMF (BooleanVec n → BooleanVec n)) (τ : SimonQueryTree n)
    (hq : τ.maxQueries ≤ q) :
    event (ρ.bind fun f => (PMF.uniformOfFintype' (BooleanVec n)).map fun s => (f, s))
      (fun fs => SimonQueryTree.periodHit fs.2 τ fs.1) ≤
        (q * q : ℕ) * (Fintype.card (BooleanVec n) : ℝ≥0∞)⁻¹ := by
  have h := queries_period_hit (q := q) (ρ.map fun f => SimonQueryTree.asked f τ)
  rw [event_bind, expectation_map] at h
  rw [event_bind]
  refine le_trans (le_of_eq ?_) h
  refine expectation_congr fun f => ?_
  rw [event_map, event_map]
  exact event_congr fun s => SimonQueryTree.periodHit_iff_indices s τ f hq
end
noncomputable section

/-- A randomized query tree bounded by `q` hits an independently uniform mask with probability
at most `q²` divided by the domain size. -/
lemma randomized_independent_path_period_hit {n q : ℕ}
    (P : PMF (SimonQueryTree n)) (ρ : PMF (BooleanVec n → BooleanVec n))
    (hq : SimonQueryTree.bounded P q) :
    event (P.bind fun τ => ρ.bind fun f =>
      (PMF.uniformOfFintype' (BooleanVec n)).map fun s => (τ, f, s))
      (fun tfs => SimonQueryTree.periodHit tfs.2.2 tfs.1 tfs.2.1) ≤
        (q * q : ℕ) * (Fintype.card (BooleanVec n) : ℝ≥0∞)⁻¹ := by
  rw [event_bind]
  let c : ℝ≥0∞ := (q * q : ℕ) * (Fintype.card (BooleanVec n) : ℝ≥0∞)⁻¹
  change expectation P _ ≤ c
  rw [← expectation_const P c]
  unfold expectation
  apply ENNReal.tsum_le_tsum
  intro τ
  by_cases hzero : P τ = 0
  · simp [hzero]
  · apply mul_le_mul_of_nonneg_left _ bot_le
    have hτ := hq τ (ENNReal.toReal_pos hzero (P.apply_ne_top τ))
    have h := independent_path_period_hit ρ τ hτ
    beta_reduce
    rw [event_bind] at h ⊢
    refine le_trans (le_of_eq ?_) h
    refine expectation_congr fun f => ?_
    rw [event_map, event_map]
end
noncomputable section

/-- A permutation of a finite nonempty type preserves its uniform probability law. -/
private lemma uniform_map_equiv {α : Type} [Fintype α] [Nonempty α] (e : α ≃ α) :
    (PMF.uniformOfFintype' α).map e = PMF.uniformOfFintype' α := by
  classical
  ext b
  rw [PMF.map_apply]
  rw [tsum_eq_single (e.symm b)]
  · simp only [Equiv.apply_symm_apply, ite_true, PMF.uniformOfFintype'_apply]
  · intro a ha
    exact if_neg fun h => ha (e.injective (h.symm.trans (e.apply_symm_apply b).symm))
end
noncomputable section

/-- Postcomposing a strict Simon oracle with an output permutation preserves its strict mask
condition. -/
lemma strict_postcompose {n : ℕ} {s : BooleanVec n}
    {f : BooleanVec n → BooleanVec n} (hf : SimonStrictTwoToOne s f)
    (π : Equiv.Perm (BooleanVec n)) : SimonStrictTwoToOne s (π ∘ f) := by
  refine ⟨fun x => congrArg π (hf.1 x), fun y => ?_⟩
  have hset : {x : BooleanVec n | (π ∘ f) x = y} =
      {x : BooleanVec n | f x = π.symm y} := by
    ext x
    exact π.apply_eq_iff_eq_symm_apply
  rw [hset]
  exact hf.2 (π.symm y)
end
noncomputable section
/-- The equivalence on strict Simon oracles induced by permuting output labels. -/
private def strictLabelEquiv {n : ℕ} (s : BooleanVec n)
    (π : Equiv.Perm (BooleanVec n)) :
    {f : BooleanVec n → BooleanVec n // SimonStrictTwoToOne s f} ≃
      {f : BooleanVec n → BooleanVec n // SimonStrictTwoToOne s f} where
  toFun f := ⟨π ∘ f.val, strict_postcompose f.property π⟩
  invFun f := ⟨π.symm ∘ f.val, strict_postcompose f.property π.symm⟩
  left_inv f := by
    apply Subtype.ext
    funext x
    exact π.symm_apply_apply (f.val x)
  right_inv f := by
    apply Subtype.ext
    funext x
    exact π.apply_symm_apply (f.val x)
end
noncomputable section

/-- For positive width, permuting output labels preserves `simonTwoToOneDist s`. -/
lemma simonTwoToOneDist_postcompose {n : ℕ} (hn : 1 ≤ n)
    (s : BooleanVec n) (π : Equiv.Perm (BooleanVec n)) :
    (simonTwoToOneDist s).map (fun f => π ∘ f) = simonTwoToOneDist s := by
  classical
  let Ω := {f : BooleanVec n → BooleanVec n // SimonStrictTwoToOne s f}
  letI : Fintype Ω := Fintype.ofFinite Ω
  letI : Nonempty Ω := simonStrictTwoToOne_nonempty hn s
  have h := congrArg (fun p : PMF Ω => p.map (fun g => g.val))
    (uniform_map_equiv (strictLabelEquiv s π))
  simp only [PMF.map_comp] at h
  have hlaw : simonTwoToOneDist s =
      (PMF.uniformOfFintype' Ω).map (fun g => g.val) := by
    unfold simonTwoToOneDist
    rw [dif_pos (simonStrictTwoToOne_nonempty hn s)]
    ext f
    simp [PMF.map, PMF.bind_apply, PMF.pure_apply, Function.comp_def,
      PMF.monad_map_eq_map, ← Nat.card_eq_fintype_card, Ω]
  rw [hlaw, PMF.map_comp]
  exact h
end
noncomputable section

/-- Transporting a probability law through an equivalence preserves each point mass at the
corresponding image. -/
private lemma map_equiv_apply {α : Type} (p : PMF α) (e : α ≃ α) (a : α) :
    (p.map e) (e a) = p a := by
  classical
  rw [PMF.map_apply, tsum_eq_single a]
  · simp
  · intro b hb
    exact if_neg fun h => hb (e.injective h).symm
end
noncomputable section

/-- A probability law on Boolean vectors invariant under every permutation is uniform. -/
private lemma booleanVec_law_uniform {n : ℕ} (p : PMF (BooleanVec n))
    (h : ∀ π : Equiv.Perm (BooleanVec n), p.map π = p) :
    p = PMF.uniformOfFintype' (BooleanVec n) := by
  classical
  have hequal (y : BooleanVec n) : p y = p 0 := by
    have heval := congrArg (fun m : PMF (BooleanVec n) => m y) (h (Equiv.swap 0 y))
    have hmap := map_equiv_apply p (Equiv.swap 0 y) 0
    rw [Equiv.swap_apply_left] at hmap
    exact heval.symm.trans hmap
  have hc0 : (Fintype.card (BooleanVec n) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hcT : (Fintype.card (BooleanVec n) : ℝ≥0∞) ≠ ⊤ := by simp
  have htotal : p 0 * (Fintype.card (BooleanVec n) : ℝ≥0∞) = 1 := by
    have ht := p.tsum_coe
    simpa only [tsum_fintype, hequal, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_comm] using! ht
  have hzero : p 0 = (Fintype.card (BooleanVec n) : ℝ≥0∞)⁻¹ :=
    (ENNReal.mul_left_inj hc0 hcT).mp
      (htotal.trans (ENNReal.inv_mul_cancel hc0 hcT).symm)
  ext y
  rw [hequal, hzero, PMF.uniformOfFintype'_apply]
end
noncomputable section

/-- For positive width, the value of a Simon-distributed oracle at any fixed input is uniform. -/
lemma simonTwoToOneDist_eval_uniform {n : ℕ} (hn : 1 ≤ n)
    (s x : BooleanVec n) :
    (simonTwoToOneDist s).map (fun f => f x) =
      PMF.uniformOfFintype' (BooleanVec n) := by
  apply booleanVec_law_uniform
  intro π
  have h := congrArg (fun p : PMF (BooleanVec n → BooleanVec n) =>
    p.map (fun f => f x)) (simonTwoToOneDist_postcompose hn s π)
  simpa only [PMF.map_comp, Function.comp_def] using! h
end
noncomputable section

/-- The image of a fixed Boolean vector under a uniformly random permutation is uniform. -/
lemma uniform_permutation_eval {n : ℕ} (x : BooleanVec n) :
    (PMF.uniformOfFintype' (Equiv.Perm (BooleanVec n))).map (fun π => π x) =
      PMF.uniformOfFintype' (BooleanVec n) := by
  apply booleanVec_law_uniform
  intro π
  let e : Equiv.Perm (BooleanVec n) ≃ Equiv.Perm (BooleanVec n) :=
    Equiv.mulLeft π
  have h := congrArg (fun p : PMF (Equiv.Perm (BooleanVec n)) =>
    p.map (fun σ => σ x)) (uniform_map_equiv e)
  simpa only [PMF.map_comp, Function.comp_def, e, Equiv.coe_mulLeft,
    Equiv.Perm.mul_apply] using! h
end
end Qatlib.Papers.QPowerSimon97.Recovery.NativeRetryConstruction
namespace Qatlib.Papers.QPowerSimon97.Recovery.SimonQueryTree
variable {n : ℕ}
noncomputable section

/-- A query tree with zero maximum queries has the same result for all oracles. -/
lemma run_eq_of_maxQueries_zero (f g : BooleanVec n → BooleanVec n)
    (τ : SimonQueryTree n) (h : τ.maxQueries = 0) : run f τ = run g τ := by
  cases τ with
  | halt _ => rfl
  | ask x next => simp [maxQueries] at h
end
noncomputable section

/-- Oracle laws with matching single-input value distributions induce the same result law for a
tree using at most one query. -/
lemma one_query_run_law_eq (ρ σ : PMF (BooleanVec n → BooleanVec n))
    (h : ∀ x, ρ.map (fun f => f x) = σ.map (fun f => f x))
    (τ : SimonQueryTree n) (hq : τ.maxQueries ≤ 1) :
    ρ.map (fun f => run f τ) = σ.map (fun f => run f τ) := by
  classical
  cases τ with
  | halt b =>
    change ρ.map (Function.const _ (b, 0)) = σ.map (Function.const _ (b, 0))
    rw [PMF.map_const, PMF.map_const]
  | ask x next =>
    have hzero (y : BooleanVec n) : (next y).maxQueries = 0 := by
      have hle : (next y).maxQueries ≤
          Finset.sup (Finset.univ : Finset (BooleanVec n))
            (fun z => (next z).maxQueries) :=
        Finset.le_sup (f := fun z => (next z).maxQueries) (Finset.mem_univ y)
      simp only [maxQueries] at hq
      omega
    let out : BooleanVec n → Bool × ℕ := fun y =>
      ((run (fun _ => 0) (next y)).1, (run (fun _ => 0) (next y)).2 + 1)
    have hrun : (fun f => run f (.ask x next)) = out ∘ (fun f => f x) := by
      funext f
      simp only [run, Function.comp_apply, out]
      rw [run_eq_of_maxQueries_zero f (fun _ => 0) (next (f x)) (hzero (f x))]
    rw [hrun, ← PMF.map_comp, h x, PMF.map_comp]
end
end Qatlib.Papers.QPowerSimon97.Recovery.SimonQueryTree
namespace Qatlib.Papers.QPowerSimon97.Recovery.NativeRetryConstruction
variable {n : ℕ}
noncomputable section

/-- At positive width, a tree using at most one query has the same result law under a Simon
oracle and a uniformly random permutation. -/
lemma one_query_twoToOne_run_law {n : ℕ} (hn : 1 ≤ n) (s : BooleanVec n)
    (τ : SimonQueryTree n) (hq : τ.maxQueries ≤ 1) :
    (simonTwoToOneDist s).map (fun f => SimonQueryTree.run f τ) =
      (PMF.uniformOfFintype' (Equiv.Perm (BooleanVec n))).map
        (fun (π : Equiv.Perm (BooleanVec n)) => SimonQueryTree.run π τ) := by
  let σ := (PMF.uniformOfFintype' (Equiv.Perm (BooleanVec n))).map
    (fun (π : Equiv.Perm (BooleanVec n)) => (π : BooleanVec n → BooleanVec n))
  have h := SimonQueryTree.one_query_run_law_eq (simonTwoToOneDist s) σ
    (fun x => (simonTwoToOneDist_eval_uniform hn s x).trans (by
      simpa only [σ, PMF.map_comp, Function.comp_def] using!
        (uniform_permutation_eval x).symm)) τ hq
  simpa only [σ, PMF.map_comp, Function.comp_def] using! h
end
noncomputable section

/-- For positive width, prescribing either of two injective output labelings on the same input
list gives equal event probabilities under the Simon oracle law. -/
lemma simonTwoToOneDist_injective_cylinder_eq {n k : ℕ} (hn : 1 ≤ n)
    (s : BooleanVec n) (xs a b : Fin k → BooleanVec n)
    (ha : Function.Injective a) (hb : Function.Injective b) :
    event (simonTwoToOneDist s) (fun f => ∀ i, f (xs i) = a i) =
      event (simonTwoToOneDist s) (fun f => ∀ i, f (xs i) = b i) := by
  classical
  obtain ⟨π, hπ⟩ := Equiv.Perm.exists_extending_pair a b ha hb
  have h := congrArg (fun p : PMF (BooleanVec n → BooleanVec n) =>
    event p (fun f => ∀ i, f (xs i) = b i)) (simonTwoToOneDist_postcompose hn s π)
  beta_reduce at h
  rw [event_map] at h
  refine (event_congr fun f => ?_).trans h
  constructor
  · intro hf i
    change π (f (xs i)) = b i
    rw [hf i, hπ i]
  · intro hf i
    apply π.injective
    exact (hf i).trans (hπ i).symm
end
noncomputable section

/-- For positive width, a Simon-distributed oracle agrees at `x` and `x + s` with probability
one. -/
lemma simonTwoToOneDist_period_pair_mass {n : ℕ} (hn : 1 ≤ n)
    (s x : BooleanVec n) :
    event (simonTwoToOneDist s) (fun f => f x = f (x + s)) = 1 := by
  classical
  calc
    _ = ∑' f, simonTwoToOneDist s f := by
      unfold event expectation
      apply tsum_congr
      intro f
      by_cases hf : simonTwoToOneDist s f = 0
      · simp [hf]
      · beta_reduce
        rw [if_pos ((simonTwoToOneDist_of_pos hn s hf).1 x), mul_one]
    _ = 1 := PMF.tsum_coe _
end
noncomputable section

/-- A uniformly random permutation agrees at `x` and `x + s` with probability zero when `s` is
nonzero. -/
lemma uniform_permutation_period_pair_mass {n : ℕ} {s : BooleanVec n}
    (hs : s ≠ 0) (x : BooleanVec n) :
    event (PMF.uniformOfFintype' (Equiv.Perm (BooleanVec n)))
      (fun π => π x = π (x + s)) = 0 := by
  apply event_zero
  intro π h
  apply hs
  have hx := π.injective h
  have hz : x + 0 = x + s := by simpa only [add_zero] using! hx
  exact (add_left_cancel hz).symm
end
noncomputable section

/-- Two finite probability laws supported on the same nonempty set and constant on that set are
equal. -/
private lemma finite_pmf_eq_of_uniform_on {α : Type} [Fintype α]
    (p q : PMF α) (E : α → Prop) (r : α) (hr : E r)
    (hp0 : ∀ a, ¬ E a → p a = 0) (hq0 : ∀ a, ¬ E a → q a = 0)
    (hp : ∀ a, E a → p a = p r) (hq : ∀ a, E a → q a = q r) : p = q := by
  classical
  let S := Finset.univ.filter E
  have hrS : r ∈ S := by simp [S, hr]
  have hc0 : (S.card : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr ⟨r, hrS⟩
  have hcT : (S.card : ℝ≥0∞) ≠ ⊤ := by simp
  have htotal (m : PMF α) (hm0 : ∀ a, ¬ E a → m a = 0)
      (hm : ∀ a, E a → m a = m r) : m r * (S.card : ℝ≥0∞) = 1 := by
    calc
      _ = ∑ a ∈ S, m r := by simp [nsmul_eq_mul, mul_comm]
      _ = ∑ a, m a := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro a _
        by_cases ha : E a
        · simp [ha, hm a ha]
        · simp [ha, hm0 a ha]
      _ = 1 := by simpa only [tsum_fintype] using! m.tsum_coe
  have heq : p r = q r := (ENNReal.mul_left_inj hc0 hcT).mp
    ((htotal p hp0 hp).trans (htotal q hq0 hq).symm)
  ext a
  by_cases ha : E a
  · rw [hp a ha, hq a ha, heq]
  · rw [hp0 a ha, hq0 a ha]
end
noncomputable section

/-- The mass of a point under a mapped probability law equals the probability of its fiber. -/
private lemma pmf_map_apply_event {α β : Type} (p : PMF α) (F : α → β) (b : β) :
    p.map F b = event p (fun a => F a = b) := by
  classical
  rw [PMF.map_apply]
  unfold event expectation
  apply tsum_congr
  intro a
  by_cases h : F a = b
  · simp [h]
  · simp [h, Ne.symm h]
end
noncomputable section

/-- On an injective input family avoiding pairs whose sum is a nonzero mask, the Simon oracle
law and uniform permutation law have identical restrictions. -/
lemma simonTwoToOneDist_restrict_eq {n : ℕ} (hn : 1 ≤ n)
    (s : BooleanVec n) (hs : s ≠ 0) {ι : Type} [Fintype ι]
    (xs : ι → BooleanVec n) (hxs : Function.Injective xs)
    (havoid : ∀ i j, i ≠ j → xs i + xs j ≠ s) :
    (simonTwoToOneDist s).map (fun f => f ∘ xs) =
      (PMF.uniformOfFintype' (Equiv.Perm (BooleanVec n))).map
        (fun (π : Equiv.Perm (BooleanVec n)) => π ∘ xs) := by
  classical
  let p := (simonTwoToOneDist s).map (fun f => f ∘ xs)
  let q := (PMF.uniformOfFintype' (Equiv.Perm (BooleanVec n))).map
    (fun (π : Equiv.Perm (BooleanVec n)) => π ∘ xs)
  have hp0 (a : ι → BooleanVec n) (ha : ¬ Function.Injective a) : p a = 0 := by
    by_contra h
    obtain ⟨f, hf, hfa⟩ :=
        (PMF.mem_support_map_iff (fun f => f ∘ xs) (simonTwoToOneDist s) a).mp
        ((p.mem_support_iff a).mpr h)
    apply ha
    rw [← hfa]
    intro i j hij
    by_contra hne
    exact havoid i j hne (strict_collision_period
      (simonTwoToOneDist_of_pos hn s hf) hs (fun heq => hne (hxs heq)) hij).symm
  have hq0 (a : ι → BooleanVec n) (ha : ¬ Function.Injective a) : q a = 0 := by
    by_contra h
    obtain ⟨π, _, hπa⟩ :=
        (PMF.mem_support_map_iff (fun (π : Equiv.Perm (BooleanVec n)) => π ∘ xs) (PMF.uniformOfFintype' (Equiv.Perm (BooleanVec n))) a).mp ((q.mem_support_iff a).mpr h)
    exact ha (hπa ▸ π.injective.comp hxs)
  have hp (a : ι → BooleanVec n) (ha : Function.Injective a) : p a = p xs := by
    obtain ⟨π, hπ⟩ := Equiv.Perm.exists_extending_pair a xs ha hxs
    have h := congrArg (fun m : PMF (BooleanVec n → BooleanVec n) =>
      event m (fun f => f ∘ xs = xs)) (simonTwoToOneDist_postcompose hn s π)
    beta_reduce at h
    rw [event_map] at h
    rw [pmf_map_apply_event, pmf_map_apply_event]
    refine (event_congr fun f => ?_).trans h
    constructor
    · intro hf
      funext i
      change π (f (xs i)) = xs i
      exact (congrArg π (congrFun hf i)).trans (hπ i)
    · intro hf
      funext i
      apply π.injective
      exact (congrFun hf i).trans (hπ i).symm
  have hq (a : ι → BooleanVec n) (ha : Function.Injective a) : q a = q xs := by
    obtain ⟨π, hπ⟩ := Equiv.Perm.exists_extending_pair a xs ha hxs
    let e : Equiv.Perm (BooleanVec n) ≃ Equiv.Perm (BooleanVec n) := Equiv.mulLeft π
    have h := congrArg (fun m : PMF (Equiv.Perm (BooleanVec n)) =>
      event m (fun σ => σ ∘ xs = xs)) (uniform_map_equiv e)
    beta_reduce at h
    rw [event_map] at h
    rw [pmf_map_apply_event, pmf_map_apply_event]
    refine (event_congr fun σ => ?_).trans h
    constructor
    · intro hf
      funext i
      change π (σ (xs i)) = xs i
      exact (congrArg π (congrFun hf i)).trans (hπ i)
    · intro hf
      funext i
      apply π.injective
      exact (congrFun hf i).trans (hπ i).symm
  exact finite_pmf_eq_of_uniform_on p q Function.Injective xs hxs hp0 hq0 hp hq
end
noncomputable section

/-- On a finite set avoiding the nonzero mask, agreement with a fixed permutation has the same
probability under the Simon oracle law and the uniform permutation law. -/
lemma simonTwoToOneDist_finset_cylinder_eq {n : ℕ} (hn : 1 ≤ n)
    (s : BooleanVec n) (hs : s ≠ 0) (xs : Finset (BooleanVec n))
    (havoid : ∀ a ∈ xs, ∀ b ∈ xs, a ≠ b → a + b ≠ s)
    (π : Equiv.Perm (BooleanVec n)) :
    event (simonTwoToOneDist s) (fun f => ∀ x ∈ xs, f x = π x) =
      event (PMF.uniformOfFintype' (Equiv.Perm (BooleanVec n)))
        (fun σ => ∀ x ∈ xs, σ x = π x) := by
  classical
  have h := congrArg (fun p : PMF (xs → BooleanVec n) => p (fun x => π x))
    (simonTwoToOneDist_restrict_eq hn s hs (fun x : xs => x.val)
      Subtype.val_injective (fun i j hij => havoid i i.property j j.property
        (fun heq => hij (Subtype.ext heq))))
  beta_reduce at h
  rw [pmf_map_apply_event, pmf_map_apply_event] at h
  have heq (f : BooleanVec n → BooleanVec n) :
      f ∘ (fun x : xs => x.val) = (fun x : xs => π x) ↔
      ∀ x ∈ xs, f x = π x := by
    constructor
    · intro hf x hx
      exact congrFun hf ⟨x, hx⟩
    · intro hf
      funext x
      exact hf x x.property
  exact (event_congr heq).symm.trans (h.trans (event_congr fun σ => heq σ))
end
end Qatlib.Papers.QPowerSimon97.Recovery.NativeRetryConstruction
namespace Qatlib.Papers.QPowerSimon97.Recovery.SimonQueryTree
variable {n : ℕ}
noncomputable section

/-- The list of query inputs and oracle responses along a query-tree execution. -/
def simonTrace (f : BooleanVec n → BooleanVec n) : SimonQueryTree n →
    List (BooleanVec n × BooleanVec n)
  | .halt _ => []
  | .ask x next => (x, f x) :: simonTrace f (next (f x))
end
noncomputable section

/-- Projecting the inputs of a Simon transcript recovers the list of queried inputs. -/
lemma trace_inputs (f : BooleanVec n → BooleanVec n) :
    ∀ τ : SimonQueryTree n, (simonTrace f τ).map Prod.fst = asked f τ
  | .halt _ => rfl
  | .ask x next => by simp only [simonTrace, List.map_cons, asked, trace_inputs]
end
noncomputable section

/-- Two oracles give the same transcript exactly when they agree on all inputs queried along the
first execution. -/
lemma trace_eq_iff_agree (f g : BooleanVec n → BooleanVec n) :
    ∀ τ : SimonQueryTree n,
      simonTrace f τ = simonTrace g τ ↔ ∀ x ∈ asked f τ, f x = g x
  | .halt _ => by simp [simonTrace, asked]
  | .ask x next => by
      constructor
      · intro h
        have hx : f x = g x := congrArg (fun t => t.2) (List.cons.inj h).1
        have ht : simonTrace f (next (f x)) = simonTrace g (next (f x)) := by
          simpa only [simonTrace, ← hx] using! (List.cons.inj h).2
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hx
        · exact (trace_eq_iff_agree f g (next (f x))).mp ht z hz
      · intro h
        have hx : f x = g x := h x (by simp [asked])
        have ht : ∀ z ∈ asked f (next (f x)), f z = g z := by
          intro z hz
          exact h z (by simp [asked, hz])
        simp only [simonTrace, ← hx]
        rw [(trace_eq_iff_agree f g (next (f x))).mpr ht]
end
noncomputable section

/-- Equal query transcripts imply equal query-tree results. -/
lemma run_eq_of_trace_eq (f g : BooleanVec n → BooleanVec n)
    (τ : SimonQueryTree n) (h : simonTrace f τ = simonTrace g τ) : run f τ = run g τ :=
  run_eq_of_agree_on_asked f g τ ((trace_eq_iff_agree f g τ).mp h)
end
noncomputable section

/-- An oracle with no queried value collision agrees on its queried inputs with some
permutation. -/
lemma exists_perm_agree_of_not_valueCollision (f : BooleanVec n → BooleanVec n)
    (τ : SimonQueryTree n) (h : ¬ valueCollision f τ) :
    ∃ π : Equiv.Perm (BooleanVec n), ∀ x ∈ asked f τ, π x = f x := by
  classical
  let xs := (asked f τ).toFinset
  have hinj : Function.Injective (fun x : xs => f x) := by
    intro a b hab
    apply Subtype.ext
    by_contra hne
    exact h ⟨a, List.mem_toFinset.mp a.2, b, List.mem_toFinset.mp b.2, hne, hab⟩
  obtain ⟨π, hπ⟩ := Equiv.Perm.exists_extending_pair
    (fun x : xs => (x : BooleanVec n)) (fun x : xs => f x)
    Subtype.val_injective hinj
  exact ⟨π, fun x hx => hπ ⟨x, List.mem_toFinset.mpr hx⟩⟩
end
noncomputable section

/-- The pair consisting of the query transcript and the final Boolean result with its query
count. -/
def simonObservation (f : BooleanVec n → BooleanVec n) (τ : SimonQueryTree n) :=
  (simonTrace f τ, run f τ)
end
noncomputable section

/-- Two oracles give the same observation exactly when they agree on the inputs queried along
the first execution. -/
lemma observation_eq_iff_agree (f g : BooleanVec n → BooleanVec n)
    (τ : SimonQueryTree n) :
    simonObservation f τ = simonObservation g τ ↔ ∀ x ∈ asked f τ, f x = g x := by
  constructor
  · intro h
    exact (trace_eq_iff_agree f g τ).mp (congrArg Prod.fst h)
  · intro h
    exact Prod.ext ((trace_eq_iff_agree f g τ).mpr h)
      (run_eq_of_agree_on_asked f g τ h)
end
end Qatlib.Papers.QPowerSimon97.Recovery.SimonQueryTree
namespace Qatlib.Papers.QPowerSimon97.Recovery.NativeRetryConstruction
variable {n : ℕ}
noncomputable section

/-- If two laws agree pointwise outside a bad event, any event under the first law is bounded by
its probability under the second plus the second law's bad-event probability. -/
private lemma event_le_of_agree_off_bad {α : Type} (p q : PMF α)
    (B E : α → Prop) (h : ∀ x, ¬ B x → p x = q x) :
    event p E ≤ event q E + event q B := by
  classical
  have good (F : α → Prop) :
      event p (fun x => F x ∧ ¬B x) = event q (fun x => F x ∧ ¬B x) := by
    unfold event expectation
    apply tsum_congr
    intro x
    by_cases hx : B x
    · simp [hx]
    · rw [h x hx]
  have hgood := good (fun _ => True)
  simp only [true_and] at hgood
  have hbad : event p B = event q B := by
    apply (ENNReal.add_left_inj (ne_top_of_le_ne_top (by simp) (event_le_one q (fun x => ¬ B x)))).mp
    have hp := event_partition p B
    rw [hgood] at hp
    exact hp.trans (event_partition q B).symm
  calc
    event p E ≤ event p (fun x => E x ∧ ¬B x) + event p B := by
      unfold event
      rw [← expectation_add]
      apply expectation_le_of_forall
      intro x
      by_cases hx : E x <;> by_cases hb : B x <;> simp [hx, hb]
    _ = event q (fun x => E x ∧ ¬B x) + event q B := by rw [good, hbad]
    _ ≤ event q E + event q B := by
      gcongr
      apply expectation_le_of_forall
      intro x
      by_cases hx : E x <;> by_cases hb : B x <;> simp [hx, hb]
end
noncomputable section

/-- The predicate that an observation contains two distinct query inputs summing to the
specified mask. -/
def simonObservationBad {n : ℕ} (s : BooleanVec n)
    (t : List (BooleanVec n × BooleanVec n) × (Bool × ℕ)) : Prop :=
  ∃ a ∈ t.1.map Prod.fst, ∃ b ∈ t.1.map Prod.fst, a ≠ b ∧ a + b = s
end
noncomputable section

/-- An observation is bad exactly when its execution hits the specified period. -/
lemma simonObservationBad_observation {n : ℕ} (s : BooleanVec n)
    (f : BooleanVec n → BooleanVec n) (τ : SimonQueryTree n) :
    simonObservationBad s (SimonQueryTree.simonObservation f τ) ↔
      SimonQueryTree.periodHit s τ f := by
  simp only [simonObservationBad, SimonQueryTree.simonObservation, SimonQueryTree.trace_inputs,
    SimonQueryTree.periodHit]
end
noncomputable section

/-- The law on oracle functions induced by a uniformly random permutation of Boolean vectors. -/
def simonPermutationLaw (n : ℕ) : PMF (BooleanVec n → BooleanVec n) :=
  (PMF.uniformOfFintype' (Equiv.Perm (BooleanVec n))).map
    (fun (π : Equiv.Perm (BooleanVec n)) => (π : BooleanVec n → BooleanVec n))
end
noncomputable section

/-- For positive width and nonzero mask, any observation avoiding a period hit has equal mass
under the Simon oracle law and the permutation law. -/
lemma simon_good_observation_mass {n : ℕ} (hn : 1 ≤ n)
    (s : BooleanVec n) (hs : s ≠ 0) (τ : SimonQueryTree n)
    (t : List (BooleanVec n × BooleanVec n) × (Bool × ℕ))
    (ht : ¬ simonObservationBad s t) :
    (simonTwoToOneDist s).map (fun f => SimonQueryTree.simonObservation f τ) t =
      (simonPermutationLaw n).map (fun f => SimonQueryTree.simonObservation f τ) t := by
  classical
  have hrep (π : Equiv.Perm (BooleanVec n))
      (hπ : SimonQueryTree.simonObservation π τ = t) :
      (simonTwoToOneDist s).map (fun f => SimonQueryTree.simonObservation f τ) t =
        (simonPermutationLaw n).map (fun f => SimonQueryTree.simonObservation f τ) t := by
    let xs := (SimonQueryTree.asked π τ).toFinset
    have havoid : ∀ a ∈ xs, ∀ b ∈ xs, a ≠ b → a + b ≠ s := by
      intro a ha b hb hne hab
      apply ht
      rw [← hπ, simonObservationBad_observation]
      exact ⟨a, List.mem_toFinset.mp ha, b, List.mem_toFinset.mp hb, hne, hab⟩
    conv_lhs => rw [pmf_map_apply_event]
    conv_rhs => rw [pmf_map_apply_event]
    have hcyl := simonTwoToOneDist_finset_cylinder_eq hn s hs xs havoid π
    have hfiber (f : BooleanVec n → BooleanVec n) :
        SimonQueryTree.simonObservation f τ = t ↔ ∀ x ∈ xs, f x = π x := by
      rw [← hπ, eq_comm, SimonQueryTree.observation_eq_iff_agree]
      simp only [xs, List.mem_toFinset]
      exact forall_congr' fun x => forall_congr' fun _ => eq_comm
    rw [event_congr hfiber]
    unfold simonPermutationLaw
    conv_rhs => rw [event_map]
    exact hcyl.trans (event_congr (fun (π' : Equiv.Perm (BooleanVec n)) => hfiber π')).symm
  by_cases hex : ∃ π : Equiv.Perm (BooleanVec n), SimonQueryTree.simonObservation π τ = t
  · obtain ⟨π, hπ⟩ := hex
    exact hrep π hπ
  · have hleft : (simonTwoToOneDist s).map (fun f => SimonQueryTree.simonObservation f τ) t = 0 := by
      by_contra hpos
      obtain ⟨f, hf, hft⟩ := (PMF.mem_support_map_iff
        (fun f => SimonQueryTree.simonObservation f τ) (simonTwoToOneDist s) t).mp hpos
      have hstrict := simonTwoToOneDist_of_pos hn s hf
      have hnc : ¬ SimonQueryTree.valueCollision f τ := by
        rw [SimonQueryTree.valueCollision_iff_periodHit hstrict hs]
        intro hbad
        apply ht
        rw [← hft, simonObservationBad_observation]
        exact hbad
      obtain ⟨π, hπ⟩ := SimonQueryTree.exists_perm_agree_of_not_valueCollision f τ hnc
      apply hex
      refine ⟨π, ?_⟩
      refine Eq.trans ?_ hft
      apply (SimonQueryTree.observation_eq_iff_agree π f τ).mpr
      intro x hx
      have hagree : ∀ x ∈ SimonQueryTree.asked f τ, f x = π x :=
        fun x hx => (hπ x hx).symm
      have hpath := SimonQueryTree.asked_eq_of_agree_on_asked f π τ hagree
      exact hπ x (hpath.symm ▸ hx)
    have hright : (simonPermutationLaw n).map (fun f => SimonQueryTree.simonObservation f τ) t = 0 := by
      simp only [simonPermutationLaw, PMF.map_comp]
      by_contra hpos
      obtain ⟨π, _, hπ⟩ := (PMF.mem_support_map_iff
        (fun (π : Equiv.Perm (BooleanVec n)) => SimonQueryTree.simonObservation π τ)
        (PMF.uniformOfFintype' (Equiv.Perm (BooleanVec n))) t).mp hpos
      exact hex ⟨π, hπ⟩
    rw [hleft, hright]
end
noncomputable section

/-- For positive width and nonzero mask, a tree's true-output probability under the Simon law is
bounded by its true-output and period-hit probabilities under the permutation law. -/
lemma simon_twoToOne_true_le_reference {n : ℕ} (hn : 1 ≤ n)
    (s : BooleanVec n) (hs : s ≠ 0) (τ : SimonQueryTree n) :
    event (simonTwoToOneDist s) (fun f => (SimonQueryTree.run f τ).1 = true) ≤
      event (simonPermutationLaw n) (fun f => (SimonQueryTree.run f τ).1 = true) +
        event (simonPermutationLaw n) (fun f => SimonQueryTree.periodHit s τ f) := by
  have h := event_le_of_agree_off_bad
    ((simonTwoToOneDist s).map (fun f => SimonQueryTree.simonObservation f τ))
    ((simonPermutationLaw n).map (fun f => SimonQueryTree.simonObservation f τ))
    (simonObservationBad s) (fun t => t.2.1 = true)
    (simon_good_observation_mass hn s hs τ)
  simpa only [event_map, SimonQueryTree.simonObservation, simonObservationBad,
    SimonQueryTree.trace_inputs, SimonQueryTree.periodHit] using! h
end
end Qatlib.Papers.QPowerSimon97.Recovery.NativeRetryConstruction
