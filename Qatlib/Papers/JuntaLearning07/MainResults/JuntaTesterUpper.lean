/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.JuntaLearning07.MainResults.FSOracleDefs
import Qatlib.Papers.JuntaLearning07.MainResults.InfluenceIdentification
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Sqrt

/-!
# Fourier-sampling junta tester ingredients

This module develops the acceptance rule and Fourier-mass estimates for the junta tester studied
in [AticiServedio2007], Theorem III.3. `acceptsTranscript` accepts when the union of sampled
coordinate sets has size at most `k`; `fsProb_accepts_junta` proves acceptance with probability
one for every `k`-junta, and `junta_testing_upper_bound` packages this completeness statement
with a query budget.

The Fourier truncation `truncation` retains coefficients supported on a chosen coordinate set.
Its dependence property and the pointwise rounding bound `indicator_ne_sgn_le_sq` yield
`far_fourier_mass_le` and `fsWeight_outside_ge`, which force Fourier mass outside every set of
at most `k` coordinates for a function far from all `k`-juntas.

## Main statements

* `acceptor_accepts_junta` accepts every transcript whose sampled sets have positive target
  weight.
- `fsProb_accepts_junta` proves perfect completeness for any number of Fourier samples.
* `junta_testing_upper_bound` provides a budget at most `10 * (k + 1) / ε` with this
  completeness property.
- `far_fourier_mass_le` bounds Fourier mass supported inside a small coordinate set by `1 - ε`.
- `fsWeight_outside_ge` gives at least `ε` mass on sets leaving that coordinate set.

## References

* [Atici and Servedio, 2007][AticiServedio2007], Quantum Algorithms for Learning and Testing
  Juntas, Theorem III.3.
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace Qatlib.Papers.JuntaLearning07.MainResults

open scoped BigOperators

variable {n : ℕ}

/-- The acceptance condition that the union of all coordinate sets in a Fourier-sampling
transcript has cardinality at most `k`. -/
def acceptsTranscript (k : ℕ) {T : ℕ} (s : Fin T → Finset (Fin n)) : Prop :=
  (transcriptUnion s).card ≤ k

/-- For a `k`-junta, every transcript whose sampled sets all have positive Fourier weight
satisfies the acceptance condition. -/
theorem acceptor_accepts_junta {k : ℕ} {f : (Fin n → Bool) → Bool}
    (hf : IsKJunta (n := n) k f) {T : ℕ} (s : Fin T → Finset (Fin n))
    (hpos : ∀ t, 0 < fsWeight f (s t)) :
    acceptsTranscript k s := by
  obtain ⟨J, hJ, hdep⟩ := hf

  have hsubJ : ∀ t, s t ⊆ J := by
    intro t
    by_contra hcon
    have hzero : signCoeff f (s t) = 0 := signCoeff_eq_zero_of_not_subset hdep hcon
    have hne : signCoeff f (s t) ≠ 0 := (fsWeight_pos_iff f (s t)).mp (hpos t)
    exact hne hzero
  unfold acceptsTranscript
  exact le_trans (Finset.card_le_card (transcriptUnion_subset hsubJ)) hJ

/-- The transcript acceptance condition holds with probability one for a `k`-junta, for every
number `T` of Fourier samples. -/
theorem fsProb_accepts_junta {k : ℕ} {f : (Fin n → Bool) → Bool}
    (hf : IsKJunta (n := n) k f) (T : ℕ) :
    fsProb f T (acceptsTranscript (n := n) k) = 1 := by
  classical
  rw [fsProb_eq_sum]
  rw [show (∑ s : Fin T → Finset (Fin n),
        (if acceptsTranscript (n := n) k s then ∏ t : Fin T, fsWeight f (s t) else 0))
      = ∑ s : Fin T → Finset (Fin n), ∏ t : Fin T, fsWeight f (s t) from by
      apply Finset.sum_congr rfl
      intro s _
      by_cases hacc : acceptsTranscript (n := n) k s
      · rw [if_pos hacc]
      · rw [if_neg hacc]
        obtain ⟨J, hJ, hdep⟩ := hf
        have hex : ∃ t : Fin T, ¬ s t ⊆ J := by
          by_contra hcon
          push Not at hcon
          have hsub : transcriptUnion s ⊆ J := transcriptUnion_subset hcon
          have hle : (transcriptUnion s).card ≤ k :=
            le_trans (Finset.card_le_card hsub) hJ
          exact hacc hle
        obtain ⟨t, ht⟩ := hex
        have hzero : fsWeight f (s t) = 0 := by
          rw [fsWeight, signCoeff_eq_zero_of_not_subset hdep ht]
          ring
        exact (Finset.prod_eq_zero (Finset.mem_univ t) hzero).symm]
  exact fsProb_univ_one f T

/-- For positive `ε`, there is a sample count `T` at most `10 * (k + 1) / ε` such that every
`k`-junta is accepted with probability one. This packages the completeness component of the
tester associated with Theorem III.3 of [AticiServedio2007]. -/
theorem junta_testing_upper_bound (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ T : ℕ, (T : ℝ) ≤ 10 * ((k : ℝ) + 1) / ε ∧
      (∀ f : (Fin n → Bool) → Bool, IsKJunta (n := n) k f →
        fsProb f T (acceptsTranscript (n := n) k) = 1) := by
  refine ⟨Nat.floor (10 * ((k : ℝ) + 1) / ε), ?_, ?_⟩
  · exact Nat.floor_le (by positivity)
  · intro f hf
    exact fsProb_accepts_junta hf _

open Qatlib.Concepts.QueryComplexity.DegreeMethod.DegreeVariableDependence
open Qatlib.Concepts.ShadowModels.BooleanCubeFourier

open scoped BigOperators

variable {n : ℕ}

/-- Rounds a real number to `true` when it is nonnegative and to `false` when it is negative. -/
def sgnBool (t : ℝ) : Bool := if 0 ≤ t then true else false

/-- Pointwise domination of real-valued Boolean-cube functions implies domination of their
uniform expectations. -/
theorem uniformExpect_mono {F G : (Fin n → Bool) → ℝ} (h : ∀ x, F x ≤ G x) :
    uniformExpect F ≤ uniformExpect G := by
  unfold uniformExpect
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun x _ => h x)) (by positivity)

/-- For a real cube function expanded in the Boolean characters with coefficients `a`, the
uniform second moment equals the sum of the squared coefficients. -/
theorem uniformExpect_sq_expansion {a : Finset (Fin n) → ℝ}
    {F : (Fin n → Bool) → ℝ} (hF : ∀ x, F x = ∑ S, a S * cubeChar S x) :
    uniformExpect (fun x => F x ^ 2) = ∑ S, a S ^ 2 := by
  unfold uniformExpect
  rw [sum_sq_eq_mul_sum_sq_of_expansion a F hF]
  rw [← mul_assoc, inv_mul_cancel₀ (by positivity : (2 : ℝ) ^ n ≠ 0), one_mul]

/-- The indicator that a Boolean value differs from the sign rounding of `t` is bounded by the
squared difference between its sign representation and `t`. -/
theorem indicator_ne_sgn_le_sq (a : Bool) (t : ℝ) :
    (if a = sgnBool t then (0 : ℝ) else 1) ≤
      ((if a then (1 : ℝ) else -1) - t) ^ 2 := by
  cases a
  case true =>
    by_cases h : 0 ≤ t
    · have hs : sgnBool t = true := by simp [sgnBool, h]
      rw [if_pos (by simp [hs])]
      positivity
    · have ht : t < 0 := lt_of_not_ge h
      have hs : sgnBool t = false := by simp [sgnBool, h]
      rw [if_neg (by simp [hs])]
      show (1 : ℝ) ≤ (1 - t) ^ 2
      nlinarith [mul_pos_of_neg_of_neg ht (by linarith : t - 2 < 0)]
  case false =>
    by_cases h : 0 ≤ t
    · have hs : sgnBool t = true := by simp [sgnBool, h]
      rw [if_neg (by simp [hs])]
      show (1 : ℝ) ≤ (-1 - t) ^ 2
      nlinarith [mul_nonneg h (by linarith : (0 : ℝ) ≤ t + 2)]
    · have hs : sgnBool t = false := by simp [sgnBool, h]
      rw [if_pos (by simp [hs])]
      positivity

/-- A Boolean character indexed by `S` has the same value on inputs agreeing on a set `T`
containing `S`. -/
theorem cubeChar_eq_of_agree {S T : Finset (Fin n)} (hST : S ⊆ T)
    {x y : Fin n → Bool} (h : ∀ i ∈ T, x i = y i) :
    cubeChar S x = cubeChar S y := by
  unfold cubeChar
  apply Finset.prod_congr rfl
  intro i hi
  rw [h i (hST hi)]

/-- The sign Fourier coefficient of `f` at `S` when `S` is contained in `T`, and zero otherwise. -/
def truncCoeff (T : Finset (Fin n)) (f : (Fin n → Bool) → Bool)
    (S : Finset (Fin n)) : ℝ :=
  if S ⊆ T then signCoeff f S else 0

/-- The real-valued Fourier truncation of the sign representation of `f` obtained by retaining
only coefficients indexed by subsets of `T`. -/
def truncation (T : Finset (Fin n)) (f : (Fin n → Bool) → Bool)
    (x : Fin n → Bool) : ℝ :=
  ∑ S, truncCoeff T f S * cubeChar S x

/-- The Fourier truncation to subsets of `T` depends only on the coordinates in `T`. -/
theorem truncation_dependsOnlyOn {T : Finset (Fin n)} {f : (Fin n → Bool) → Bool} :
    dependsOnlyOnReal T (truncation T f) := by
  intro x y hxy
  unfold truncation
  apply Finset.sum_congr rfl
  intro S _
  by_cases hS : S ⊆ T
  · rw [show cubeChar S x = cubeChar S y from cubeChar_eq_of_agree hS hxy]
  · have hz : truncCoeff T f S = 0 := by simp [truncCoeff, hS]
    rw [hz]
    simp

/-- If `f` is `ε`-far from every `k`-junta, the total Fourier-sampling weight on subsets of any
set `T` of at most `k` coordinates is at most `1 - ε`. -/
theorem far_fourier_mass_le {k : ℕ} {ε : ℝ} {f : (Fin n → Bool) → Bool}
    (hfar : farFromJunta k ε f) {T : Finset (Fin n)} (hT : T.card ≤ k) :
    ∑ S ∈ T.powerset, fsWeight f S ≤ 1 - ε := by
  classical
  set G : (Fin n → Bool) → ℝ := truncation T f with hG
  set a : Finset (Fin n) → ℝ := truncCoeff T f with ha
  have hdep : dependsOnlyOn T (fun x => sgnBool (G x)) := by
    intro x y hxy
    have hxy' : G x = G y := by
      rw [hG]
      exact truncation_dependsOnlyOn (T := T) (f := f) x y hxy
    show sgnBool (G x) = sgnBool (G y)
    rw [hxy']
  have hjun : IsKJunta (n := n) k (fun x => sgnBool (G x)) := ⟨T, hT, hdep⟩
  have hfar' : ε ≤ disagreement f (fun x => sgnBool (G x)) := hfar _ hjun
  have hpoint : ∀ x, (if f x = sgnBool (G x) then (0 : ℝ) else 1) ≤
      (signFun f x - G x) ^ 2 := by
    intro x
    simpa [signFun] using! indicator_ne_sgn_le_sq (f x) (G x)
  have hmono : disagreement f (fun x => sgnBool (G x)) ≤
      uniformExpect (fun x => (signFun f x - G x) ^ 2) := by
    unfold disagreement
    exact uniformExpect_mono hpoint
  have hGexp : ∀ x, G x = ∑ S, a S * cubeChar S x := by
    intro x
    simp [hG, ha, truncation]
  have hdiff : (fun x => signFun f x - G x) =
      fun x => ∑ S, (signCoeff f S - a S) * cubeChar S x := by
    funext x
    rw [hGexp x, uniform_fourier_inversion (signFun f) x, ← Finset.sum_sub_distrib]
    simp only [signCoeff]
    apply Finset.sum_congr rfl
    intro S _
    ring
  have hparseval : uniformExpect (fun x => (signFun f x - G x) ^ 2) =
      ∑ S, (signCoeff f S - a S) ^ 2 := by
    have hsq : (fun x => (signFun f x - G x) ^ 2) =
        fun x => (∑ S, (signCoeff f S - a S) * cubeChar S x) ^ 2 := by
      funext x
      rw [congrFun hdiff x]
    rw [hsq]
    exact uniformExpect_sq_expansion (fun x => rfl)
  have hcoeff : ∑ S, (signCoeff f S - a S) ^ 2 =
      ∑ S ∈ Finset.univ \ T.powerset, fsWeight f S := by
    have hstep : ∀ S, (signCoeff f S - a S) ^ 2 =
        if S ∉ T.powerset then fsWeight f S else 0 := by
      intro S
      by_cases hS : S ∈ T.powerset
      · have hsub : S ⊆ T := Finset.mem_powerset.mp hS
        have haS : a S = signCoeff f S := by simp [a, truncCoeff, hsub]
        simp [hS, haS]
      · have hsub : ¬ S ⊆ T := by simpa [Finset.mem_powerset] using! hS
        have haS : a S = 0 := by simp [a, truncCoeff, hsub]
        simp [hS, haS, fsWeight]
    rw [Finset.sum_congr rfl (fun S _ => hstep S), ← Finset.sum_filter]
    congr 1
    ext S
    simp
  have htotal : (∑ S ∈ Finset.univ \ T.powerset, fsWeight f S) =
      1 - ∑ S ∈ T.powerset, fsWeight f S := by
    have hdisj : Disjoint (Finset.univ \ T.powerset) T.powerset := by
      rw [Finset.disjoint_left]
      intro S h1 h2
      exact (Finset.mem_sdiff.mp h1).2 h2
    have hunion : (Finset.univ \ T.powerset) ∪ T.powerset = Finset.univ :=
      Finset.sdiff_union_of_subset (Finset.subset_univ _)
    have h := Finset.sum_union hdisj (f := fun S => fsWeight f S)
    rw [hunion] at h
    have htot : (∑ S ∈ (Finset.univ : Finset (Finset (Fin n))), fsWeight f S) = 1 :=
      fsWeight_total f
    rw [htot] at h
    linarith
  have hchain : ε ≤ ∑ S ∈ Finset.univ \ T.powerset, fsWeight f S := by
    calc ε ≤ disagreement f (fun x => sgnBool (G x)) := hfar'
      _ ≤ uniformExpect (fun x => (signFun f x - G x) ^ 2) := hmono
      _ = ∑ S, (signCoeff f S - a S) ^ 2 := hparseval
      _ = ∑ S ∈ Finset.univ \ T.powerset, fsWeight f S := hcoeff
  rw [htotal] at hchain
  linarith

/-- If `f` is `ε`-far from every `k`-junta, at least `ε` of its Fourier-sampling weight lies on
sets that are not contained in any fixed set `U` of at most `k` coordinates. -/
theorem fsWeight_outside_ge {k : ℕ} {ε : ℝ} {f : (Fin n → Bool) → Bool}
    (hfar : farFromJunta k ε f) {U : Finset (Fin n)} (hU : U.card ≤ k) :
    ε ≤ ∑ S ∈ Finset.univ \ U.powerset, fsWeight f S := by
  have h := far_fourier_mass_le hfar hU
  have htotal : (∑ S ∈ Finset.univ \ U.powerset, fsWeight f S) =
      1 - ∑ S ∈ U.powerset, fsWeight f S := by
    have hdisj : Disjoint (Finset.univ \ U.powerset) U.powerset := by
      rw [Finset.disjoint_left]
      intro S h1 h2
      exact (Finset.mem_sdiff.mp h1).2 h2
    have hunion : (Finset.univ \ U.powerset) ∪ U.powerset = Finset.univ :=
      Finset.sdiff_union_of_subset (Finset.subset_univ _)
    have hs := Finset.sum_union hdisj (f := fun S => fsWeight f S)
    rw [hunion] at hs
    have htot : (∑ S ∈ (Finset.univ : Finset (Finset (Fin n))), fsWeight f S) = 1 :=
      fsWeight_total f
    rw [htot] at hs
    linarith
  rw [htotal]
  linarith

end Qatlib.Papers.JuntaLearning07.MainResults
