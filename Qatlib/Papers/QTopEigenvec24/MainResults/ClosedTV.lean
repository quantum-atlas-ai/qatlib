/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QTopEigenvec24.MainResults.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section


/-! Finite probability identities and the total variation bound for conditioning and pushforward. No eigenvector algorithm is asserted. -/

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator Classical ComplexOrder

namespace Qatlib.Papers.QTopEigenvec24.MainResults.ClosedTV
open Qatlib.Papers.QTopEigenvec24.MainResults
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteInformationDivergence

/-! Mathematical identities for the source model. -/

/-- The probability of an event is at most one. -/
theorem pr_le_one {Ω : Type*} [Fintype Ω] (p : FinDist Ω) (A : Ω → Prop)
    [DecidablePred A] : pr p A ≤ 1 := by
  have h := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset A Finset.univ)
    (fun x _ _ => p.nonneg x)
  simpa [pr, p.sum_one] using h

/-- The mass inside an event plus the mass outside it is the total mass. -/
theorem pr_add_pr_compl {Ω : Type*} [Fintype Ω] (p : FinDist Ω) (A : Ω → Prop)
    [DecidablePred A] : pr p A + pr p (fun ω => ¬ A ω) = 1 := by
  have h : pr p (fun ω => ¬ A ω) = 1 - pr p A := by
    have hsub : Finset.univ.filter (fun ω => ¬ A ω) =
        Finset.univ \ Finset.univ.filter A := by
      ext ω
      simp
    rw [pr, hsub]
    have hsdiff := Finset.sum_sdiff (s₁ := Finset.univ.filter A) (s₂ := Finset.univ)
      (f := p.prob) (Finset.filter_subset A Finset.univ)
    rw [p.sum_one] at hsdiff
    have hpr : pr p A = ∑ x ∈ Finset.univ.filter A, p.prob x := rfl
    rw [hpr]
    linarith
  rw [h]
  ring

/-! ## Singular-value notation for Theorem 2.19 -/

/-- Mass of `y` coming from samples in the event `A`. -/
def sliceA {Ω α : Type*} [Fintype Ω] [_instFintypeα : Fintype α] (p : FinDist Ω) (X : Ω → α)
    (A : Ω → Prop) [DecidablePred A] (y : α) : ℝ :=
  ∑ ω, if X ω = y ∧ A ω then p.prob ω else 0

/-- Mass of `y` coming from samples outside the event `A`. -/
def sliceAc {Ω α : Type*} [Fintype Ω] [_instFintypeα : Fintype α] (p : FinDist Ω) (X : Ω → α)
    (A : Ω → Prop) [DecidablePred A] (y : α) : ℝ :=
  ∑ ω, if X ω = y ∧ ¬ A ω then p.prob ω else 0

/-- **Corollary 2.24.**  Conditioning a random variable on an event `A` of
positive probability moves it in total variation by at most the mass of the
complement of `A`: `d_TV(X, X|A) ≤ 1 - Pr[A]`. -/
theorem cor2_24_conditioningTV {Ω : Type*} {α : Type} [Fintype Ω] [_instDecidableEqΩ : DecidableEq Ω]
    [_instFintypeα : Fintype α] [DecidableEq α] (p : FinDist Ω) (X : Ω → α) (A : Ω → Prop)
    [DecidablePred A] (hA : 0 < pr p A) :
    tv (pushforwardTo α X p) (pushforwardTo α X (condLaw p A hA)) ≤ 1 - pr p A := by
  classical
  have hm1 : pr p A ≤ 1 := pr_le_one p A
  have hane : pr p A ≠ 0 := ne_of_gt hA
  -- masses of the two slices
  have ha_nonneg : ∀ y : α, 0 ≤ sliceA p X A y := by
    intro y
    exact Finset.sum_nonneg fun ω _ => by
      by_cases h : X ω = y ∧ A ω
      · simpa [h] using p.nonneg ω
      · simp [h]
  have hb_nonneg : ∀ y : α, 0 ≤ sliceAc p X A y := by
    intro y
    exact Finset.sum_nonneg fun ω _ => by
      by_cases h : X ω = y ∧ ¬ A ω
      · simpa [h] using p.nonneg ω
      · simp [h]
  have hsum_a : ∑ y, sliceA p X A y = pr p A := by
    simp only [sliceA, pr]
    rw [Finset.sum_comm]
    trans ∑ ω : Ω, (if A ω then p.prob ω else 0)
    · apply Finset.sum_congr rfl
      intro ω _
      by_cases h : A ω
      · rw [ite_eq_left h]
        rw [Finset.sum_eq_single (X ω)]
        · simp [h]
        · intro y _ hy
          rw [ite_eq_right]
          intro hc
          exact hy hc.1.symm
        · intro hmem
          exact absurd (Finset.mem_univ (X ω)) hmem
      · rw [ite_eq_right h]
        apply Finset.sum_eq_zero
        intro y _
        rw [ite_eq_right]
        intro hc
        exact h hc.2
    · rw [← Finset.sum_filter]
  have hsum_b : ∑ y, sliceAc p X A y = 1 - pr p A := by
    have hcompl : pr p (fun ω => ¬ A ω) = 1 - pr p A := by
      have h := pr_add_pr_compl p A
      linarith
    simp only [sliceAc]
    rw [Finset.sum_comm]
    trans ∑ ω : Ω, (if ¬ A ω then p.prob ω else 0)
    · apply Finset.sum_congr rfl
      intro ω _
      by_cases h : ¬ A ω
      · rw [ite_eq_left h]
        rw [Finset.sum_eq_single (X ω)]
        · simp [h]
        · intro y _ hy
          rw [ite_eq_right]
          intro hc
          exact hy hc.1.symm
        · intro hmem
          exact absurd (Finset.mem_univ (X ω)) hmem
      · rw [ite_eq_right h]
        apply Finset.sum_eq_zero
        intro y _
        rw [ite_eq_right]
        intro hc
        exact h hc.2
    · rw [← Finset.sum_filter]
      exact hcompl
  have hP : ∀ y : α, (pushforwardTo α X p).prob y = sliceA p X A y + sliceAc p X A y := by
    intro y
    simp only [pushforwardTo, sliceA, sliceAc]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ω _
    by_cases h1 : X ω = y
    · by_cases h2 : A ω <;> simp [h1, h2]
    · simp [h1]
  have hQ : ∀ y : α, (pushforwardTo α X (condLaw p A hA)).prob y = sliceA p X A y / pr p A := by
    intro y
    simp only [pushforwardTo, condLaw, sliceA]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro ω _
    by_cases h1 : X ω = y
    · by_cases h2 : A ω <;> simp [h1, h2]
    · simp [h1]
  -- the two triangle-inequality pieces
  have hcoef : 0 ≤ 1 / pr p A - 1 := by
    have hle : 1 ≤ 1 / pr p A := by
      rw [le_div_iff₀ hA]
      simpa using hm1
    linarith
  have hpiece1 : ∑ y, |(pushforwardTo α X p).prob y - sliceA p X A y| = 1 - pr p A := by
    have hpt : ∀ y : α, (pushforwardTo α X p).prob y - sliceA p X A y = sliceAc p X A y := by
      intro y
      rw [hP y]
      ring
    rw [Finset.sum_congr rfl (fun y _ => by rw [hpt y, abs_of_nonneg (hb_nonneg y)])]
    exact hsum_b
  have hpiece2 : ∑ y,
      |sliceA p X A y - (pushforwardTo α X (condLaw p A hA)).prob y| = 1 - pr p A := by
    have hpt : ∀ y : α,
        (pushforwardTo α X (condLaw p A hA)).prob y - sliceA p X A y =
          sliceA p X A y * (1 / pr p A - 1) := by
      intro y
      rw [hQ y]
      field_simp
    have habs : ∀ y : α,
        |sliceA p X A y - (pushforwardTo α X (condLaw p A hA)).prob y| =
          sliceA p X A y * (1 / pr p A - 1) := by
      intro y
      rw [abs_sub_comm, hpt y]
      exact abs_of_nonneg (mul_nonneg (ha_nonneg y) hcoef)
    simp only [habs]
    rw [← Finset.sum_mul, hsum_a]
    field_simp
  have htri : ∀ y : α,
      |(pushforwardTo α X p).prob y - (pushforwardTo α X (condLaw p A hA)).prob y| ≤
        |(pushforwardTo α X p).prob y - sliceA p X A y| +
          |sliceA p X A y - (pushforwardTo α X (condLaw p A hA)).prob y| := by
    intro y
    have hsplit : (pushforwardTo α X p).prob y - (pushforwardTo α X (condLaw p A hA)).prob y =
        ((pushforwardTo α X p).prob y - sliceA p X A y) +
          (sliceA p X A y - (pushforwardTo α X (condLaw p A hA)).prob y) := by ring
    rw [hsplit]
    exact abs_add_le _ _
  calc tv (pushforwardTo α X p) (pushforwardTo α X (condLaw p A hA))
      = (∑ y, |(pushforwardTo α X p).prob y - (pushforwardTo α X (condLaw p A hA)).prob y|) / 2 := rfl
    _ ≤ (∑ y, (|(pushforwardTo α X p).prob y - sliceA p X A y| +
          |sliceA p X A y - (pushforwardTo α X (condLaw p A hA)).prob y|)) / 2 := by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        exact Finset.sum_le_sum fun y _ => htri y
    _ = ((1 - pr p A) + (1 - pr p A)) / 2 := by rw [Finset.sum_add_distrib, hpiece1, hpiece2]
    _ = 1 - pr p A := by ring

/-! ## Theorem 2.10: sparse block encoding -/

/-- A finitely supported probability law cannot have the moment generating function of a standard Gaussian. -/
theorem noFiniteGaussian {Ω : Type*} [Fintype Ω]
    (p X : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (hsum : ∑ ω, p ω = 1) :
    ¬ (∀ t : ℝ, ∑ ω, p ω * Real.exp (t * X ω) = Real.exp (t ^ 2 / 2)) := by
  intro hmgf
  classical
  let B : ℝ := (∑ ω, |X ω|) + 1
  have hB : 0 < B := by
    dsimp [B]
    have hn : 0 ≤ ∑ ω, |X ω| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    linarith
  have hX : ∀ ω, X ω ≤ B := by
    intro ω
    have hs : |X ω| ≤ ∑ ω', |X ω'| :=
      Finset.single_le_sum (f := fun ω' : Ω => |X ω'|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ ω)
    dsimp [B]
    linarith [le_abs_self (X ω)]
  let t : ℝ := 2 * B + 2
  have ht : 0 < t := by dsimp [t]; linarith
  have hbound : ∑ ω, p ω * Real.exp (t * X ω) ≤ Real.exp (t * B) := by
    calc ∑ ω, p ω * Real.exp (t * X ω)
        ≤ ∑ ω, p ω * Real.exp (t * B) := by
          apply Finset.sum_le_sum
          intro ω _
          exact mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hX ω) ht.le)) (hp ω)
      _ = Real.exp (t * B) := by rw [← Finset.sum_mul, hsum, one_mul]
  rw [hmgf t] at hbound
  have hexponent : t * B < t ^ 2 / 2 := by dsimp [t]; nlinarith
  exact (not_le_of_gt (Real.exp_lt_exp.mpr hexponent)) hbound


end Qatlib.Papers.QTopEigenvec24.MainResults.ClosedTV
