/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace CBMD

open Matrix Set
open scoped Matrix.Norms.L2Operator ComplexOrder

private theorem l2_norm_one_le {I : Type*} [Fintype I] [DecidableEq I] :
    ‖(1 : Matrix I I ℂ)‖ ≤ 1 := by
  rcases subsingleton_or_nontrivial (Matrix I I ℂ) with h | h
  · simp [Subsingleton.elim (1 : Matrix I I ℂ) 0]
  · exact CStarRing.norm_one.le

noncomputable def orderedDysonTerm {I : Type} [Fintype I] [DecidableEq I]
    (A : ℝ → Matrix I I ℂ) (s : ℝ) : ℕ → ℝ → Matrix I I ℂ
  | 0, _ => 1
  | n+1, t => ∫ u in s..t, -(A u * orderedDysonTerm A s n u)

noncomputable def orderedEvolution {I : Type} [Fintype I] [DecidableEq I]
    (A : ℝ → Matrix I I ℂ) (s t : ℝ) : Matrix I I ℂ :=
  ∑' n : ℕ, orderedDysonTerm A s n t

theorem orderedDysonTerm_continuous {I : Type} [Fintype I] [DecidableEq I]
    (A : ℝ → Matrix I I ℂ) (hA : Continuous A) (s : ℝ) (n : ℕ) :
    Continuous (orderedDysonTerm A s n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    exact (intervalIntegral.differentiable_integral_of_continuous
      (hA.mul ih).neg).continuous

theorem orderedDysonTerm_hasDerivAt_succ {I : Type} [Fintype I] [DecidableEq I]
    (A : ℝ → Matrix I I ℂ) (hA : Continuous A) (s : ℝ) (n : ℕ) (t : ℝ) :
    HasDerivAt (orderedDysonTerm A s (n+1))
      (-(A t * orderedDysonTerm A s n t)) t := by
  have hc := (hA.mul (orderedDysonTerm_continuous A hA s n)).neg
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

@[simp] theorem orderedDysonTerm_succ_self {I : Type} [Fintype I] [DecidableEq I]
    (A : ℝ → Matrix I I ℂ) (s : ℝ) (n : ℕ) : orderedDysonTerm A s (n+1) s = 0 := by
  simp [orderedDysonTerm]

@[simp] theorem orderedEvolution_self {I : Type} [Fintype I] [DecidableEq I]
    (A : ℝ → Matrix I I ℂ) (s : ℝ) : orderedEvolution A s s = 1 := by
  unfold orderedEvolution
  rw [tsum_eq_single 0]
  · rfl
  · intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    exact orderedDysonTerm_succ_self A s k

theorem orderedDysonTerm_norm_le {I : Type} [Fintype I] [DecidableEq I]
    (A : ℝ → Matrix I I ℂ) (hA : Continuous A) (s t M : ℝ)
    (hM : 0 ≤ M) (hbound : ∀ u ∈ uIcc s t, ‖A u‖ ≤ M) (n : ℕ) :
    ‖orderedDysonTerm A s n t‖ ≤ (M * |t-s|)^n / (n.factorial : ℝ) := by
  induction n generalizing t with
  | zero => simpa [orderedDysonTerm] using (l2_norm_one_le (I := I))
  | succ n ih =>
    let g : ℝ → ℝ := fun u => M^(n+1) / (n.factorial : ℝ) * |u-s|^n
    have hg : Continuous g := by fun_prop
    have hb : ∀ u ∈ uIoc s t, ‖-(A u * orderedDysonTerm A s n u)‖ ≤ g u := by
      intro u hu
      have hu' : u ∈ uIcc s t := uIoc_subset_uIcc hu
      have hn := ih u (fun x hx => hbound x (uIcc_subset_uIcc_left hu' hx))
      calc
        _ ≤ ‖A u‖ * ‖orderedDysonTerm A s n u‖ := by
          rw [norm_neg]; exact norm_mul_le _ _
        _ ≤ M * ((M * |u-s|)^n / (n.factorial : ℝ)) :=
          mul_le_mul (hbound u hu') hn (norm_nonneg _) hM
        _ = g u := by dsimp [g]; rw [mul_pow, pow_succ]; ring
    calc
      _ ≤ ∫ u in uIoc s t, ‖-(A u * orderedDysonTerm A s n u)‖ :=
        intervalIntegral.norm_integral_le_integral_norm_uIoc
      _ ≤ ∫ u in uIoc s t, g u := by
        apply MeasureTheory.integral_mono_ae
        · exact ((hA.mul (orderedDysonTerm_continuous A hA s n)).neg.norm.intervalIntegrable s t).def'
        · exact (hg.intervalIntegrable s t).def'
        · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIoc hb
      _ = (M * |t-s|)^(n+1) / ((n+1).factorial : ℝ) := by
        rw [show g = fun u => M^(n+1) / (n.factorial : ℝ) * |u-s|^n from rfl,
          MeasureTheory.integral_const_mul, integral_pow_abs_sub_uIoc]
        rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_pow]
        field_simp

theorem orderedDysonTerm_summable {I : Type} [Fintype I] [DecidableEq I]
    (A : ℝ → Matrix I I ℂ) (hA : Continuous A) (s t : ℝ) :
    Summable (fun n => orderedDysonTerm A s n t) := by
  obtain ⟨C, hC⟩ := (isCompact_uIcc.image hA).isBounded.exists_norm_le
  let M := max 0 C
  apply Summable.of_norm_bounded (Real.summable_pow_div_factorial (M * |t-s|))
  intro n
  exact orderedDysonTerm_norm_le A hA s t M (le_max_left _ _)
    (fun u hu => (hC (A u) ⟨u, hu, rfl⟩).trans (le_max_right _ _)) n

theorem orderedEvolution_hasDerivAt {I : Type} [Fintype I] [DecidableEq I]
    (A : ℝ → Matrix I I ℂ) (hA : Continuous A) (s t : ℝ) :
    HasDerivAt (orderedEvolution A s) (-(A t * orderedEvolution A s t)) t := by
  let R : ℝ := |t-s| + 1
  let a := s-R
  let b := s+R
  have hR : 0 < R := by dsimp [R]; positivity
  obtain ⟨C, hC⟩ := ((isCompact_Icc (a := a) (b := b)).image hA).isBounded.exists_norm_le
  let M := max 0 C
  have hM : 0 ≤ M := le_max_left _ _
  have hbound : ∀ u ∈ Icc a b, ‖A u‖ ≤ M := by
    intro u hu
    exact (hC (A u) ⟨u, hu, rfl⟩).trans (le_max_right _ _)
  have hs : s ∈ Ioo a b := by dsimp [a, b]; constructor <;> linarith
  have ht : t ∈ Ioo a b := by
    dsimp [a, b, R]
    constructor <;> linarith [le_abs_self (t-s), neg_le_abs (t-s)]
  have hn (n : ℕ) (u : ℝ) (hu : u ∈ Ioo a b) :
      ‖orderedDysonTerm A s n u‖ ≤ (M*R)^n / (n.factorial : ℝ) := by
    have hsub : uIcc s u ⊆ Icc a b :=
      (convex_Icc a b).ordConnected.uIcc_subset ⟨hs.1.le, hs.2.le⟩ ⟨hu.1.le, hu.2.le⟩
    have hb := orderedDysonTerm_norm_le A hA s u M hM
      (fun x hx => hbound x (hsub hx)) n
    have huR : |u-s| ≤ R := by
      rw [abs_le]
      dsimp [a, b] at hu
      constructor <;> linarith [hu.1, hu.2]
    exact hb.trans (by gcongr)
  have hd := hasDerivAt_tsum_of_isPreconnected
    ((Real.summable_pow_div_factorial (M*R)).mul_left M)
    isOpen_Ioo isPreconnected_Ioo
    (fun n u (_ : u ∈ Ioo a b) => orderedDysonTerm_hasDerivAt_succ A hA s n u)
    (fun n u hu => (by
      rw [norm_neg]
      exact (norm_mul_le _ _).trans
        (mul_le_mul (hbound u ⟨hu.1.le, hu.2.le⟩) (hn n u hu) (norm_nonneg _) hM)))
    hs (by simp) ht
  have he : (fun u => 1 + ∑' n, orderedDysonTerm A s (n+1) u) = orderedEvolution A s := by
    funext u
    exact ((orderedDysonTerm_summable A hA s u).tsum_eq_zero_add).symm
  have hsum : (∑' n, -(A t * orderedDysonTerm A s n t)) =
      -(A t * orderedEvolution A s t) := by
    simp_rw [← neg_mul]
    exact (orderedDysonTerm_summable A hA s t).tsum_mul_left (-A t)
  rw [hsum] at hd
  simpa only [he] using hd.const_add 1

theorem ordered_matrix_ode_unique {I : Type} [Fintype I] [DecidableEq I]
    (A : ℝ → Matrix I I ℂ) (hA : Continuous A)
    (f g : ℝ → Matrix I I ℂ) (s : ℝ) (hinit : f s = g s)
    (hf : ∀ t, HasDerivAt f (-(A t * f t)) t)
    (hg : ∀ t, HasDerivAt g (-(A t * g t)) t) : f = g := by
  funext t
  let a := min s t - 1
  let b := max s t + 1
  obtain ⟨C, hC⟩ := ((isCompact_Icc (a := a) (b := b)).image hA).isBounded.exists_norm_le
  let K : NNReal := ⟨max 0 C, le_max_left _ _⟩
  have hbound (u : ℝ) (hu : u ∈ Ioo a b) : ‖A u‖ ≤ (K : ℝ) :=
    (hC (A u) ⟨u, ⟨hu.1.le, hu.2.le⟩, rfl⟩).trans (le_max_right _ _)
  have hlip (u : ℝ) (hu : u ∈ Ioo a b) :
      LipschitzOnWith K (fun x : Matrix I I ℂ => -(A u*x)) Set.univ := by
    apply LipschitzWith.lipschitzOnWith
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, dist_eq_norm,
      show -(A u*x) - -(A u*y) = -(A u*(x-y)) from by noncomm_ring, norm_neg]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hbound u hu) (norm_nonneg _))
  have hs : s ∈ Ioo a b := by
    dsimp [a, b]
    constructor <;> linarith [min_le_left s t, le_max_left s t]
  have ht : t ∈ Icc a b := by
    dsimp [a, b]
    constructor <;> linarith [min_le_right s t, le_max_right s t]
  exact ODE_solution_unique_of_mem_Icc (s := fun _ => Set.univ) hlip hs
    (continuous_iff_continuousAt.mpr (fun u => (hf u).continuousAt)).continuousOn
    (fun u _ => hf u) (fun _ _ => Set.mem_univ _)
    (continuous_iff_continuousAt.mpr (fun u => (hg u).continuousAt)).continuousOn
    (fun u _ => hg u) (fun _ _ => Set.mem_univ _) hinit ht

theorem orderedEvolution_cocycle {I : Type} [Fintype I] [DecidableEq I]
    (A : ℝ → Matrix I I ℂ) (hA : Continuous A) (s r t : ℝ) :
    orderedEvolution A r t * orderedEvolution A s r = orderedEvolution A s t := by
  have he := ordered_matrix_ode_unique A hA
    (fun u => orderedEvolution A r u * orderedEvolution A s r)
    (orderedEvolution A s) r (by simp)
    (fun u => (by
      convert! (orderedEvolution_hasDerivAt A hA r u).mul_const (orderedEvolution A s r) using 1
      noncomm_ring))
    (orderedEvolution_hasDerivAt A hA s)
  exact congrFun he t

theorem ordered_evolution_dyson_semantics :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (A : ℝ → Matrix I I ℂ),
      Continuous A →
      (∀ s t : ℝ, Summable (fun n => orderedDysonTerm A s n t)) ∧
      (∀ s : ℝ, orderedEvolution A s s = 1) ∧
      (∀ s t : ℝ, HasDerivAt (orderedEvolution A s)
        (-(A t * orderedEvolution A s t)) t) ∧
      (∀ s r t : ℝ, orderedEvolution A r t * orderedEvolution A s r = orderedEvolution A s t) ∧
      (∀ (s : ℝ) (V : ℝ → Matrix I I ℂ), V s = 1 →
        (∀ t, HasDerivAt V (-(A t * V t)) t) → V = orderedEvolution A s) := by
  intro I _ _ A hA
  refine ⟨orderedDysonTerm_summable A hA, orderedEvolution_self A,
    orderedEvolution_hasDerivAt A hA, orderedEvolution_cocycle A hA, ?_⟩
  intro s V hV hder
  exact ordered_matrix_ode_unique A hA V (orderedEvolution A s) s
    (by simpa using hV) hder (orderedEvolution_hasDerivAt A hA s)

end CBMD

end Qatlib.Foundations.CbmdAnalysis.Core
