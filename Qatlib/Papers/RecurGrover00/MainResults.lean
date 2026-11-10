/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Hom
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Set.Defs
import Mathlib.Logic.Function.Defs
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Order.Filter.Tendsto
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Order.Lattice
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.LinearCombination.Lemmas
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Continuous
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.UniformSpace.Defs

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Filter

namespace Qatlib.Papers.RecurGrover00.MainResults

variable {M U : Type*}

abbrev StateIndex (M U : Type*) : Type _ := M ⊕ U

def phaseMarked [Fintype M] [Fintype U] (γ : ℝ) (a : StateIndex M U → ℂ) :
    StateIndex M U → ℂ :=
  Sum.elim (fun j => Complex.exp (Complex.I * (γ : ℂ)) * a (Sum.inl j)) (fun j => a (Sum.inr j))

def GApply [Fintype M] [Fintype U] (β : ℝ) (η b : StateIndex M U → ℂ) :
    StateIndex M U → ℂ :=
  fun x => (1 - Complex.exp (Complex.I * (β : ℂ))) * η x *
              (∑ s, star (η s) * b s) - b x

def groverStep [Fintype M] [Fintype U] (β γ : ℝ) (η a : StateIndex M U → ℂ) :
    StateIndex M U → ℂ :=
  GApply β η (phaseMarked γ a)

def weightK [Fintype M] (η : StateIndex M U → ℂ) : ℝ := ∑ i : M, Complex.normSq (η (Sum.inl i))

def weightL [Fintype U] (η : StateIndex M U → ℂ) : ℝ := ∑ i : U, Complex.normSq (η (Sum.inr i))

def weightedAvgK [Fintype M] (η : StateIndex M U → ℂ) (Wk : ℝ) (k' : M → ℂ) : ℂ :=
  ((∑ i : M, (Complex.normSq (η (Sum.inl i)) : ℂ) * k' i) / (Wk : ℂ))

def weightedAvgL [Fintype U] (η : StateIndex M U → ℂ) (Wl : ℝ) (l' : U → ℂ) : ℂ :=
  ((∑ i : U, (Complex.normSq (η (Sum.inr i)) : ℂ) * l' i) / (Wl : ℂ))

variable [Fintype M] [Fintype U]

theorem inner_sum_split (γ : ℝ) (η a : StateIndex M U → ℂ) :
    (∑ s : StateIndex M U, star (η s) * phaseMarked γ a s)
      = Complex.exp (Complex.I * (γ : ℂ)) *
          (∑ i : M, a (Sum.inl i) * star (η (Sum.inl i)))
        + (∑ i : U, a (Sum.inr i) * star (η (Sum.inr i))) := by
  rw [Fintype.sum_sum_type, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    rintro i -
    simp only [phaseMarked, Sum.elim_inl]
    ring
  · apply Finset.sum_congr rfl
    rintro i -
    simp only [phaseMarked, Sum.elim_inr]
    ring

theorem recursion_marked (β γ : ℝ) (η a : StateIndex M U → ℂ) (j : M) :
    groverStep β γ η a (Sum.inl j) =
      (1 - Complex.exp (Complex.I * (β : ℂ))) * Complex.exp (Complex.I * (γ : ℂ)) *
          η (Sum.inl j) * (∑ i : M, a (Sum.inl i) * star (η (Sum.inl i)))
      + (1 - Complex.exp (Complex.I * (β : ℂ))) * η (Sum.inl j) *
          (∑ i : U, a (Sum.inr i) * star (η (Sum.inr i)))
      - Complex.exp (Complex.I * (γ : ℂ)) * a (Sum.inl j) := by
  simp only [groverStep, GApply]
  rw [inner_sum_split]
  simp only [phaseMarked, Sum.elim_inl]
  ring

theorem recursion_unmarked (β γ : ℝ) (η a : StateIndex M U → ℂ) (j : U) :
    groverStep β γ η a (Sum.inr j) =
      (1 - Complex.exp (Complex.I * (β : ℂ))) * Complex.exp (Complex.I * (γ : ℂ)) *
          η (Sum.inr j) * (∑ i : M, a (Sum.inl i) * star (η (Sum.inl i)))
      + (1 - Complex.exp (Complex.I * (β : ℂ))) * η (Sum.inr j) *
          (∑ i : U, a (Sum.inr i) * star (η (Sum.inr i)))
      - a (Sum.inr j) := by
  simp only [groverStep, GApply]
  rw [inner_sum_split]
  simp only [phaseMarked, Sum.elim_inr]
  ring

theorem deviation_invariant (x bar : ℕ → ℂ) (f : ℕ → ℂ) (c : ℂ)
    (hx : ∀ t, x (t + 1) = f t - c * x t)
    (hb : ∀ t, bar (t + 1) = f t - c * bar t) :
    ∀ t, x t - bar t = (-c) ^ t * (x 0 - bar 0) := by
  intro t
  induction t with
  | zero => simp
  | succ n ih =>
    rw [hx n, hb n]
    have h1 : f n - c * x n - (f n - c * bar n) = -c * (x n - bar n) := by ring
    rw [h1, ih, pow_succ]
    ring

theorem exp_I_pow (γ : ℝ) (t : ℕ) :
    (Complex.exp (Complex.I * (γ : ℂ))) ^ t = Complex.exp (Complex.I * ((t : ℂ) * γ)) := by
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

theorem marked_deviation_closed_form
    (k' : M → ℕ → ℂ) (kbar : ℕ → ℂ) (C : ℕ → ℂ) (γ : ℝ)
    (hk : ∀ (j : M) (t : ℕ), k' j (t + 1) = 2 * C t - Complex.exp (Complex.I * (γ : ℂ)) * k' j t)
    (hb : ∀ t, kbar (t + 1) = 2 * C t - Complex.exp (Complex.I * (γ : ℂ)) * kbar t) :
    ∀ (j : M) (t : ℕ),
      k' j t - kbar t = (-1) ^ t * Complex.exp (Complex.I * ((t : ℂ) * γ)) * (k' j 0 - kbar 0) := by
  intro j t
  rw [deviation_invariant (fun t => k' j t) kbar (fun t => 2 * C t)
        (Complex.exp (Complex.I * (γ : ℂ))) (hk j) hb t]
  congr 1
  rw [← neg_one_mul, mul_pow, exp_I_pow]

theorem unmarked_deviation_closed_form
    (l' : U → ℕ → ℂ) (lbar : ℕ → ℂ) (C : ℕ → ℂ)
    (hl : ∀ (j : U) (t : ℕ), l' j (t + 1) = 2 * C t - l' j t)
    (hb : ∀ t, lbar (t + 1) = 2 * C t - lbar t) :
    ∀ (j : U) (t : ℕ), l' j t - lbar t = (-1) ^ t * (l' j 0 - lbar 0) := by
  intro j t
  have hl' : ∀ t, l' j (t + 1) = 2 * C t - 1 * l' j t := by
    intro t; rw [one_mul]; exact hl j t
  have hb' : ∀ t, lbar (t + 1) = 2 * C t - 1 * lbar t := by
    intro t; rw [one_mul]; exact hb t
  rw [deviation_invariant (fun t => l' j t) lbar (fun t => 2 * C t) 1 hl' hb' t]

theorem marked_amplitude_closed_form
    (η : StateIndex M U → ℂ) (k' : M → ℕ → ℂ) (kbar : ℕ → ℂ) (C : ℕ → ℂ) (γ : ℝ)
    (hk : ∀ (j : M) (t : ℕ), k' j (t + 1) = 2 * C t - Complex.exp (Complex.I * (γ : ℂ)) * k' j t)
    (hb : ∀ t, kbar (t + 1) = 2 * C t - Complex.exp (Complex.I * (γ : ℂ)) * kbar t)
    (j : M) (t : ℕ) :
    η (Sum.inl j) * k' j t =
      η (Sum.inl j) *
        (kbar t + (-1) ^ t * Complex.exp (Complex.I * ((t : ℂ) * γ)) * (k' j 0 - kbar 0)) := by
  have hd := marked_deviation_closed_form k' kbar C γ hk hb j t
  rw [sub_eq_iff_eq_add] at hd
  rw [hd]; ring

theorem unmarked_amplitude_closed_form
    (η : StateIndex M U → ℂ) (l' : U → ℕ → ℂ) (lbar : ℕ → ℂ) (C : ℕ → ℂ)
    (hl : ∀ (j : U) (t : ℕ), l' j (t + 1) = 2 * C t - l' j t)
    (hb : ∀ t, lbar (t + 1) = 2 * C t - lbar t)
    (j : U) (t : ℕ) :
    η (Sum.inr j) * l' j t = η (Sum.inr j) * (lbar t + (-1) ^ t * (l' j 0 - lbar 0)) := by
  have hd := unmarked_deviation_closed_form l' lbar C hl hb j t
  rw [sub_eq_iff_eq_add] at hd
  rw [hd]; ring

theorem normSq_phase_diff (a1 a2 α β : ℝ) :
    ‖(a1 : ℂ) * Complex.exp (α * Complex.I) - (a2 : ℂ) * Complex.exp (β * Complex.I)‖ ^ 2
      = a1 ^ 2 + a2 ^ 2 - 2 * a1 * a2 * Real.cos (α - β) := by
  rw [← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  rw [Real.cos_sub]
  nlinarith [Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β]

theorem sinusoidal_probability (Wk σk a1 a2 φ1 φ2 ω ωp ωm : ℝ)
    (hω : ωp - ωm = 2 * ω) (t : ℝ) :
    Wk * (σk + ‖(a1 : ℂ) * Complex.exp (((φ1 + ωp * t : ℝ) : ℂ) * Complex.I)
              - (a2 : ℂ) * Complex.exp (((φ2 + ωm * t : ℝ) : ℂ) * Complex.I)‖ ^ 2)
      = Wk * (a1 ^ 2 + a2 ^ 2 + σk)
        - 2 * Wk * a1 * a2 * Real.cos (2 * (ω * t + (φ1 - φ2) / 2)) := by
  have h1 : ωp * t - ωm * t = 2 * ω * t := by rw [← sub_mul, hω]
  have hrew : (φ1 + ωp * t) - (φ2 + ωm * t) = 2 * (ω * t + (φ1 - φ2) / 2) := by
    linarith [h1]
  rw [normSq_phase_diff a1 a2 (φ1 + ωp * t) (φ2 + ωm * t), hrew]
  ring

theorem cos_deviation_exact (β γ : ℝ) (ω Wk Wl : ℝ → ℝ)
    (hcos : ∀ w, Real.cos (ω w)
      = Wk w * Real.cos ((β + γ) / 2) + Wl w * Real.cos ((β - γ) / 2))
    (hsum : ∀ w, Wk w + Wl w = 1) (w : ℝ) :
    Real.cos (ω w) - Real.cos ((β - γ) / 2)
      = Wk w * (Real.cos ((β + γ) / 2) - Real.cos ((β - γ) / 2)) := by
  rw [hcos w]
  linear_combination (Real.cos ((β - γ) / 2)) * (hsum w)

theorem distinct_angle_frequency_limit (β γ : ℝ) (ω Wk Wl : ℝ → ℝ)
    (hcos : ∀ w, Real.cos (ω w)
      = Wk w * Real.cos ((β + γ) / 2) + Wl w * Real.cos ((β - γ) / 2))
    (hsum : ∀ w, Wk w + Wl w = 1)
    (hWk : Tendsto Wk (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hω : ∀ w, ω w ∈ Set.Icc (0 : ℝ) Real.pi)
    (hB : |β - γ| / 2 ∈ Set.Icc (0 : ℝ) Real.pi) :
    Tendsto ω (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (|β - γ| / 2)) := by
  let F : Filter ℝ := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  have hclim : Tendsto (fun w => Real.cos (ω w)) F (nhds (Real.cos ((β - γ) / 2))) := by
    have heq : (fun w => Real.cos (ω w)) =ᶠ[F]
        (fun w => Real.cos ((β - γ) / 2)
          + Wk w * (Real.cos ((β + γ) / 2) - Real.cos ((β - γ) / 2))) :=
      Filter.Eventually.of_forall (fun w => by
        beta_reduce
        rw [hcos w]
        linear_combination (Real.cos ((β - γ) / 2)) * (hsum w))
    rw [tendsto_congr' heq]
    simpa using tendsto_const_nhds.add (hWk.mul_const _)
  have hcomp : Tendsto (fun w => Real.arccos (Real.cos (ω w))) F
      (nhds (Real.arccos (Real.cos ((β - γ) / 2)))) :=
    (Real.continuous_arccos.tendsto (Real.cos ((β - γ) / 2))).comp hclim
  have hωeq : (fun w => ω w) =ᶠ[F] (fun w => Real.arccos (Real.cos (ω w))) :=
    Filter.Eventually.of_forall (fun w => (Real.arccos_cos (hω w).1 (hω w).2).symm)
  rw [tendsto_congr' hωeq]
  have hval : Real.arccos (Real.cos ((β - γ) / 2)) = |β - γ| / 2 := by
    have hB' : |(β - γ) / 2| ∈ Set.Icc (0 : ℝ) Real.pi := by
      have he : |(β - γ) / 2| = |β - γ| / 2 := by rw [abs_div]; norm_num
      rw [he]; exact hB
    have hcosabs : Real.cos |(β - γ) / 2| = Real.cos ((β - γ) / 2) := by
      by_cases h : 0 ≤ (β - γ) / 2
      · rw [abs_of_nonneg h]
      · rw [abs_of_neg (not_le.mp h), Real.cos_neg]
    calc Real.arccos (Real.cos ((β - γ) / 2))
        = Real.arccos (Real.cos |(β - γ) / 2|) := by rw [hcosabs]
      _ = |(β - γ) / 2| := Real.arccos_cos hB'.1 hB'.2
      _ = |β - γ| / 2 := by rw [abs_div]; norm_num
  rw [← hval]
  exact hcomp

theorem deltaP_sqrt_bound (W a b C1 C2 : ℝ) (hW : 0 < W)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (ha1 : a ≤ C1) (hb2 : b ≤ C2 / Real.sqrt W) :
    2 * W * a * b ≤ 2 * C1 * C2 * Real.sqrt W := by
  have hs : 0 < Real.sqrt W := Real.sqrt_pos.mpr hW
  have hW0 : 0 ≤ W := le_of_lt hW
  have hab : a * b ≤ C1 * C2 / Real.sqrt W := by
    have h := mul_le_mul ha1 hb2 hb hC1
    calc a * b ≤ C1 * (C2 / Real.sqrt W) := h
      _ = C1 * C2 / Real.sqrt W := by ring
  have hstep : 2 * W * (a * b) ≤ 2 * W * (C1 * C2 / Real.sqrt W) :=
    mul_le_mul_of_nonneg_left hab (by nlinarith [hW])
  have hdiv : W / Real.sqrt W = Real.sqrt W := by
    rw [div_eq_iff (ne_of_gt hs), ← pow_two, Real.sq_sqrt hW0]
  calc 2 * W * a * b = 2 * W * (a * b) := by ring
    _ ≤ 2 * W * (C1 * C2 / Real.sqrt W) := hstep
    _ = 2 * C1 * C2 * Real.sqrt W := by
          rw [show 2 * W * (C1 * C2 / Real.sqrt W)
                = 2 * (C1 * C2) * (W / Real.sqrt W) by ring]
          rw [hdiv]; ring

theorem distinct_angle_fails (Pav ΔP Pinit : ℝ) (hΔ : 0 ≤ ΔP) (hP : |Pinit - Pav| ≤ ΔP) :
    ∀ t : ℝ, Pav - ΔP ≤ Pav - ΔP * Real.cos t := by
  intro t
  have hle : Real.cos t ≤ 1 := Real.cos_le_one t
  have h1 : ΔP * Real.cos t ≤ ΔP * 1 := mul_le_mul_of_nonneg_left hle hΔ
  linarith [h1]

theorem abs_sum_sq_identity (a b : ℂ) :
    (‖a + b‖ + ‖a - b‖) ^ 2
      = 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖a ^ 2 - b ^ 2‖) := by
  have h1 : ‖a + b‖ * ‖a - b‖ = ‖a ^ 2 - b ^ 2‖ := by
    rw [← Complex.norm_mul]; congr 1; ring
  have h2 : ‖a + b‖ ^ 2 + ‖a - b‖ ^ 2 = 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.sq_norm]

    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im,
      Complex.normSq_apply, Complex.ofReal_re, Complex.ofReal_im]
    ring
  nlinarith [h1, h2]

theorem pmax_upper_bound (Wl σl A B θ : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    1 - Wl * σl - A / 2 - B / 2
        + (1 / 2) * ‖(A : ℂ) * Complex.exp (θ * Complex.I) + (B : ℂ)‖
      ≤ 1 - Wl * σl := by
  have hnorm : ‖(A : ℂ) * Complex.exp (θ * Complex.I) + (B : ℂ)‖ ≤ A + B := by
    have hsplit : ‖(A : ℂ) * Complex.exp (θ * Complex.I) + (B : ℂ)‖
        ≤ ‖(A : ℂ) * Complex.exp (θ * Complex.I)‖ + ‖(B : ℂ)‖ := norm_add_le _ _
    have hAn : ‖(A : ℂ) * Complex.exp (θ * Complex.I)‖ = A := by
      rw [Complex.norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hA]
    have hBn : ‖(B : ℂ)‖ = B := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hB]
    linarith [hsplit, hAn, hBn]
  nlinarith [hnorm]

theorem pmax_upper_bound_attained (Wl σl A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    1 - Wl * σl - A / 2 - B / 2
        + (1 / 2) * ‖(A : ℂ) * Complex.exp (0 * Complex.I) + (B : ℂ)‖
      = 1 - Wl * σl := by
  simp only [zero_mul, Complex.exp_zero, mul_one]
  have hAB : (A : ℂ) + (B : ℂ) = ((A + B : ℝ) : ℂ) := by push_cast; ring
  rw [hAB, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  ring

noncomputable def pmaxClosed (Wl σl a b θ : ℝ) (Wk : ℝ) : ℝ :=
  1 - Wl * σl - (1 / 2) * Wl * (a * a) - (1 / 2) * Wk * (b * b)
    + (1 / 2) * ‖(Wl * (a * a) : ℂ) * Complex.exp (θ * Complex.I) + (Wk * (b * b) : ℂ)‖

theorem phase_adjust (ψ αk αl : ℝ) (h : ψ = αk - αl) :
    Complex.exp ((2 * (ψ + αl - αk) : ℝ) * Complex.I) = 1 := by
  have h0 : 2 * (ψ + αl - αk) = 0 := by linarith
  rw [h0, Complex.ofReal_zero, zero_mul, Complex.exp_zero]

theorem pmax_optimal_one (Wk Wl : ℝ) (hsum : Wk + Wl = 1) :
    pmaxClosed Wl 0 1 1 0 Wk = 1 := by
  unfold pmaxClosed
  simp only [Complex.ofReal_one, mul_one, mul_zero, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero]
  have hnorm : ‖(Wl : ℂ) + (Wk : ℂ)‖ = 1 := by
    have hc : (Wl : ℂ) + (Wk : ℂ) = ((Wl + Wk : ℝ) : ℂ) := by push_cast; ring
    have hsum' : Wl + Wk = 1 := by linarith
    rw [hc, hsum']
    simp
  rw [hnorm]
  nlinarith [hsum]

theorem optimal_iteration_value (φ ω T : ℝ) (hω : ω ≠ 0)
    (hT : 2 * (ω * T + φ) = Real.pi) :
    T = (Real.pi - 2 * φ) / (2 * ω) := by
  field_simp at hT ⊢
  linarith

theorem optimal_iteration_maximizes (Pav ΔP φ ω T : ℝ) (hΔ : 0 ≤ ΔP)
    (hT : 2 * (ω * T + φ) = Real.pi) :
    (∀ t : ℝ, Pav - ΔP * Real.cos (2 * (ω * t + φ)) ≤ Pav + ΔP) ∧
      Pav - ΔP * Real.cos (2 * (ω * T + φ)) = Pav + ΔP := by
  constructor
  · intro t
    have hc : -1 ≤ Real.cos (2 * (ω * t + φ)) := Real.neg_one_le_cos _
    nlinarith
  · rw [hT, Real.cos_pi]; ring

theorem one_sub_cos_two_sin_sq (x : ℝ) : 1 - Real.cos x = 2 * Real.sin (x / 2) ^ 2 := by
  have h := Real.cos_two_mul (x / 2)
  have h2 : Real.cos x = 2 * Real.cos (x / 2) ^ 2 - 1 := by
    have hx : 2 * (x / 2) = x := by ring
    rwa [hx] at h
  have hs := Real.sin_sq_add_cos_sq (x / 2)
  nlinarith [h2, hs]

theorem identical_angle_cos (β : ℝ) (ω Wk Wl : ℝ → ℝ)
    (hcos : ∀ w, Real.cos (ω w)
      = Wk w * Real.cos ((β + β) / 2) + Wl w * Real.cos ((β - β) / 2))
    (hsum : ∀ w, Wk w + Wl w = 1) (w : ℝ) :
    Real.cos (ω w) = 1 - Wk w * (1 - Real.cos β) := by
  have h := hcos w
  have hsumw := hsum w
  have h1 : (β + β) / 2 = β := by ring
  have h2 : (β - β) / 2 = 0 := by ring
  rw [h1, h2, Real.cos_zero] at h
  nlinarith [h, hsumw]

theorem identical_angle_sin_half (β : ℝ) (ω Wk Wl : ℝ → ℝ)
    (hcos : ∀ w, Real.cos (ω w)
      = Wk w * Real.cos ((β + β) / 2) + Wl w * Real.cos ((β - β) / 2))
    (hsum : ∀ w, Wk w + Wl w = 1) (w : ℝ) :
    Real.sin (ω w / 2) ^ 2 = Wk w * Real.sin (β / 2) ^ 2 := by
  have hc := identical_angle_cos β ω Wk Wl hcos hsum w
  have h1 : 1 - Real.cos (ω w) = 2 * Real.sin (ω w / 2) ^ 2 :=
    one_sub_cos_two_sin_sq (ω w)
  have h2 : 1 - Real.cos β = 2 * Real.sin (β / 2) ^ 2 := one_sub_cos_two_sin_sq β
  have h3 : 1 - Real.cos (ω w) = Wk w * (1 - Real.cos β) := by linarith [hc]
  rw [h2] at h3
  linarith [h1, h3]

theorem sin_half_eq_sqrt (β ω Wk : ℝ)
    (h : Real.sin (ω / 2) ^ 2 = Wk * Real.sin (β / 2) ^ 2)
    (hWk : 0 ≤ Wk) (hβ : 0 ≤ Real.sin (β / 2))
    (hω0 : 0 ≤ ω / 2) (hωπ : ω / 2 ≤ Real.pi) :
    Real.sin (ω / 2) = Real.sin (β / 2) * Real.sqrt Wk := by
  have hωs : 0 ≤ Real.sin (ω / 2) := Real.sin_nonneg_of_nonneg_of_le_pi hω0 hωπ
  have hr : 0 ≤ Real.sin (β / 2) * Real.sqrt Wk := mul_nonneg hβ (Real.sqrt_nonneg _)
  have hR : (Real.sin (β / 2) * Real.sqrt Wk) ^ 2 = Wk * Real.sin (β / 2) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hWk]; ring
  calc Real.sin (ω / 2) = |Real.sin (ω / 2)| := (abs_of_nonneg hωs).symm
    _ = Real.sqrt (Real.sin (ω / 2) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ = Real.sqrt ((Real.sin (β / 2) * Real.sqrt Wk) ^ 2) := by rw [h, hR]
    _ = |Real.sin (β / 2) * Real.sqrt Wk| := Real.sqrt_sq_eq_abs _
    _ = Real.sin (β / 2) * Real.sqrt Wk := abs_of_nonneg hr

theorem omega_eq_two_arcsin (β ω Wk : ℝ)
    (hω0 : 0 ≤ ω / 2) (hωπ : ω / 2 ≤ Real.pi / 2)
    (h : Real.sin (ω / 2) = Real.sin (β / 2) * Real.sqrt Wk) :
    ω = 2 * Real.arcsin (Real.sin (β / 2) * Real.sqrt Wk) := by
  have hx : Real.arcsin (Real.sin (ω / 2)) = ω / 2 :=
    Real.arcsin_sin (by linarith [Real.pi_pos]) hωπ
  rw [h] at hx
  linarith [hx]

theorem two_measurement_half_max (Pav ΔP φ ω T1 : ℝ) (hω : ω ≠ 0) (hΔ : 0 ≤ ΔP)
    (hbound : ΔP ≤ Pav) :
    Pav - ΔP * Real.cos (2 * (ω * T1 + φ)) ≥ (Pav + ΔP) / 2 ∨
      Pav - ΔP * Real.cos (2 * (ω * (T1 + Real.pi / (2 * ω)) + φ)) ≥ (Pav + ΔP) / 2 := by
  by_cases hc : Real.cos (2 * (ω * T1 + φ)) ≤ 0
  · left
    have hcos : ΔP * Real.cos (2 * (ω * T1 + φ)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hΔ hc
    nlinarith
  · right
    rw [not_le] at hc

    have harg : 2 * (ω * (T1 + Real.pi / (2 * ω)) + φ) = 2 * (ω * T1 + φ) + Real.pi := by
      field_simp
      ring
    rw [harg, Real.cos_add_pi]
    have hcos : 0 ≤ ΔP * Real.cos (2 * (ω * T1 + φ)) := mul_nonneg hΔ (le_of_lt hc)
    nlinarith

end Qatlib.Papers.RecurGrover00.MainResults
