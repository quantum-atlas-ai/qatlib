/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.UnbiasedBases.ExclusionCheck.MUB6PhaseEnclosure
public import Qatlib.Concepts.UnbiasedBases.ThreeBasis.MUBNormalization
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

@[expose] public section
open Qatlib.Foundations.PureStateMath Qatlib.Concepts.UnbiasedBases.ThreeBasis Qatlib.Concepts.UnbiasedBases.ThreeBasis.MUB
open Qatlib.Concepts.UnbiasedBases.ExclusionCheck

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.UnbiasedBases.ThreeBasis Qatlib.Concepts.UnbiasedBases.ThreeBasis

namespace Qatlib.Concepts.UnbiasedBases.ExclusionCheck
open Qatlib.Concepts.UnbiasedBases.ThreeBasis Qatlib.Concepts.UnbiasedBases.ThreeBasis
open Qatlib.Concepts.UnbiasedBases.ExclusionCheck
open scoped BigOperators
abbrev Phase6 := Fin 6 → ℝ
noncomputable def cycleVector (v : Phase6) : QState (Fin 6) :=
  fun j => (sixthAmplitude : ℂ) * phase (2*Real.pi*v j)

/-- Expresses the inner product of two cycle vectors with a common base phase as one sixth of
the sum of relative phases. -/
theorem cycle_inner (v x y : Phase6) :
    Inner (cycleVector (v+x)) (cycleVector (v+y)) =
      (1/6 : ℂ) * ∑ j, phase (2*Real.pi*(y j-x j)) := by
  change Inner (fun j => (sixthAmplitude : ℂ)*phase (2*Real.pi*(v+x) j))
    (fun j => (sixthAmplitude : ℂ)*phase (2*Real.pi*(v+y) j)) = _
  rw [inner_rephase,sixthAmplitude_conj_mul,inner_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  unfold phase
  rw [← Complex.exp_conj,map_mul,Complex.conj_I,Complex.conj_ofReal,← Complex.exp_add]
  congr 1
  simp only [Pi.add_apply]
  push_cast
  ring

/-- Bounds the sum of absolute coordinate displacements by one half for two phase vectors in the
stated small Euclidean ball. -/
theorem displacement_l1 (x y : Phase6) (s : ℝ) (hs : 0 ≤ s) (hsmall : s < 1/10)
    (hx : ∑ j, x j^2 ≤ s^2) (hy : ∑ j, y j^2 ≤ s^2) :
    ∑ j, |y j-x j| < (1 : ℝ)/2 := by
  have hsq : ∑ j, (y j-x j)^2 ≤ 4*s^2 := by
    calc
      _ ≤ ∑ j : Fin 6, (2*(y j)^2+2*(x j)^2) := by
        apply Finset.sum_le_sum
        intro j _
        nlinarith [sq_nonneg (y j+x j)]
      _ = 2*(∑ j, y j^2)+2*(∑ j, x j^2) := by
        simp [Finset.sum_add_distrib,Finset.mul_sum]
      _ ≤ _ := by linarith
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun j : Fin 6 => |y j-x j|) (fun _ => (1 : ℝ))
  simp only [mul_one,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,Nat.cast_ofNat,mul_one,sq_abs] at hcs
  have hss : s^2 < (1 : ℝ)/100 := by
    nlinarith [mul_pos (sub_pos.mpr hsmall) (show 0 < 1/10+s by linarith)]
  nlinarith

/-- Shows that the norm of the relative-phase sum is greater than twenty sevenths under the
small-ball assumptions. -/
theorem raw_same_ball_gap (x y : Phase6) (s : ℝ) (hs : 0 ≤ s) (hsmall : s < 1/10)
    (hx : ∑ j, x j^2 ≤ s^2) (hy : ∑ j, y j^2 ≤ s^2) :
    (20 : ℝ)/7 < ‖∑ j, phase (2*Real.pi*(y j-x j))‖ := by
  have hl := displacement_l1 x y s hs hsmall hx hy
  have he (j : Fin 6) : ‖phase (2*Real.pi*(y j-x j))-1‖ ≤ 2*Real.pi*|y j-x j| := by
    have h := phase_distance (2*Real.pi*(y j-x j)) 0
    simpa [phase,abs_mul,abs_of_pos Real.pi_pos] using h
  have hsum : ‖(∑ j, phase (2*Real.pi*(y j-x j)))-(6 : ℂ)‖ ≤
      2*Real.pi*(∑ j, |y j-x j|) := by
    calc
      _ = ‖∑ j : Fin 6, (phase (2*Real.pi*(y j-x j))-1)‖ := by
        simp [Finset.sum_sub_distrib]
      _ ≤ ∑ j : Fin 6, ‖phase (2*Real.pi*(y j-x j))-1‖ := norm_sum_le _ _
      _ ≤ ∑ j : Fin 6, 2*Real.pi*|y j-x j| := Finset.sum_le_sum (fun j _ => he j)
      _ = _ := by rw [Finset.mul_sum]
  have ht := norm_sub_norm_le (6 : ℂ) (∑ j, phase (2*Real.pi*(y j-x j)))
  rw [norm_sub_rev] at ht
  norm_num at ht
  have hh := mul_lt_mul_of_pos_left hl (show 0 < 2*Real.pi by positivity)
  have hp : Real.pi < 22/7 := Real.pi_lt_d20.trans (by norm_num)
  linarith

/-- Shows that phase-scaled cycle vectors in the same small ball have squared inner product
greater than one sixth. -/
theorem same_ball_normSq_gap (v x y : Phase6) (s : ℝ)
    (hs : 0 ≤ s) (hsmall : s < 1/10) (hx : ∑ j, x j^2 ≤ s^2) (hy : ∑ j, y j^2 ≤ s^2)
    (c d : ℂ) (hc : Complex.normSq c=1) (hd : Complex.normSq d=1) :
    (1 : ℝ)/6 < Complex.normSq (Inner (fun i => c*cycleVector (v+x) i)
      (fun i => d*cycleVector (v+y) i)) := by
  rw [inner_rephase,Complex.normSq_mul,Complex.normSq_mul,Complex.normSq_conj,hc,hd,one_mul,one_mul,
    cycle_inner,Complex.normSq_mul]
  have h := raw_same_ball_gap x y s hs hsmall hx hy
  norm_num
  rw [Complex.normSq_eq_norm_sq]
  nlinarith
end Qatlib.Concepts.UnbiasedBases.ExclusionCheck
