/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import Qatlib.Papers.AnalogDigital96.MainResults.EvolutionBridge

/-!
# Analog quantum search from the Hamiltonian exponential

The Hamiltonian `analogHamiltonian` is the energy-scaled sum of the starting and target rank-one
matrices. Its sum and difference relations give an exact transition amplitude and Born
probability, leading to certain success at the resonant time and a uniform-start specialization.
This development supports the treatment in [FarhiGutmann1998a].

## Main statements

* `analog_search_probability`: the exact probability formula at time `t`.
* `analog_search_probability_at_tm`: probability one at `π/(2 * E * x)`.
* `uniform_search_success`: every basis target is found at time `π * sqrt(N)/(2 * E)`.

## References

* [Farhi and Gutmann, 1998][FarhiGutmann1998a]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Papers.AnalogDigital96.MainResults
open scoped BigOperators Matrix

namespace Qatlib.Papers.AnalogDigital96.MainResults.AnalogSearch

local notation "qInner" => Qatlib.Foundations.PureStateMath.Inner

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The analog search Hamiltonian given by `E` times the sum of the rank-one matrices associated
with `w` and `s`. -/
def analogHamiltonian (E : ℝ) (s w : QState I) : Matrix I I ℂ :=
  (E : ℂ) • (outerProduct w + outerProduct s)

omit [Fintype I] [DecidableEq I] in

/-- The analog search Hamiltonian is Hermitian for real energy `E` and arbitrary starting and
target vectors. -/
theorem analogHamiltonian_isHermitian (E : ℝ) (s w : QState I) :
    (analogHamiltonian E s w).IsHermitian := by
  unfold analogHamiltonian
  have hE : IsSelfAdjoint (E : ℂ) := by
    show star (E : ℂ) = (E : ℂ)
    rw [RCLike.star_def, Complex.conj_ofReal]
  exact Matrix.IsHermitian.smul ((outerProduct_isHermitian w).add
    (outerProduct_isHermitian s)) hE

/-- For normalized `s` and `w` with real overlap `x`, the vector `s + w` satisfies the
eigenvalue relation with value `E * (1 + x)`. -/
theorem analogHamiltonian_eigen_plus (E x : ℝ) (s w : QState I)
    (hs : Normalized s) (hw : Normalized w) (hsw : qInner s w = (x : ℂ)) :
    analogHamiltonian E s w *ᵥ (s + w) = ((E * (1 + x) : ℝ) : ℂ) • (s + w) := by
  have hss : qInner s s = 1 := (normalized_iff_inner_self s).1 hs
  have hww : qInner w w = 1 := (normalized_iff_inner_self w).1 hw
  have hws : qInner w s = (x : ℂ) := by
    rw [← inner_conj_state, hsw, RCLike.star_def, Complex.conj_ofReal]
  unfold analogHamiltonian
  rw [Matrix.smul_mulVec, Matrix.add_mulVec,
    outerProduct_mulVec, outerProduct_mulVec,
    inner_add_state, inner_add_state, hws, hww, hss, hsw]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

/-- For normalized `s` and `w` with real overlap `x`, the vector `s - w` satisfies the
eigenvalue relation with value `E * (1 - x)`. -/
theorem analogHamiltonian_eigen_minus (E x : ℝ) (s w : QState I)
    (hs : Normalized s) (hw : Normalized w) (hsw : qInner s w = (x : ℂ)) :
    analogHamiltonian E s w *ᵥ (s - w) = ((E * (1 - x) : ℝ) : ℂ) • (s - w) := by
  have hss : qInner s s = 1 := (normalized_iff_inner_self s).1 hs
  have hww : qInner w w = 1 := (normalized_iff_inner_self w).1 hw
  have hws : qInner w s = (x : ℂ) := by
    rw [← inner_conj_state, hsw, RCLike.star_def, Complex.conj_ofReal]
  unfold analogHamiltonian
  rw [Matrix.smul_mulVec, Matrix.add_mulVec,
    outerProduct_mulVec, outerProduct_mulVec,
    inner_sub_state, inner_sub_state, hws, hww, hss, hsw]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

/-- The half-weighted combination of the two spectral phases equals `exp(-I * t * E) * (x *
cos(E * x * t) - I * sin(E * x * t))`. -/
theorem phase_combination (E x t : ℝ) :
    (2⁻¹ : ℂ) * (Complex.exp ((-Complex.I * (t : ℂ)) * ((E * (1 + x) : ℝ) : ℂ)) *
        ((x : ℂ) + 1)) +
      (2⁻¹ : ℂ) * (Complex.exp ((-Complex.I * (t : ℂ)) * ((E * (1 - x) : ℝ) : ℂ)) *
        ((x : ℂ) - 1)) =
    Complex.exp ((-Complex.I * (t : ℂ)) * (E : ℂ)) *
      ((x : ℂ) * (Real.cos (E * x * t) : ℂ) - (Real.sin (E * x * t) : ℂ) * Complex.I) := by
  have ha : (-Complex.I * (t : ℂ)) * ((E * (1 + x) : ℝ) : ℂ) =
      (-Complex.I * (t : ℂ)) * (E : ℂ) + ((-(E * x * t) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have hb : (-Complex.I * (t : ℂ)) * ((E * (1 - x) : ℝ) : ℂ) =
      (-Complex.I * (t : ℂ)) * (E : ℂ) + ((E * x * t : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [ha, hb, Complex.exp_add, Complex.exp_add, Complex.exp_ofReal_mul_I,
    Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
  push_cast
  ring

/-- For normalized starting and target states with real overlap `x`, the evolved target
amplitude is `exp(-I * t * E) * (x * cos(E * x * t) - I * sin(E * x * t))`
[FarhiGutmann1998a]. -/
theorem analogEvolution_amplitude (E x t : ℝ) (s w : QState I)
    (hs : Normalized s) (hw : Normalized w) (hsw : qInner s w = (x : ℂ)) :
    qInner w (HamiltonianEvolution (analogHamiltonian E s w) t *ᵥ s) =
      Complex.exp ((-Complex.I * (t : ℂ)) * (E : ℂ)) *
        ((x : ℂ) * (Real.cos (E * x * t) : ℂ) - (Real.sin (E * x * t) : ℂ) * Complex.I) := by
  have hss : qInner s s = 1 := (normalized_iff_inner_self s).1 hs
  have hww : qInner w w = 1 := (normalized_iff_inner_self w).1 hw
  have hws : qInner w s = (x : ℂ) := by
    rw [← inner_conj_state, hsw, RCLike.star_def, Complex.conj_ofReal]
  have hs_eq : s = (2⁻¹ : ℂ) • (s + w) + (2⁻¹ : ℂ) • (s - w) := by
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  set H : Matrix I I ℂ := analogHamiltonian E s w with hH
  have hplus : H *ᵥ (s + w) = ((E * (1 + x) : ℝ) : ℂ) • (s + w) := by
    rw [hH]; exact analogHamiltonian_eigen_plus E x s w hs hw hsw
  have hminus : H *ᵥ (s - w) = ((E * (1 - x) : ℝ) : ℂ) • (s - w) := by
    rw [hH]; exact analogHamiltonian_eigen_minus E x s w hs hw hsw
  have hmain : HamiltonianEvolution H t *ᵥ s =
      (2⁻¹ : ℂ) • (Complex.exp ((-Complex.I * (t : ℂ)) * ((E * (1 + x) : ℝ) : ℂ)) • (s + w)) +
        (2⁻¹ : ℂ) • (Complex.exp ((-Complex.I * (t : ℂ)) * ((E * (1 - x) : ℝ) : ℂ)) • (s - w)) := by
    nth_rewrite 1 [hs_eq]
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      hamiltonianEvolution_eigenvector H (s + w) (E * (1 + x)) t hplus,
      hamiltonianEvolution_eigenvector H (s - w) (E * (1 - x)) t hminus]
  rw [hmain]
  simp only [inner_add_state, inner_sub_state, inner_smul_state, hws, hww]
  exact phase_combination E x t

/-- For normalized states with real overlap `x`, the target probability at time `t` is `sin(E *
x * t)^2 + x^2 * cos(E * x * t)^2` [Farhi and Gutmann, Eq. 11][FarhiGutmann1998a]. -/
theorem analog_search_probability (E x t : ℝ) (s w : QState I)
    (hs : Normalized s) (hw : Normalized w) (hsw : qInner s w = (x : ℂ)) :
    ‖qInner w (HamiltonianEvolution (analogHamiltonian E s w) t *ᵥ s)‖ ^ 2 =
      Real.sin (E * x * t) ^ 2 + x ^ 2 * Real.cos (E * x * t) ^ 2 := by
  rw [analogEvolution_amplitude E x t s w hs hw hsw]
  have hexp : ‖Complex.exp ((-Complex.I * (t : ℂ)) * (E : ℂ))‖ = 1 := by
    rw [show (-Complex.I * (t : ℂ)) * (E : ℂ) = ((-(E * t) : ℝ) : ℂ) * Complex.I by
      push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [norm_mul, hexp, one_mul]
  have hz : (x : ℂ) * (Real.cos (E * x * t) : ℂ) - (Real.sin (E * x * t) : ℂ) * Complex.I =
      ((x * Real.cos (E * x * t) : ℝ) : ℂ) + ((-Real.sin (E * x * t) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hz, ← Complex.normSq_eq_norm_sq, Complex.normSq_add_mul_I]
  ring

/-- For positive energy and positive real overlap `x`, the normalized-state target probability
is one at time `π/(2 * E * x)` [Farhi and Gutmann, Eq. 12][FarhiGutmann1998a]. -/
theorem analog_search_probability_at_tm (E x : ℝ) (s w : QState I)
    (hs : Normalized s) (hw : Normalized w) (hsw : qInner s w = (x : ℂ))
    (hE : 0 < E) (hx : 0 < x) :
    ‖qInner w (HamiltonianEvolution (analogHamiltonian E s w) (Real.pi / (2 * E * x)) *ᵥ s)‖ ^ 2 =
      1 := by
  rw [analog_search_probability E x (Real.pi / (2 * E * x)) s w hs hw hsw]
  have harg : E * x * (Real.pi / (2 * E * x)) = Real.pi / 2 := by
    field_simp
  rw [harg, Real.sin_pi_div_two, Real.cos_pi_div_two]
  ring

/-- The average squared overlap of a normalized state with the columns of a unitary matrix is
the reciprocal of the positive dimension [FarhiGutmann1998a]. -/
theorem basis_overlap_average (V : Matrix I I ℂ) (hV : V ∈ Matrix.unitaryGroup I ℂ)
    (w : QState I) (hw : Normalized w) (_hN : 0 < Fintype.card I) :
    (∑ i, ‖qInner (fun j => V j i) w‖ ^ 2) / (Fintype.card I : ℝ) =
      1 / (Fintype.card I : ℝ) := by
  rw [spectral_weights_sum V w hV hw]

/-- For positive energy and dimension parameter, substituting overlap `1/sqrt N` gives search
time `π * sqrt N/(2 * E)`. -/
theorem search_time_typical (E N : ℝ) (hE : 0 < E) (hN : 0 < N) :
    Real.pi / (2 * E * (1 / Real.sqrt N)) = Real.pi * Real.sqrt N / (2 * E) := by
  have hsqrt : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  have hden : 2 * E * (1 / Real.sqrt N) = 2 * E / Real.sqrt N := by ring
  rw [hden]
  field_simp [hsqrt.ne', hE.ne']

/-- For positive `E` and `N` with `1/sqrt N ≤ x ≤ 1`, the search time `π/(2 * E * x)` lies
between `π/(2 * E)` and `π * sqrt N/(2 * E)`. -/
theorem search_time_order (E x N : ℝ) (hE : 0 < E) (hN : 0 < N)
    (hx_low : 1 / Real.sqrt N ≤ x) (hx_high : x ≤ 1) :
    Real.pi / (2 * E) ≤ Real.pi / (2 * E * x) ∧
      Real.pi / (2 * E * x) ≤ Real.pi * Real.sqrt N / (2 * E) := by
  have hsqrt : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx_low
  constructor
  · exact div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤ Real.pi)
      (by positivity : (0 : ℝ) < 2 * E * x) (by nlinarith [hx_high, hE])
  · have hxinv : 1 / x ≤ Real.sqrt N := by
      rw [div_le_iff₀ hx0]
      calc (1 : ℝ) = Real.sqrt N * (1 / Real.sqrt N) := by field_simp
        _ ≤ Real.sqrt N * x := mul_le_mul_of_nonneg_left hx_low hsqrt.le
    calc Real.pi / (2 * E * x) = (Real.pi / (2 * E)) * (1 / x) := by
          field_simp
      _ ≤ (Real.pi / (2 * E)) * Real.sqrt N :=
          mul_le_mul_of_nonneg_left hxinv (by positivity)
      _ = Real.pi * Real.sqrt N / (2 * E) := by ring

/-- The overlap of the uniform state with any basis target is the real scalar `1/sqrt(card I)`
embedded in the complex numbers. -/
theorem uniform_target_overlap (w : I) :
    qInner (Uniform I) (Ket w) = ((1 / Real.sqrt (Fintype.card I) : ℝ) : ℂ) := by
  simp [Qatlib.Foundations.PureStateMath.Inner, Uniform, Ket, dotProduct]

/-- Hamiltonian evolution under the analog search Hamiltonian preserves normalization of the
starting state [FarhiGutmann1998a]. -/
theorem analog_search_normalized (E t : ℝ) (s w : QState I) (hs : Normalized s) :
    Normalized (HamiltonianEvolution (analogHamiltonian E s w) t *ᵥ s) := by
  exact normalized_applyGate
      (hamiltonianEvolution_unitary (analogHamiltonian_isHermitian E s w) t) hs

/-- Starting from the uniform state, every basis target has Born probability one at time `π *
sqrt(card I)/(2 * E)` when `E > 0` [FarhiGutmann1998a]. -/
theorem uniform_search_success (w : I) (E : ℝ) (hE : 0 < E) :
    BornProb (HamiltonianEvolution (analogHamiltonian E (Uniform I) (Ket w))
      (Real.pi * Real.sqrt (Fintype.card I) / (2 * E)) *ᵥ Uniform I) w = 1 := by
  have hN : 0 < Fintype.card I := Fintype.card_pos_iff.mpr ⟨w⟩
  have hNr : (0 : ℝ) < Fintype.card I := by exact_mod_cast hN
  have hx : (0 : ℝ) < 1 / Real.sqrt (Fintype.card I) := by positivity
  have ht := search_time_typical E (Fintype.card I) hE hNr
  have hp := analog_search_probability_at_tm E (1 / Real.sqrt (Fintype.card I))
    (Uniform I) (Ket w) (normalized_uniform hN) (normalized_ket w)
    (uniform_target_overlap w) hE hx
  rw [ht] at hp
  have he (v : QState I) : qInner (Ket w) v = v w := by
    simp [Qatlib.Foundations.PureStateMath.Inner, Ket, dotProduct]
  simpa only [he, BornProb] using hp

end Qatlib.Papers.AnalogDigital96.MainResults.AnalogSearch
