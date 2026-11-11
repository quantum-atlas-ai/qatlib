/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ContDiscWalk08.SineReadout.FidelityCore
import Qatlib.Papers.ContDiscWalk08.CompressedSim.CompressedSymbol

/-!
# Sine-phase readout operators and overlaps

The definitions `sinePhase`, `sineWindowMatrix`, `idealVec`, and `simVec` model diagonal
sine-phase readout and the resulting state vectors. The module computes their overlap and bounds
its real part using a weighted phase-error second moment, following the readout analysis of
[Childs2010].

## Main statements

* `sineWindowMatrix_mem_unitary`: the diagonal phase matrix is unitary.
* `readout_fidelity_ge`: a quadratic lower bound on the real overlap.
* `readout_fidelity_of_variance`: the variance estimate yields the constant `93` bound.

## References

* [Childs, 2010][Childs2010]
-/

set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

noncomputable section

open Matrix Qatlib.Foundations.PureStateMath
open scoped ComplexConjugate

namespace Qatlib.Papers.ContDiscWalk08.SineReadout

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Defines the complex phase `exp(-i * t * sin φ)`. -/
def sinePhase (t φ : ℝ) : ℂ :=
  Complex.exp (-(Complex.I * ((t * Real.sin φ : ℝ) : ℂ)))

/-- The sine phase has norm one. -/
theorem sinePhase_norm (t φ : ℝ) : ‖sinePhase t φ‖ = 1 := by
  unfold sinePhase
  rw [Complex.norm_exp]
  have hre : (-(Complex.I * ((t * Real.sin φ : ℝ) : ℂ))).re = 0 := by simp
  rw [hre, Real.exp_zero]

/-- Adding the time parameters multiplies the corresponding sine phases. -/
theorem sinePhase_add (t u φ : ℝ) : sinePhase (t + u) φ = sinePhase t φ * sinePhase u φ := by
  unfold sinePhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The distance between two sine phases at time `t` is at most `|t| * |θ - φ|`. This is the
scalar continuity estimate used in [Childs2010]. -/
theorem sinePhase_sub_bound (t θ φ : ℝ) :
    ‖sinePhase t θ - sinePhase t φ‖ ≤ |t| * |θ - φ| := by
  have hcore :=
      Qatlib.Papers.ContDiscWalk08.CompressedSim.norm_exp_phase_sub_le (t * Real.sin θ)
      (t * Real.sin φ)
  have hs := Real.abs_sin_sub_sin_le θ φ
  have hsin : |t * Real.sin θ - t * Real.sin φ| ≤ |t| * |θ - φ| := by
    rw [← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_left hs (abs_nonneg t)
  unfold sinePhase
  calc ‖Complex.exp (-(Complex.I * ((t * Real.sin θ : ℝ) : ℂ)))
        - Complex.exp (-(Complex.I * ((t * Real.sin φ : ℝ) : ℂ)))‖
      ≤ |t * Real.sin θ - t * Real.sin φ| := hcore
    _ ≤ |t| * |θ - φ| := hsin

/-- Defines the diagonal matrix with diagonal entries `sinePhase t (φ i)`. -/
def sineWindowMatrix (t : ℝ) (φ : ι → ℝ) : Matrix ι ι ℂ :=
  Matrix.diagonal (fun i => sinePhase t (φ i))

/-- The sine-window matrix has the specified sine phase on the diagonal and zero off the
diagonal. -/
theorem sineWindowMatrix_apply (t : ℝ) (φ : ι → ℝ) (i j : ι) :
    sineWindowMatrix t φ i j = if i = j then sinePhase t (φ i) else 0 := by
  unfold sineWindowMatrix
  rw [Matrix.diagonal_apply]

/-- The diagonal sine-window matrix is unitary, realizing the phase readout operation of
[Childs2010]. -/
theorem sineWindowMatrix_mem_unitary (t : ℝ) (φ : ι → ℝ) :
    sineWindowMatrix t φ ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  unfold sineWindowMatrix
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  funext i j
  rw [Matrix.diagonal_apply, Matrix.one_apply]
  by_cases h : i = j
  · subst h
    simp only [↓reduceIte, Pi.star_apply]
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
        sinePhase_norm]
    norm_num
  · simp [h]

/-- The sine-window matrix multiplies each state coordinate by its corresponding sine phase. -/
theorem sineWindowMatrix_mulVec_apply (t : ℝ) (φ : ι → ℝ) (v : QState ι) (i : ι) :
    (sineWindowMatrix t φ *ᵥ v) i = sinePhase t (φ i) * v i := by
  unfold sineWindowMatrix
  simp only [Matrix.mulVec, dotProduct, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [show i ≠ j from fun h => hji h.symm]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- Defines the state vector with amplitudes `w i` multiplied by the ideal phases `exp(-i * t *
sin (θ i))`. -/
def idealVec (t : ℝ) (θ : ι → ℝ) (w : ι → ℂ) : QState ι :=
  fun i => w i * Complex.exp (-(Complex.I * ((t * Real.sin (θ i) : ℝ) : ℂ)))

/-- Defines the state vector with amplitudes `w i` multiplied by the readout phases `sinePhase t
(φ i)`. -/
def simVec (t : ℝ) (φ : ι → ℝ) (w : ι → ℂ) : QState ι :=
  fun i => w i * sinePhase t (φ i)

/-- The ideal and simulated vectors have inner product equal to the sum of phase differences
weighted by `‖w i‖ ^ 2`. This is the overlap formula underlying [Childs2010]. -/
theorem inner_idealVec_simVec (t : ℝ) (θ φ : ι → ℝ) (w : ι → ℂ) :
    Qatlib.Foundations.PureStateMath.Inner (idealVec t θ w) (simVec t φ w)
      = ∑ i, ((‖w i‖ ^ 2 : ℝ) : ℂ) *
          Complex.exp (Complex.I * ((t * (Real.sin (θ i) - Real.sin (φ i)) : ℝ) : ℂ)) := by
  unfold Qatlib.Foundations.PureStateMath.Inner idealVec simVec
  rw [dotProduct]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Pi.star_apply]
  have hconj : (star (w i * Complex.exp (-(Complex.I * ((t * Real.sin (θ i) : ℝ) : ℂ)))))
      = (star (w i)) * Complex.exp (Complex.I * ((t * Real.sin (θ i) : ℝ) : ℂ)) := by
    rw [star_mul, mul_comm]
    congr 1
    rw [Complex.star_def, ← Complex.exp_conj]
    congr 1
    rw [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  rw [hconj]
  have hexp : Complex.exp (Complex.I * ((t * Real.sin (θ i) : ℝ) : ℂ)) *
        Complex.exp (-(Complex.I * ((t * Real.sin (φ i) : ℝ) : ℂ)))
      = Complex.exp (Complex.I * ((t * (Real.sin (θ i) - Real.sin (φ i)) : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc (star (w i) * Complex.exp (Complex.I * ((t * Real.sin (θ i) : ℝ) : ℂ))) *
        (w i * Complex.exp (-(Complex.I * ((t * Real.sin (φ i) : ℝ) : ℂ))))
      = (star (w i) * w i) *
          (Complex.exp (Complex.I * ((t * Real.sin (θ i) : ℝ) : ℂ)) *
            Complex.exp (-(Complex.I * ((t * Real.sin (φ i) : ℝ) : ℂ)))) := by
        ring
    _ = (star (w i) * w i) *
          Complex.exp (Complex.I * ((t * (Real.sin (θ i) - Real.sin (φ i)) : ℝ) : ℂ)) := by
        rw [hexp]
    _ = ((‖w i‖ ^ 2 : ℝ) : ℂ) *
          Complex.exp (Complex.I * ((t * (Real.sin (θ i) - Real.sin (φ i)) : ℝ) : ℂ)) := by
        rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]

/-- The real part of the ideal-simulated overlap is the weighted sum of cosines of the
sine-phase differences. See [Childs2010]. -/
theorem inner_idealVec_simVec_re (t : ℝ) (θ φ : ι → ℝ) (w : ι → ℂ) :
    (Qatlib.Foundations.PureStateMath.Inner (idealVec t θ w) (simVec t φ w)).re
      = ∑ i, ‖w i‖ ^ 2 * Real.cos (t * (Real.sin (θ i) - Real.sin (φ i))) := by
  rw [inner_idealVec_simVec]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Complex.mul_re]
  rw [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have harg : Complex.I * ((t * (Real.sin (θ i) - Real.sin (φ i)) : ℝ) : ℂ)
      = ((t * (Real.sin (θ i) - Real.sin (φ i)) : ℝ) : ℂ) * Complex.I := by
    ring
  rw [harg, Complex.exp_ofReal_mul_I_re]

/-- For amplitudes with squared norms summing to one, the real overlap is bounded below by one
minus half `t ^ 2` times the weighted squared phase error. See [Childs2010]. -/
theorem readout_fidelity_ge (t : ℝ) (θ φ : ι → ℝ) (w : ι → ℂ)
    (hsum : ∑ i, ‖w i‖ ^ 2 = 1) :
    1 - t ^ 2 / 2 * (∑ i, ‖w i‖ ^ 2 * (θ i - φ i) ^ 2)
      ≤ (Qatlib.Foundations.PureStateMath.Inner (idealVec t θ w) (simVec t φ w)).re := by
  rw [inner_idealVec_simVec_re]
  have h := weighted_cos_ge (fun i => ‖w i‖ ^ 2)
    (fun i => sq_nonneg _) hsum θ φ t
  calc 1 - t ^ 2 / 2 * (∑ i, ‖w i‖ ^ 2 * (θ i - φ i) ^ 2)
      ≤ ∑ i, ‖w i‖ ^ 2 * Real.cos (t * (Real.sin (θ i) - Real.sin (φ i))) := h

/-- For normalized amplitudes and positive `M`, a weighted phase-error second moment at most
`186 / M ^ 2` gives real overlap at least `1 - 93 * t ^ 2 / M ^ 2`. See [Childs2010]. -/
theorem readout_fidelity_of_variance (t M : ℝ) (θ φ : ι → ℝ) (w : ι → ℂ)
    (hsum : ∑ i, ‖w i‖ ^ 2 = 1) (hM : 0 < M)
    (hV : ∑ i, ‖w i‖ ^ 2 * (θ i - φ i) ^ 2 ≤ 186 / M ^ 2) :
    1 - 93 * t ^ 2 / M ^ 2 ≤ (Qatlib.Foundations.PureStateMath.Inner (idealVec t θ w) (simVec t φ w)).re := by
  rw [inner_idealVec_simVec_re]
  exact fidelity_of_variance_le (fun i => ‖w i‖ ^ 2) (fun i => sq_nonneg _) hsum θ φ t M hM hV

/-- If the squared amplitude norms sum to one, `simVec t φ w` is normalized. This verifies
normalization for the readout model in [Childs2010]. -/
theorem normalized_simVec (t : ℝ) (φ : ι → ℝ) (w : ι → ℂ)
    (hsum : ∑ i, ‖w i‖ ^ 2 = 1) : Normalized (simVec t φ w) := by
  unfold Normalized simVec
  rw [← hsum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [norm_mul, sinePhase_norm, mul_one]

/-- If the squared amplitude norms sum to one, `idealVec t θ w` is normalized. -/
theorem normalized_idealVec (t : ℝ) (θ : ι → ℝ) (w : ι → ℂ)
    (hsum : ∑ i, ‖w i‖ ^ 2 = 1) : Normalized (idealVec t θ w) := by
  unfold Normalized idealVec
  rw [← hsum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hnorm : ‖Complex.exp (-(Complex.I * ((t * Real.sin (θ i) : ℝ) : ℂ)))‖ = 1 := by
    rw [Complex.norm_exp]
    have hre : (-(Complex.I * ((t * Real.sin (θ i) : ℝ) : ℂ))).re = 0 := by simp
    rw [hre, Real.exp_zero]
  rw [norm_mul, hnorm, mul_one]

end Qatlib.Papers.ContDiscWalk08.SineReadout
