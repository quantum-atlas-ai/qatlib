/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.NormCast
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge

/-!
# Rank-one spectral search

This module studies `searchHamiltonian`, an affine rescaling of a real-spectrum Hamiltonian with
a marked-state outer product added. It develops the secular function and secular states, a
calibration parameter, and explicit bounds locating two nearby eigenvalues and controlling their
overlaps. This is the rank-one perturbation framework used in continuous-time spatial search
[ChakrabortyEtAl2016].

The final results analyze Hamiltonian evolution of a resonant difference of secular states. They
bound the approximation remainder and derive a transition-probability lower bound under explicit
coefficient and remainder hypotheses.

## Main statements

* `rank_one_calibration_exists`: existence of a calibrated spectral rescaling.
* `rank_one_two_level_states`: normalized eigenstates with quantitative overlap bounds.
* `rank_one_resonant_probability_bound`: a lower bound at the resonant evolution time.

## References

* [Chakraborty et al., 2016][ChakrabortyEtAl2016]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

set_option autoImplicit false

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Concepts.WalkSearch.RankOneSpectralSearch.RankOneSpectralSearch

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The outer-product matrix of a state with its conjugate; it is a rank-one orthogonal
projector when the state is normalized. -/
noncomputable def rankOneProjector (ψ : QState I) : Matrix I I ℂ :=
  Matrix.of fun i j => ψ i * (starRingEnd ℂ) (ψ j)

/-- The Hermitian matrix `V * diagonal lam * Vᴴ` associated with real spectral coefficients. -/
noncomputable def spectralHamiltonian (V : Matrix I I ℂ) (lam : I → ℝ) : Matrix I I ℂ :=
  V * Matrix.diagonal (fun i => (lam i : ℂ)) * V.conjTranspose

/-- The rescaled spectral gap parameter `(1 - c) / (1 + c)`. -/
noncomputable def spectralGapParam (c : ℝ) : ℝ := (1 - c) / (1 + c)

/-- The small-overlap threshold given by the minimum of `spectralGapParam c` to the power `3/2`,
divided by eight, and one half. -/
noncomputable def searchOverlapBound (c : ℝ) : ℝ :=
  min ((spectralGapParam c) ^ (3 / 2 : ℝ) / 8) (1 / 2)

/-- The affine spectral rescaling `(1 + r) * lam i - r`. -/
def rescaledEigenvalue (lam : I → ℝ) (r : ℝ) (i : I) : ℝ := (1 + r) * lam i - r

/-- The affinely rescaled spectral Hamiltonian with the outer product of the marked state added. -/
noncomputable def searchHamiltonian (V : Matrix I I ℂ) (lam : I → ℝ) (r : ℝ)
    (w : QState I) : Matrix I I ℂ :=
  (1 + r) • spectralHamiltonian V lam - r • (1 : Matrix I I ℂ) + rankOneProjector w

/-- The sum of squared spectral overlaps divided by the differences between a trial eigenvalue
and the rescaled eigenvalues. -/
noncomputable def rankOneSecularFunction (V : Matrix I I ℂ) (lam : I → ℝ)
    (r : ℝ) (w : QState I) (ℓ : ℝ) : ℝ :=
  ∑ i, ‖Qatlib.Foundations.PureStateMath.Inner (fun j => V j i) w‖ ^ 2 / (ℓ - rescaledEigenvalue lam r i)

/-- The outer-product matrix of `w` maps `x` to its inner product with `w`, multiplied by `w`. -/
theorem rankOneProjector_mulVec (w x : QState I) :
    rankOneProjector w *ᵥ x = Qatlib.Foundations.PureStateMath.Inner w x • w := by
  ext i
  simp only [rankOneProjector, Matrix.mulVec, dotProduct, Matrix.of_apply,
    inner_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [Fintype I] [DecidableEq I] in

/-- The outer-product matrix of any state is Hermitian. -/
theorem rankOneProjector_isHermitian (w : QState I) :
    (rankOneProjector w).IsHermitian := by
  ext i j
  simp [rankOneProjector, Matrix.conjTranspose_apply, mul_comm]

/-- Real diagonal coefficients make `spectralHamiltonian V lam` Hermitian for every matrix `V`. -/
theorem spectralHamiltonian_isHermitian (V : Matrix I I ℂ) (lam : I → ℝ) :
    (spectralHamiltonian V lam).IsHermitian := by
  unfold spectralHamiltonian
  apply Matrix.isHermitian_mul_mul_conjTranspose
  apply Matrix.isHermitian_diagonal_iff.2
  intro i
  simp [IsSelfAdjoint]

/-- For unitary `V`, its column indexed by `i` is an eigenvector of `spectralHamiltonian V lam`
with eigenvalue `lam i`. -/
theorem spectralHamiltonian_eigen (V : Matrix I I ℂ) (lam : I → ℝ) (i : I)
    (hV : V ∈ Matrix.unitaryGroup I ℂ) :
    spectralHamiltonian V lam *ᵥ (fun j => V j i) = (lam i : ℂ) • (fun j => V j i) := by
  have hVV : Vᴴ * V = 1 := by
    simpa only [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] using hV
  have hv : Vᴴ *ᵥ V.col i = Pi.single i 1 := by
    rw [← Matrix.mulVec_single_one, Matrix.mulVec_mulVec, hVV, Matrix.one_mulVec]
  change spectralHamiltonian V lam *ᵥ V.col i = (lam i : ℂ) • V.col i
  unfold spectralHamiltonian
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.diagonal_mulVec_single]
  simp

omit [DecidableEq I] in

/-- Move a matrix acting on the second inner-product argument to its adjoint acting on the
first. -/
theorem inner_mulVec_adjoint (M : Matrix I I ℂ) (s x : QState I) :
    Qatlib.Foundations.PureStateMath.Inner s (M *ᵥ x) = Qatlib.Foundations.PureStateMath.Inner (Mᴴ *ᵥ s) x := by
  simp only [Qatlib.Foundations.PureStateMath.Inner, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose,
    Matrix.dotProduct_mulVec]

omit [DecidableEq I] in

/-- The state inner product is complex-linear in its second argument. -/
theorem inner_smul_state (s x : QState I) (a : ℂ) :
    Qatlib.Foundations.PureStateMath.Inner s (a • x) = a * Qatlib.Foundations.PureStateMath.Inner s x := by
  simp only [Qatlib.Foundations.PureStateMath.Inner, dotProduct_smul, smul_eq_mul]

omit [DecidableEq I] in

/-- The state inner product preserves addition in its second argument. -/
theorem inner_add_state (s x y : QState I) : Qatlib.Foundations.PureStateMath.Inner s (x + y) = Qatlib.Foundations.PureStateMath.Inner s x + Qatlib.Foundations.PureStateMath.Inner s y :=
  dotProduct_add _ _ _

omit [DecidableEq I] in

/-- The state inner product preserves subtraction in its second argument. -/
theorem inner_sub_state (s x y : QState I) : Qatlib.Foundations.PureStateMath.Inner s (x - y) = Qatlib.Foundations.PureStateMath.Inner s x - Qatlib.Foundations.PureStateMath.Inner s y :=
  dotProduct_sub _ _ _

omit [DecidableEq I] in

/-- Complex conjugation exchanges the arguments of the state inner product. -/
theorem inner_conj_state (s x : QState I) : star (Qatlib.Foundations.PureStateMath.Inner s x) = Qatlib.Foundations.PureStateMath.Inner x s := by
  rw [← inner_euclidean_fromVec, Qatlib.Foundations.PureStateMath.BornBridge.inner_conj_symm,
      inner_euclidean_fromVec]
  rfl

/-- The squared overlaps of a normalized state with the columns of a unitary matrix sum to one. -/
theorem spectral_weights_sum (V : Matrix I I ℂ) (w : QState I)
    (hV : V ∈ Matrix.unitaryGroup I ℂ) (hw : Normalized w) :
    ∑ i, ‖Qatlib.Foundations.PureStateMath.Inner (fun j => V j i) w‖ ^ 2 = 1 := by
  have hVs : Vᴴ ∈ Matrix.unitaryGroup I ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    simpa only [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] using hV
  have hn := normalized_applyGate hVs hw
  have hi (i : I) : Qatlib.Foundations.PureStateMath.Inner (fun j => V j i) w = (Vᴴ *ᵥ w) i := by
    rfl
  simpa only [Normalized, ApplyGate, hi] using hn

/-- Under the spectral and normalization hypotheses, there is a rescaling parameter between `-c
/ (1 + c)` and `c / (1 - c)` for which the weighted reciprocal gap sum equals the weight
outside the distinguished column. -/
theorem rank_one_calibration_exists
    (V : Matrix I I ℂ) (lam : I → ℝ) (σ : I) (c : ℝ) (w : QState I)
    (hV : V ∈ Matrix.unitaryGroup I ℂ) (_hlamσ : lam σ = 1)
    (hlamc : ∀ i, i ≠ σ → |lam i| ≤ c) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hw : Normalized w) (hε : ‖Qatlib.Foundations.PureStateMath.Inner w (fun j => V j σ)‖ < 1) :
    ∃ r : ℝ, -c / (1 + c) ≤ r ∧ r ≤ c / (1 - c) ∧
      ∑ i ∈ Finset.univ \ {σ}, ‖Qatlib.Foundations.PureStateMath.Inner (fun j => V j i) w‖ ^ 2 /
          (1 - rescaledEigenvalue lam r i)
        = 1 - ‖Qatlib.Foundations.PureStateMath.Inner w (fun j => V j σ)‖ ^ 2 := by
  let S := Finset.univ \ {σ}
  let a : I → ℝ := fun i => ‖Qatlib.Foundations.PureStateMath.Inner (fun j => V j i) w‖ ^ 2
  let A := ∑ i ∈ S, a i
  let W := ∑ i ∈ S, a i / (1 - lam i)
  have ha (i : I) : 0 ≤ a i := sq_nonneg _
  have hs : ‖Qatlib.Foundations.PureStateMath.Inner (fun j => V j σ) w‖ = ‖Qatlib.Foundations.PureStateMath.Inner w (fun j => V j σ)‖ := by
    rw [← inner_conj_state, norm_star]
  have hAtotal : A = 1 - ‖Qatlib.Foundations.PureStateMath.Inner w (fun j => V j σ)‖ ^ 2 := by
    have ht := spectral_weights_sum V w hV hw
    have hsum := Finset.sum_erase_add (Finset.univ : Finset I) a (Finset.mem_univ σ)
    change (∑ i ∈ S, a i) = _
    dsimp [S]
    rw [Finset.sdiff_singleton_eq_erase]
    change (∑ i, a i) = 1 at ht
    rw [ht] at hsum
    dsimp [a] at hsum
    rw [hs] at hsum
    linarith
  have hA : 0 < A := by
    rw [hAtotal]
    have := norm_nonneg (Qatlib.Foundations.PureStateMath.Inner w (fun j => V j σ))
    nlinarith
  have hcp : 0 < 1 + c := by linarith
  have hcm : 0 < 1 - c := by linarith
  have hg (i : I) (hi : i ∈ S) : 1 - c ≤ 1 - lam i ∧ 1 - lam i ≤ 1 + c := by
    have hne : i ≠ σ := by simpa [S] using hi
    have h := abs_le.mp (hlamc i hne)
    constructor <;> linarith
  have hgap (i : I) (hi : i ∈ S) : 0 < 1 - lam i := lt_of_lt_of_le hcm (hg i hi).1
  have hlo : A / (1+c) ≤ W := by
    dsimp [A, W]
    rw [Finset.sum_div]
    exact Finset.sum_le_sum fun i hi =>
      div_le_div_of_nonneg_left (ha i) (hgap i hi) (hg i hi).2
  have hhi : W ≤ A / (1-c) := by
    dsimp [A, W]
    rw [Finset.sum_div]
    exact Finset.sum_le_sum fun i hi =>
      div_le_div_of_nonneg_left (ha i) hcm (hg i hi).1
  have hW : 0 < W := lt_of_lt_of_le (div_pos hA hcp) hlo
  let r := W / A - 1
  have hr : 1+r = W/A := by dsimp [r]; ring
  have hrpos : 0 < 1+r := by rw [hr]; exact div_pos hW hA
  have hrlo : -c/(1+c) ≤ r := by
    have h := (le_div_iff₀ hA).2 (show (1/(1+c))*A ≤ W by
      simpa [div_eq_mul_inv, mul_comm] using hlo)
    have he : 1/(1+c) - 1 = -c/(1+c) := by field_simp; ring
    dsimp [r]
    linarith
  have hrhi : r ≤ c/(1-c) := by
    have h := (div_le_iff₀ hA).2 (show W ≤ (1/(1-c))*A by
      simpa [div_eq_mul_inv, mul_comm] using hhi)
    have he : 1/(1-c) - 1 = c/(1-c) := by field_simp; ring
    dsimp [r]
    linarith
  refine ⟨r, hrlo, hrhi, ?_⟩
  change (∑ i ∈ S, a i / (1 - rescaledEigenvalue lam r i)) = _
  calc
    (∑ i ∈ S, a i / (1 - rescaledEigenvalue lam r i)) = W / (1+r) := by
      dsimp [W]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      have he : 1 - rescaledEigenvalue lam r i = (1+r)*(1-lam i) := by
        unfold rescaledEigenvalue
        ring
      rw [he, div_mul_eq_div_div_swap]
    _ = A := by rw [hr]; field_simp
    _ = 1 - ‖Qatlib.Foundations.PureStateMath.Inner w (fun j => V j σ)‖ ^ 2 := hAtotal

omit [Fintype I] [DecidableEq I] in

/-- For calibrated nonnegative weights and gaps at least `ν > 0`, the reciprocal second moment
lies between the total weight and that weight divided by `ν`. -/
theorem rank_one_weighted_second_moment_bounds
    (S : Finset I) (a g : I → ℝ) (ν : ℝ)
    (ha : ∀ i ∈ S, 0 ≤ a i) (hν : 0 < ν) (hg : ∀ i ∈ S, ν ≤ g i)
    (hA : 0 < ∑ i ∈ S, a i)
    (hcal : ∑ i ∈ S, a i / g i = ∑ i ∈ S, a i) :
    (∑ i ∈ S, a i) ≤ (∑ i ∈ S, a i / g i ^ 2) ∧
      (∑ i ∈ S, a i / g i ^ 2) ≤ (∑ i ∈ S, a i) / ν := by
  have hgp (i : I) (hi : i ∈ S) : 0 < g i := hν.trans_le (hg i hi)
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul S
    (f := a) (g := fun i => a i / g i ^ 2)
    ha (fun i hi => div_nonneg (ha i hi) (sq_nonneg _))
    (r := fun i => a i / g i) (fun i hi => by
      have hn := (hgp i hi).ne'
      apply le_of_eq
      field_simp)
  rw [hcal] at hcs
  constructor
  · nlinarith
  · rw [← hcal, Finset.sum_div]
    apply Finset.sum_le_sum
    intro i hi
    rw [div_div]
    apply div_le_div_of_nonneg_left (ha i hi) (mul_pos (hgp i hi) hν)
    nlinarith [hg i hi]

omit [Fintype I] [DecidableEq I] in

/-- Shifting gaps by `y ∈ [0, ν / 2]` bounds the mixed reciprocal moments between two thirds and
one times the unshifted second moment for the positive shift, and between one and two times
it for the negative shift. -/
theorem rank_one_shifted_moment_bounds
    (S : Finset I) (a g : I → ℝ) (ν y : ℝ)
    (ha : ∀ i ∈ S, 0 ≤ a i) (hν : 0 < ν) (hg : ∀ i ∈ S, ν ≤ g i)
    (hy0 : 0 ≤ y) (hy : y ≤ ν / 2) :
    (2/3 : ℝ) * (∑ i ∈ S, a i / g i ^ 2) ≤
        (∑ i ∈ S, a i / (g i * (g i + y))) ∧
      (∑ i ∈ S, a i / (g i * (g i + y))) ≤ (∑ i ∈ S, a i / g i ^ 2) ∧
      (∑ i ∈ S, a i / g i ^ 2) ≤ (∑ i ∈ S, a i / (g i * (g i - y))) ∧
      (∑ i ∈ S, a i / (g i * (g i - y))) ≤ 2 * (∑ i ∈ S, a i / g i ^ 2) := by
  have hgp (i : I) (hi : i ∈ S) : 0 < g i := hν.trans_le (hg i hi)
  have hyp (i : I) (hi : i ∈ S) : y ≤ g i / 2 := le_trans hy (by linarith [hg i hi])
  have hp (i : I) (hi : i ∈ S) : 0 < g i * (g i + y) :=
    mul_pos (hgp i hi) (by linarith [hgp i hi])
  have hm (i : I) (hi : i ∈ S) : 0 < g i * (g i - y) :=
    mul_pos (hgp i hi) (by linarith [hgp i hi, hyp i hi])
  have hs (i : I) (hi : i ∈ S) : 0 < g i ^ 2 := sq_pos_of_pos (hgp i hi)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    apply (le_div_iff₀ (hp i hi)).2
    calc
      (2/3 : ℝ) * (a i / g i ^ 2) * (g i * (g i+y)) =
          (a i / g i ^ 2) * ((2/3 : ℝ) * (g i * (g i+y))) := by ring
      _ ≤ (a i / g i ^ 2) * g i ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (div_nonneg (ha i hi) (hs i hi).le)
        nlinarith [mul_le_mul_of_nonneg_left (hyp i hi) (hgp i hi).le]
      _ = a i := div_mul_cancel₀ _ (hs i hi).ne'
  · apply Finset.sum_le_sum
    intro i hi
    apply div_le_div_of_nonneg_left (ha i hi) (hs i hi)
    nlinarith [mul_nonneg (hgp i hi).le hy0]
  · apply Finset.sum_le_sum
    intro i hi
    apply div_le_div_of_nonneg_left (ha i hi) (hm i hi)
    nlinarith [mul_nonneg (hgp i hi).le hy0]
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    apply (div_le_iff₀ (hm i hi)).2
    calc
      a i = (a i / g i ^ 2) * g i ^ 2 := (div_mul_cancel₀ _ (hs i hi).ne').symm
      _ ≤ (a i / g i ^ 2) * (2 * (g i * (g i-y))) := by
        apply mul_le_mul_of_nonneg_left _ (div_nonneg (ha i hi) (hs i hi).le)
        nlinarith [mul_le_mul_of_nonneg_left (hyp i hi) (hgp i hi).le]
      _ = 2 * (a i / g i ^ 2) * (g i * (g i-y)) := by ring

section ScalarRoots
set_option maxHeartbeats 800000

omit [Fintype I] [DecidableEq I] in

/-- Under the calibration, gap, and small-overlap hypotheses, the two scalar secular equations
have positive shifts between `ε * sqrt (ν / 2)` and `ν / 2`. -/
theorem rank_one_scalar_two_roots
    (S : Finset I) (a g : I → ℝ) (ν ε : ℝ)
    (ha : ∀ i ∈ S, 0 ≤ a i) (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hg : ∀ i ∈ S, ν ≤ g i) (hε : 0 < ε) (hεhalf : ε ≤ 1/2)
    (hεsmall : ε ^ 2 ≤ ν ^ 3 / 64)
    (htotal : ∑ i ∈ S, a i = 1 - ε ^ 2)
    (hcal : ∑ i ∈ S, a i / g i = ∑ i ∈ S, a i) :
    ∃ δp δm : ℝ,
      ε * Real.sqrt (ν/2) ≤ δp ∧ δp ≤ ν/2 ∧
      ε * Real.sqrt (ν/2) ≤ δm ∧ δm ≤ ν/2 ∧
      ε ^ 2 / δp + (∑ i ∈ S, a i / (g i + δp)) = 1 ∧
      -(ε ^ 2 / δm) + (∑ i ∈ S, a i / (g i - δm)) = 1 := by
  let A := ∑ i ∈ S, a i
  let C := ∑ i ∈ S, a i / g i ^ 2
  let Rp := fun y : ℝ => ∑ i ∈ S, a i / (g i * (g i + y))
  let Rm := fun y : ℝ => ∑ i ∈ S, a i / (g i * (g i - y))
  let L := ε * Real.sqrt (ν/2)
  let U := ν/2
  have hAlo : (3/4 : ℝ) ≤ A := by dsimp [A]; rw [htotal]; nlinarith
  have hAhi : A ≤ 1 := by dsimp [A]; rw [htotal]; nlinarith
  have hApos : 0 < A := by linarith
  have hC := rank_one_weighted_second_moment_bounds S a g ν ha hν hg hApos hcal
  change A ≤ C ∧ C ≤ A/ν at hC
  have hCν : C*ν ≤ A := (le_div_iff₀ hν).1 hC.2
  have hLpos : 0 < L := mul_pos hε (Real.sqrt_pos.2 (by linarith))
  have hUpos : 0 < U := by dsimp [U]; linarith
  have hUhalf : U ≤ 1/2 := by dsimp [U]; linarith
  have hLsq : L ^ 2 = ε ^ 2 * ν / 2 := by
    dsimp [L]
    rw [mul_pow, Real.sq_sqrt (by linarith : 0 ≤ ν/2)]
    ring
  have hνcube : ν ^ 3 ≤ ν ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg ν) (sub_nonneg.2 hν1)]
  have hεsq : ε ^ 2 ≤ ν ^ 2 / 64 := hεsmall.trans (by linarith)
  have hLU : L ≤ U := by
    have h1 := mul_le_mul_of_nonneg_right hεsq hν.le
    dsimp [U]
    nlinarith [hLsq]
  have hLhalf : L ≤ 1/2 := hLU.trans hUhalf
  have hLC : L ^ 2 * C ≤ ε ^ 2 * A / 2 := by
    calc
      L ^ 2 * C = (ε ^ 2/2) * (C*ν) := by rw [hLsq]; ring
      _ ≤ (ε ^ 2/2) * A := mul_le_mul_of_nonneg_left hCν (by positivity)
      _ = ε ^ 2 * A / 2 := by ring
  have hR (y : ℝ) (hy0 : 0 ≤ y) (hy : y ≤ U) :
      (2/3 : ℝ)*C ≤ Rp y ∧ Rp y ≤ C ∧ C ≤ Rm y ∧ Rm y ≤ 2*C :=
    rank_one_shifted_moment_bounds S a g ν y ha hν hg hy0 hy
  let Hp := fun y : ℝ => ε ^ 2 * (1-y) - y ^ 2 * Rp y
  let Hm := fun y : ℝ => ε ^ 2 * (1+y) - y ^ 2 * Rm y
  have hpL : 0 ≤ Hp L := by
    have h := mul_le_mul_of_nonneg_left (hR L hLpos.le hLU).2.1 (sq_nonneg L)
    have h1 : ε ^ 2 * (1-L) ≥ ε ^ 2 * A / 2 := by
      have := mul_nonneg (sq_nonneg ε) (show 0 ≤ 1-L-A/2 by linarith)
      nlinarith
    dsimp [Hp]
    linarith
  have hmL : 0 ≤ Hm L := by
    have h := mul_le_mul_of_nonneg_left (hR L hLpos.le hLU).2.2.2 (sq_nonneg L)
    have h1 : ε ^ 2 * (1+L) ≥ ε ^ 2 * A := by
      have := mul_nonneg (sq_nonneg ε) (show 0 ≤ 1+L-A by linarith)
      nlinarith
    dsimp [Hm]
    nlinarith [hLC]
  have hpU : Hp U ≤ 0 := by
    have hlo : (1/2 : ℝ) ≤ Rp U := by linarith [(hR U hUpos.le le_rfl).1, hC.1]
    have h1 := mul_le_mul_of_nonneg_left hlo (sq_nonneg U)
    have h2 := mul_nonneg (sq_nonneg ε) hUpos.le
    dsimp [Hp, U] at *
    nlinarith [hεsq]
  have hmU : Hm U ≤ 0 := by
    have hlo : (3/4 : ℝ) ≤ Rm U := hAlo.trans (hC.1.trans (hR U hUpos.le le_rfl).2.2.1)
    have h1 := mul_le_mul_of_nonneg_left hlo (sq_nonneg U)
    have h2 := mul_le_mul_of_nonneg_left hUhalf (sq_nonneg ε)
    dsimp [Hm, U] at *
    nlinarith [hεsq]
  have hgp (i : I) (hi : i ∈ S) : 0 < g i := hν.trans_le (hg i hi)
  have hdenp (i : I) (hi : i ∈ S) (y : ℝ) (hy : y ∈ Set.Icc L U) :
      0 < g i * (g i+y) := mul_pos (hgp i hi) (by linarith [hgp i hi, hy.1])
  have hdenm (i : I) (hi : i ∈ S) (y : ℝ) (hy : y ∈ Set.Icc L U) :
      0 < g i * (g i-y) := mul_pos (hgp i hi) (by dsimp [U] at hy; linarith [hg i hi, hy.2])
  have hRp : ContinuousOn Rp (Set.Icc L U) := by
    apply continuousOn_finsetSum S
    intro i hi
    exact continuousOn_const.div (continuousOn_const.mul
      (continuousOn_const.add continuousOn_id)) (fun y hy => (hdenp i hi y hy).ne')
  have hRm : ContinuousOn Rm (Set.Icc L U) := by
    apply continuousOn_finsetSum S
    intro i hi
    exact continuousOn_const.div (continuousOn_const.mul
      (continuousOn_const.sub continuousOn_id)) (fun y hy => (hdenm i hi y hy).ne')
  have hHp : ContinuousOn Hp (Set.Icc L U) :=
    (continuousOn_const.mul (continuousOn_const.sub continuousOn_id)).sub
      ((continuousOn_id.pow 2).mul hRp)
  have hHm : ContinuousOn Hm (Set.Icc L U) :=
    (continuousOn_const.mul (continuousOn_const.add continuousOn_id)).sub
      ((continuousOn_id.pow 2).mul hRm)
  obtain ⟨δp, hδp, hrootp⟩ := intermediate_value_Icc' hLU hHp ⟨hpU, hpL⟩
  obtain ⟨δm, hδm, hrootm⟩ := intermediate_value_Icc' hLU hHm ⟨hmU, hmL⟩
  refine ⟨δp, δm, hδp.1, hδp.2, hδm.1, hδm.2, ?_, ?_⟩
  · have hd : 0 < δp := hLpos.trans_le hδp.1
    have he : (∑ i ∈ S, a i/(g i+δp)) = A-δp*Rp δp := by
      dsimp [A, Rp]
      rw [← hcal, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      have hg0 := (hgp i hi).ne'
      have hd0 : g i+δp ≠ 0 := ne_of_gt (by linarith [hgp i hi])
      field_simp; ring
    rw [he]
    change ε ^ 2 * (1-δp) - δp ^ 2 * Rp δp = 0 at hrootp
    have hAt : A = 1-ε ^ 2 := htotal
    have hb : ε ^ 2 / δp = 1-A+δp*Rp δp := by
      apply (div_eq_iff hd.ne').2
      rw [hAt]
      nlinarith only [hrootp]
    linarith only [hb]
  · have hd : 0 < δm := hLpos.trans_le hδm.1
    have he : (∑ i ∈ S, a i/(g i-δm)) = A+δm*Rm δm := by
      dsimp [A, Rm]
      rw [← hcal, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      have hg0 := (hgp i hi).ne'
      have hd0 : g i-δm ≠ 0 := ne_of_gt (by dsimp [U] at hδm; linarith [hg i hi, hδm.2])
      field_simp; ring
    rw [he]
    change ε ^ 2 * (1+δm) - δm ^ 2 * Rm δm = 0 at hrootm
    have hAt : A = 1-ε ^ 2 := htotal
    have hb : ε ^ 2 / δm = A-1+δm*Rm δm := by
      apply (div_eq_iff hd.ne').2
      rw [hAt]
      nlinarith only [hrootm]
    linarith only [hb]

end ScalarRoots

omit [Fintype I] [DecidableEq I] in

/-- Express a shifted reciprocal sum as the unshifted sum minus the shift times a mixed
reciprocal sum, when all denominators are nonzero. -/
theorem rank_one_shifted_sum_identity (S : Finset I) (a g : I → ℝ) (y : ℝ)
    (hg : ∀ i ∈ S, g i ≠ 0) (hgy : ∀ i ∈ S, g i+y ≠ 0) :
    (∑ i ∈ S, a i / (g i+y)) = (∑ i ∈ S, a i/g i) -
      y * (∑ i ∈ S, a i / (g i*(g i+y))) := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have h1 := hg i hi
  have h2 := hgy i hi
  field_simp; ring

section ScalarOverlap
set_option maxHeartbeats 800000

omit [Fintype I] [DecidableEq I] in

/-- For calibrated secular roots in the stated intervals, the inverse second moments are at
least `ν / 3` and `ν / 6`, and their distinguished-weight contributions are at least `4 / 9`
and `1 / 9`. -/
theorem rank_one_scalar_overlap_bounds
    (S : Finset I) (a g : I → ℝ) (ν ε δp δm : ℝ)
    (ha : ∀ i ∈ S, 0 ≤ a i) (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hg : ∀ i ∈ S, ν ≤ g i) (hε : 0 < ε) (hεhalf : ε ≤ 1/2)
    (htotal : ∑ i ∈ S, a i = 1-ε ^ 2)
    (hcal : ∑ i ∈ S, a i/g i = ∑ i ∈ S, a i)
    (hpLo : ε*Real.sqrt (ν/2) ≤ δp) (hpHi : δp ≤ ν/2)
    (hmLo : ε*Real.sqrt (ν/2) ≤ δm) (hmHi : δm ≤ ν/2)
    (hrootp : ε ^ 2/δp + (∑ i ∈ S, a i/(g i+δp)) = 1)
    (hrootm : -(ε ^ 2/δm) + (∑ i ∈ S, a i/(g i-δm)) = 1) :
    ν/3 ≤ (ε ^ 2/δp ^ 2 + ∑ i ∈ S, a i/(g i+δp) ^ 2)⁻¹ ∧
    ν/6 ≤ (ε ^ 2/δm ^ 2 + ∑ i ∈ S, a i/(g i-δm) ^ 2)⁻¹ ∧
    (4/9 : ℝ) ≤ (ε ^ 2/δp ^ 2) * (ε ^ 2/δp ^ 2 + ∑ i ∈ S, a i/(g i+δp) ^ 2)⁻¹ ∧
    (1/9 : ℝ) ≤ (ε ^ 2/δm ^ 2) * (ε ^ 2/δm ^ 2 + ∑ i ∈ S, a i/(g i-δm) ^ 2)⁻¹ := by
  let A := ∑ i ∈ S, a i
  let C := ∑ i ∈ S, a i/g i ^ 2
  let Rp := ∑ i ∈ S, a i/(g i*(g i+δp))
  let Rm := ∑ i ∈ S, a i/(g i*(g i-δm))
  let Dp := ∑ i ∈ S, a i/(g i+δp) ^ 2
  let Dm := ∑ i ∈ S, a i/(g i-δm) ^ 2
  let ρp := ε ^ 2/δp ^ 2
  let ρm := ε ^ 2/δm ^ 2
  have hp : 0 < δp := (mul_pos hε (Real.sqrt_pos.2 (by linarith))).trans_le hpLo
  have hm : 0 < δm := (mul_pos hε (Real.sqrt_pos.2 (by linarith))).trans_le hmLo
  have hpHalf : δp ≤ 1/2 := hpHi.trans (by linarith)
  have hmHalf : δm ≤ 1/2 := hmHi.trans (by linarith)
  have hgp (i : I) (hi : i ∈ S) : 0 < g i := hν.trans_le (hg i hi)
  have hgpp (i : I) (hi : i ∈ S) : 0 < g i+δp := by linarith [hgp i hi]
  have hgmm (i : I) (hi : i ∈ S) : 0 < g i-δm := by linarith [hg i hi]
  have hAlo : (3/4 : ℝ) ≤ A := by dsimp [A]; rw [htotal]; nlinarith
  have hAhi : A ≤ 1 := by dsimp [A]; rw [htotal]; nlinarith
  have hApos : 0 < A := by linarith
  have hC := rank_one_weighted_second_moment_bounds S a g ν ha hν hg hApos hcal
  change A ≤ C ∧ C ≤ A/ν at hC
  have hCν : C*ν ≤ 1 := ((le_div_iff₀ hν).1 hC.2).trans hAhi
  have hRp := rank_one_shifted_moment_bounds S a g ν δp ha hν hg hp.le hpHi
  have hRm := rank_one_shifted_moment_bounds S a g ν δm ha hν hg hm.le hmHi
  change (2/3 : ℝ)*C ≤ Rp ∧ Rp ≤ C ∧ _ at hRp
  change _ ∧ _ ∧ C ≤ Rm ∧ Rm ≤ 2*C at hRm
  have hρp : 0 < ρp := div_pos (sq_pos_of_pos hε) (sq_pos_of_pos hp)
  have hρm : 0 < ρm := div_pos (sq_pos_of_pos hε) (sq_pos_of_pos hm)
  have hρpeq : ρp*(1-δp) = Rp := by
    have he := rank_one_shifted_sum_identity S a g δp
      (fun i hi => (hgp i hi).ne') (fun i hi => (hgpp i hi).ne')
    rw [he, hcal, htotal] at hrootp
    have hdiv : ε ^ 2/δp = ε ^ 2+δp*Rp := by linarith only [hrootp]
    have heq := (div_eq_iff hp.ne').1 hdiv
    dsimp only [ρp]
    rw [div_mul_eq_mul_div]
    apply (div_eq_iff (sq_pos_of_pos hp).ne').2
    nlinarith only [heq]
  have hρmeq : ρm*(1+δm) = Rm := by
    have he := rank_one_shifted_sum_identity S a g (-δm)
      (fun i hi => (hgp i hi).ne') (fun i hi => by simpa only [← sub_eq_add_neg] using (hgmm i hi).ne')
    have he' : (∑ i ∈ S, a i/(g i-δm)) = (1-ε ^ 2)+δm*Rm := by
      simpa only [sub_eq_add_neg, hcal, htotal, neg_mul, sub_neg_eq_add, neg_neg, Rm] using he
    rw [he'] at hrootm
    have hdiv : ε ^ 2/δm = -ε ^ 2+δm*Rm := by linarith only [hrootm]
    have heq := (div_eq_iff hm.ne').1 hdiv
    dsimp only [ρm]
    rw [div_mul_eq_mul_div]
    apply (div_eq_iff (sq_pos_of_pos hm).ne').2
    nlinarith only [heq]
  have hDp : Dp ≤ Rp := by
    apply Finset.sum_le_sum
    intro i hi
    apply div_le_div_of_nonneg_left (ha i hi) (mul_pos (hgp i hi) (hgpp i hi))
    nlinarith [mul_nonneg hp.le (hgpp i hi).le]
  have hDm : Dm ≤ 2*Rm := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    apply (div_le_iff₀ (sq_pos_of_pos (hgmm i hi))).2
    have hden : g i*(g i-δm) ≤ 2*(g i-δm) ^ 2 := by
      nlinarith [mul_nonneg (show 0 ≤ g i-2*δm by linarith [hg i hi]) (hgmm i hi).le]
    calc
      a i = (a i/(g i*(g i-δm))) * (g i*(g i-δm)) :=
        (div_mul_cancel₀ _ (mul_pos (hgp i hi) (hgmm i hi)).ne').symm
      _ ≤ (a i/(g i*(g i-δm))) * (2*(g i-δm) ^ 2) :=
        mul_le_mul_of_nonneg_left hden (div_nonneg (ha i hi) (mul_pos (hgp i hi) (hgmm i hi)).le)
      _ = 2*(a i/(g i*(g i-δm)))*(g i-δm) ^ 2 := by ring
  have hρpC : ρp ≤ 2*C := by
    nlinarith only [hρpeq, hRp.2.1, mul_nonneg hρp.le (show 0 ≤ 1/2-δp by linarith)]
  have hρmC : ρm ≤ 2*C := by
    nlinarith only [hρmeq, hRm.2.2.2, mul_nonneg hρm.le hm.le]
  have hBpν : (ρp+Dp)*ν ≤ 3 := by
    have hb : ρp+Dp ≤ 3*C := by linarith [hRp.2.1]
    have := mul_le_mul_of_nonneg_right hb hν.le
    nlinarith only [this, hCν]
  have hBmν : (ρm+Dm)*ν ≤ 6 := by
    have hb : ρm+Dm ≤ 6*C := by linarith [hRm.2.2.2]
    have := mul_le_mul_of_nonneg_right hb hν.le
    nlinarith only [this, hCν]
  have hBp : 0 < ρp+Dp := add_pos_of_pos_of_nonneg hρp
    (Finset.sum_nonneg fun i hi => div_nonneg (ha i hi) (sq_nonneg _))
  have hBm : 0 < ρm+Dm := add_pos_of_pos_of_nonneg hρm
    (Finset.sum_nonneg fun i hi => div_nonneg (ha i hi) (sq_nonneg _))
  change ν/3 ≤ (ρp+Dp)⁻¹ ∧ ν/6 ≤ (ρm+Dm)⁻¹ ∧
    (4/9 : ℝ) ≤ ρp*(ρp+Dp)⁻¹ ∧ (1/9 : ℝ) ≤ ρm*(ρm+Dm)⁻¹
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [inv_eq_one_div]
    apply (le_div_iff₀ hBp).2
    nlinarith only [hBpν]
  · rw [inv_eq_one_div]
    apply (le_div_iff₀ hBm).2
    nlinarith only [hBmν]
  · rw [← div_eq_mul_inv]
    apply (le_div_iff₀ hBp).2
    have hDr : Dp ≤ ρp := hDp.trans (by nlinarith only [hρpeq, mul_nonneg hρp.le hp.le])
    nlinarith only [hDr, hρp]
  · rw [← div_eq_mul_inv]
    apply (le_div_iff₀ hBm).2
    have hDr : Dm ≤ 3*ρm := by
      nlinarith only [hDm, hρmeq, mul_nonneg hρm.le (show 0 ≤ 1/2-δm by linarith)]
    nlinarith only [hDr, hρm]

end ScalarOverlap

section ScalarRemainder
set_option maxHeartbeats 800000

omit [Fintype I] [DecidableEq I] in

/-- Under the calibration and secular-root hypotheses, the weighted mixed-denominator remainder
is at most `4 * ε^2 / ν^2`. -/
theorem rank_one_scalar_remainder_bound
    (S : Finset I) (a g : I → ℝ) (ν ε δp δm : ℝ)
    (ha : ∀ i ∈ S, 0 ≤ a i) (hν : 0 < ν) (hg : ∀ i ∈ S, ν ≤ g i)
    (hε : 0 < ε) (hεhalf : ε ≤ 1/2) (hp : 0 < δp) (hm : 0 < δm)
    (hpHi : δp ≤ ν/2) (hmHi : δm ≤ ν/2)
    (htotal : ∑ i ∈ S, a i = 1-ε ^ 2)
    (hcal : ∑ i ∈ S, a i/g i = ∑ i ∈ S, a i)
    (hrootp : ε ^ 2/δp + (∑ i ∈ S, a i/(g i+δp)) = 1)
    (hrootm : -(ε ^ 2/δm) + (∑ i ∈ S, a i/(g i-δm)) = 1) :
    (δp*δm/ε) ^ 2 * (∑ i ∈ S, a i/((g i+δp)*(g i-δm)) ^ 2) ≤
      4*ε ^ 2/ν ^ 2 := by
  let J := ∑ i ∈ S, a i/((g i+δp)*(g i-δm))
  have hgp (i : I) (hi : i ∈ S) : 0 < g i := hν.trans_le (hg i hi)
  have hpp (i : I) (hi : i ∈ S) : 0 < g i+δp := by linarith [hgp i hi]
  have hmm (i : I) (hi : i ∈ S) : 0 < g i-δm := by linarith [hg i hi]
  have hP (i : I) (hi : i ∈ S) : 0 < (g i+δp)*(g i-δm) := mul_pos (hpp i hi) (hmm i hi)
  have hdiff : (∑ i ∈ S, a i/(g i-δm))-(∑ i ∈ S, a i/(g i+δp)) =
      (δp+δm)*J := by
    dsimp [J]
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have h1 := (hpp i hi).ne'
    have h2 := (hmm i hi).ne'
    field_simp; ring
  have hr : ε ^ 2/(δp*δm) = J := by
    have hsum : ε ^ 2/δp+ε ^ 2/δm = (δp+δm)*J := by
      linarith only [hrootp, hrootm, hdiff]
    have he : ε ^ 2/δp+ε ^ 2/δm = (δp+δm)*(ε ^ 2/(δp*δm)) := by
      have hp0 := hp.ne'
      have hm0 := hm.ne'
      field_simp; ring
    rw [he] at hsum
    exact mul_left_cancel₀ (ne_of_gt (add_pos hp hm)) hsum
  have hA : (3/4 : ℝ) ≤ ∑ i ∈ S, a i := by rw [htotal]; nlinarith
  have hApos : 0 < ∑ i ∈ S, a i := by linarith
  have hC := rank_one_weighted_second_moment_bounds S a g ν ha hν hg hApos hcal
  have hshift := (rank_one_shifted_moment_bounds S a g ν δp ha hν hg hp.le hpHi).1
  have hJlo : (1/2 : ℝ) ≤ J := by
    have hle : (∑ i ∈ S, a i/(g i*(g i+δp))) ≤ J := by
      apply Finset.sum_le_sum
      intro i hi
      apply div_le_div_of_nonneg_left (ha i hi) (hP i hi)
      nlinarith [mul_nonneg hm.le (hpp i hi).le]
    linarith only [hA, hC.1, hshift, hle]
  have hprod : δp*δm ≤ 2*ε ^ 2 := by
    have he := (div_eq_iff (mul_pos hp hm).ne').1 hr
    nlinarith only [he, mul_le_mul_of_nonneg_right hJlo (mul_pos hp hm).le]
  have hden (i : I) (hi : i ∈ S) : ν ^ 2/2 ≤ (g i+δp)*(g i-δm) := by
    have hhalf : δm ≤ g i/2 := by linarith [hg i hi]
    have h1 := mul_nonneg (hgp i hi).le (show 0 ≤ g i/2-δm by linarith)
    have h2 := mul_nonneg hp.le (hmm i hi).le
    nlinarith [hg i hi]
  have hK : (∑ i ∈ S, a i/((g i+δp)*(g i-δm)) ^ 2) ≤ 2*J/ν ^ 2 := by
    dsimp [J]
    rw [Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_le_sum
    intro i hi
    let P := (g i+δp)*(g i-δm)
    have hPpos : 0 < P := hP i hi
    have hle := div_le_div_of_nonneg_left (div_nonneg (ha i hi) hPpos.le)
      (by positivity : 0 < ν ^ 2/2) (hden i hi)
    change (a i/P)/P ≤ (a i/P)/(ν ^ 2/2) at hle
    change a i/P ^ 2 ≤ 2*(a i/P)/ν ^ 2
    calc
      a i/P ^ 2 = (a i/P)/P := by rw [div_div, pow_two]
      _ ≤ (a i/P)/(ν ^ 2/2) := hle
      _ = 2*(a i/P)/ν ^ 2 := by ring
  have hrprod : (δp*δm/ε) ^ 2 * J = δp*δm := by
    rw [← hr]
    have hp0 := hp.ne'
    have hm0 := hm.ne'
    have he0 := hε.ne'
    field_simp
  calc
    (δp*δm/ε) ^ 2 * (∑ i ∈ S, a i/((g i+δp)*(g i-δm)) ^ 2) ≤
        (δp*δm/ε) ^ 2 * (2*J/ν ^ 2) := mul_le_mul_of_nonneg_left hK (sq_nonneg _)
    _ = 2*(δp*δm)/ν ^ 2 := by
      calc
        _ = 2*((δp*δm/ε) ^ 2*J)/ν ^ 2 := by ring
        _ = _ := by rw [hrprod]
    _ ≤ 4*ε ^ 2/ν ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg ν)
      nlinarith only [hprod]

end ScalarRemainder

/-- The rescaled spectral gap parameter is positive for `0 ≤ c < 1`. -/
theorem spectral_gap_param_pos {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) :
    0 < spectralGapParam c := div_pos (by linarith) (by linarith)

/-- The rescaled spectral gap parameter is at most one for nonnegative `c`. -/
theorem spectral_gap_param_le_one {c : ℝ} (hc0 : 0 ≤ c) (_hc1 : c < 1) :
    spectralGapParam c ≤ 1 := by
  unfold spectralGapParam
  apply (div_le_iff₀ (by linarith : 0 < 1+c)).2
  linarith

omit [Fintype I] [DecidableEq I] in

/-- An eigenvalue of absolute value at most `c < 1` has rescaled gap at least `spectralGapParam
c` when `r ≥ -c / (1 + c)`. -/
theorem rescaled_spectral_gap_lower_bound
    (lam : I → ℝ) (c r : ℝ) (i : I) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hr : -c/(1+c) ≤ r) (hi : |lam i| ≤ c) :
    spectralGapParam c ≤ 1 - rescaledEigenvalue lam r i := by
  have hcp : 0 < 1+c := by linarith
  have hcm : 0 < 1-c := by linarith
  have he : -c/(1+c)+1 = 1/(1+c) := by field_simp; ring
  have hrl : 1/(1+c) ≤ 1+r := by linarith
  have hrp : 0 < 1+r := (one_div_pos.2 hcp).trans_le hrl
  have hgi : 1-c ≤ 1-lam i := by linarith [(abs_le.mp hi).2]
  calc
    spectralGapParam c = (1/(1+c))*(1-c) := by unfold spectralGapParam; ring
    _ ≤ (1+r)*(1-lam i) := mul_le_mul hrl hgi hcm.le hrp.le
    _ = 1-rescaledEigenvalue lam r i := by unfold rescaledEigenvalue; ring

/-- The spectral weight outside a distinguished unitary column equals one minus the squared
overlap with that column. -/
theorem spectral_weights_off_top
    (V : Matrix I I ℂ) (w : QState I) (σ : I)
    (hV : V ∈ Matrix.unitaryGroup I ℂ) (hw : Normalized w) :
    (∑ i ∈ Finset.univ \ {σ}, ‖Qatlib.Foundations.PureStateMath.Inner (fun j => V j i) w‖ ^ 2) =
      1 - ‖Qatlib.Foundations.PureStateMath.Inner w (fun j => V j σ)‖ ^ 2 := by
  have ht := spectral_weights_sum V w hV hw
  have hs : ‖Qatlib.Foundations.PureStateMath.Inner (fun j => V j σ) w‖ = ‖Qatlib.Foundations.PureStateMath.Inner w (fun j => V j σ)‖ := by
    rw [← inner_conj_state, norm_star]
  have he := Finset.sum_erase_add (Finset.univ : Finset I)
    (fun i => ‖Qatlib.Foundations.PureStateMath.Inner (fun j => V j i) w‖ ^ 2) (Finset.mem_univ σ)
  rw [ht] at he
  (try dsimp only at he)
  rw [hs] at he
  rw [Finset.sdiff_singleton_eq_erase]
  linarith

/-- At a trial eigenvalue `1 + y`, separate the distinguished eigenvalue-one contribution from
the remaining terms of the secular function. -/
theorem rankOneSecularFunction_shift_split
    (V : Matrix I I ℂ) (lam : I → ℝ) (r : ℝ) (w : QState I) (σ : I)
    (hlamσ : lam σ = 1) (y : ℝ) :
    rankOneSecularFunction V lam r w (1+y) =
      ‖Qatlib.Foundations.PureStateMath.Inner w (fun j => V j σ)‖ ^ 2 / y +
        ∑ i ∈ Finset.univ \ {σ}, ‖Qatlib.Foundations.PureStateMath.Inner (fun j => V j i) w‖ ^ 2 /
          ((1-rescaledEigenvalue lam r i)+y) := by
  have hσ : rescaledEigenvalue lam r σ = 1 := by unfold rescaledEigenvalue; rw [hlamσ]; ring
  have hs : ‖Qatlib.Foundations.PureStateMath.Inner (fun j => V j σ) w‖ = ‖Qatlib.Foundations.PureStateMath.Inner w (fun j => V j σ)‖ := by
    rw [← inner_conj_state, norm_star]
  unfold rankOneSecularFunction
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ σ), hσ, hs,
    Finset.sdiff_singleton_eq_erase]
  simp only [add_sub_cancel_left]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ring

/-- Separate the distinguished eigenvalue-one contribution from the reciprocal second moment at
`1 + y`. -/
theorem rank_one_second_moment_shift_split
    (V : Matrix I I ℂ) (lam : I → ℝ) (r : ℝ) (w : QState I) (σ : I)
    (hlamσ : lam σ = 1) (y : ℝ) :
    (∑ i, ‖Qatlib.Foundations.PureStateMath.Inner (fun j => V j i) w‖ ^ 2 / ((1+y)-rescaledEigenvalue lam r i) ^ 2) =
      ‖Qatlib.Foundations.PureStateMath.Inner w (fun j => V j σ)‖ ^ 2 / y ^ 2 +
        ∑ i ∈ Finset.univ \ {σ}, ‖Qatlib.Foundations.PureStateMath.Inner (fun j => V j i) w‖ ^ 2 /
          ((1-rescaledEigenvalue lam r i)+y) ^ 2 := by
  have hσ : rescaledEigenvalue lam r σ = 1 := by unfold rescaledEigenvalue; rw [hlamσ]; ring
  have hs : ‖Qatlib.Foundations.PureStateMath.Inner (fun j => V j σ) w‖ = ‖Qatlib.Foundations.PureStateMath.Inner w (fun j => V j σ)‖ := by
    rw [← inner_conj_state, norm_star]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ σ), hσ, hs,
    Finset.sdiff_singleton_eq_erase]
  simp only [add_sub_cancel_left]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  ring

/-- Under calibration and a sufficiently small positive marked-state overlap, the secular
function equals one at two points on opposite sides of one, with the stated gap-dependent
bounds on their shifts. -/
theorem rank_one_two_level_positioning
    (V : Matrix I I ℂ) (lam : I → ℝ) (σ : I) (c r : ℝ) (w : QState I)
    (hV : V ∈ Matrix.unitaryGroup I ℂ) (hlamσ : lam σ = 1)
    (hlamc : ∀ i, i ≠ σ → |lam i| ≤ c) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hw : Normalized w) (hrlo : -c/(1+c) ≤ r) (_hrhi : r ≤ c/(1-c))
    (hεpos : 0 < ‖Qatlib.Foundations.PureStateMath.Inner w (fun j => V j σ)‖)
    (hεbound : ‖Qatlib.Foundations.PureStateMath.Inner w (fun j => V j σ)‖ ≤ searchOverlapBound c)
    (hcal : ∑ i ∈ Finset.univ \ {σ}, ‖Qatlib.Foundations.PureStateMath.Inner (fun j => V j i) w‖ ^ 2 /
        (1-rescaledEigenvalue lam r i) = 1-‖Qatlib.Foundations.PureStateMath.Inner w (fun j => V j σ)‖ ^ 2) :
    ∃ δp δm : ℝ,
      ‖Qatlib.Foundations.PureStateMath.Inner w (fun j => V j σ)‖ * Real.sqrt (spectralGapParam c/2) ≤ δp ∧
      δp ≤ spectralGapParam c/2 ∧
      ‖Qatlib.Foundations.PureStateMath.Inner w (fun j => V j σ)‖ * Real.sqrt (spectralGapParam c/2) ≤ δm ∧
      δm ≤ spectralGapParam c/2 ∧
      rankOneSecularFunction V lam r w (1+δp) = 1 ∧
      rankOneSecularFunction V lam r w (1-δm) = 1 := by
  let S := Finset.univ \ {σ}
  let a : I → ℝ := fun i => ‖Qatlib.Foundations.PureStateMath.Inner (fun j => V j i) w‖ ^ 2
  let g := fun i => 1-rescaledEigenvalue lam r i
  let ε := ‖Qatlib.Foundations.PureStateMath.Inner w (fun j => V j σ)‖
  let ν := spectralGapParam c
  have hν : 0 < ν := spectral_gap_param_pos hc0 hc1
  have hν1 : ν ≤ 1 := spectral_gap_param_le_one hc0 hc1
  have hhalf : ε ≤ 1/2 := (le_min_iff.1 hεbound).2
  have hsmall : ε ^ 2 ≤ ν ^ 3 / 64 := by
    have hb : ε ≤ ν ^ (3/2 : ℝ) / 8 := (le_min_iff.1 hεbound).1
    have hp : (ν ^ (3/2 : ℝ)) ^ 2 = ν ^ 3 := by
      rw [← Real.rpow_two, ← Real.rpow_mul hν.le]
      norm_num
    have hz : 0 ≤ ν ^ (3/2 : ℝ) := Real.rpow_nonneg hν.le _
    nlinarith
  have htot : (∑ i ∈ S, a i) = 1-ε ^ 2 := spectral_weights_off_top V w σ hV hw
  have hca : (∑ i ∈ S, a i / g i) = ∑ i ∈ S, a i := hcal.trans htot.symm
  have hgap (i : I) (hi : i ∈ S) : ν ≤ g i := by
    have hne : i ≠ σ := by simpa [S] using hi
    exact rescaled_spectral_gap_lower_bound lam c r i hc0 hc1 hrlo (hlamc i hne)
  obtain ⟨δp, δm, hpLo, hpHi, hmLo, hmHi, hrootp, hrootm⟩ :=
    rank_one_scalar_two_roots S a g ν ε (fun i _ => sq_nonneg _) hν hν1
      hgap hεpos hhalf hsmall htot hca
  refine ⟨δp, δm, hpLo, hpHi, hmLo, hmHi, ?_, ?_⟩
  · rw [rankOneSecularFunction_shift_split V lam r w σ hlamσ δp]
    exact hrootp
  · rw [show 1-δm = 1+(-δm) by ring,
      rankOneSecularFunction_shift_split V lam r w σ hlamσ (-δm)]
    simpa only [sub_eq_add_neg, div_neg, S, a, g, ε] using hrootm

/-- The state obtained by weighting each spectral column by its overlap with `w` divided by the
trial eigenvalue minus the rescaled eigenvalue. -/
noncomputable def rankOneSecularState (V : Matrix I I ℂ) (lam : I → ℝ)
    (r : ℝ) (w : QState I) (ℓ : ℝ) : QState I :=
  V *ᵥ (fun i => Qatlib.Foundations.PureStateMath.Inner (fun j => V j i) w /
    ((ℓ : ℂ) - (rescaledEigenvalue lam r i : ℂ)))

/-- The overlap of `w` with its secular state equals the real secular function, viewed as a
complex number. -/
theorem rankOneSecularState_overlap (V : Matrix I I ℂ) (lam : I → ℝ)
    (r : ℝ) (w : QState I) (ℓ : ℝ) :
    Qatlib.Foundations.PureStateMath.Inner w (rankOneSecularState V lam r w ℓ) =
      (rankOneSecularFunction V lam r w ℓ : ℂ) := by
  unfold rankOneSecularState
  rw [inner_mulVec_adjoint, inner_apply]
  unfold rankOneSecularFunction
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hi : (Vᴴ *ᵥ w) i = Qatlib.Foundations.PureStateMath.Inner (fun j => V j i) w := rfl
  rw [hi, ← mul_div_assoc, ← Complex.normSq_eq_conj_mul_self,
    Complex.normSq_eq_norm_sq, Complex.ofReal_div, Complex.ofReal_sub]

/-- A secular root away from all rescaled eigenvalues gives an eigenvector of the search
Hamiltonian with that root as eigenvalue. -/
theorem rank_one_secular_state_eigen
    (V : Matrix I I ℂ) (lam : I → ℝ) (r : ℝ) (w : QState I) (ℓ : ℝ)
    (hV : V ∈ Matrix.unitaryGroup I ℂ)
    (hne : ∀ i, ℓ ≠ rescaledEigenvalue lam r i)
    (hroot : rankOneSecularFunction V lam r w ℓ = 1) :
    searchHamiltonian V lam r w *ᵥ rankOneSecularState V lam r w ℓ =
      (ℓ : ℂ) • rankOneSecularState V lam r w ℓ := by
  let a : QState I := fun i => Qatlib.Foundations.PureStateMath.Inner (fun j => V j i) w
  let b : QState I := fun i => a i / ((ℓ : ℂ)-(rescaledEigenvalue lam r i : ℂ))
  have hVV : Vᴴ * V = 1 := by
    simpa only [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] using hV
  have hVV' : V * Vᴴ = 1 := by
    simpa only [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] using hV
  have hwV : V *ᵥ a = w := by
    change V *ᵥ (Vᴴ *ᵥ w) = w
    rw [Matrix.mulVec_mulVec, hVV', Matrix.one_mulVec]
  have hbV : Vᴴ *ᵥ (V *ᵥ b) = b := by
    rw [Matrix.mulVec_mulVec, hVV, Matrix.one_mulVec]
  have hspec : spectralHamiltonian V lam *ᵥ (V *ᵥ b) =
      V *ᵥ (fun i => (lam i : ℂ) * b i) := by
    unfold spectralHamiltonian
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hbV]
    congr 1
    ext i
    exact Matrix.mulVec_diagonal _ _ i
  have hwo : Qatlib.Foundations.PureStateMath.Inner w (rankOneSecularState V lam r w ℓ) = 1 := by
    rw [rankOneSecularState_overlap, hroot, Complex.ofReal_one]
  rw [searchHamiltonian, Matrix.add_mulVec, Matrix.sub_mulVec,
    Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    rankOneProjector_mulVec, hwo, one_smul]
  change (1+r) • (spectralHamiltonian V lam *ᵥ (V *ᵥ b)) -
    r • (V *ᵥ b) + w = (ℓ : ℂ) • (V *ᵥ b)
  rw [hspec, ← hwV, ← Matrix.mulVec_smul, ← Matrix.mulVec_smul,
    ← Matrix.mulVec_sub, ← Matrix.mulVec_add, ← Matrix.mulVec_smul]
  congr 1
  ext i
  have hn : (ℓ : ℂ)-(rescaledEigenvalue lam r i : ℂ) ≠ 0 := by
    exact_mod_cast sub_ne_zero.2 (hne i)
  simp only [a, b, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Complex.real_smul]
  field_simp
  simp only [rescaledEigenvalue, Complex.ofReal_sub, Complex.ofReal_mul,
    Complex.ofReal_add, Complex.ofReal_one]
  ring

/-- For unitary `V`, the squared norm of the secular state is its weighted reciprocal second
moment. -/
theorem rankOneSecularState_norm_sq
    (V : Matrix I I ℂ) (lam : I → ℝ) (r : ℝ) (w : QState I) (ℓ : ℝ)
    (hV : V ∈ Matrix.unitaryGroup I ℂ) :
    ‖toEuclidean_fromVec (rankOneSecularState V lam r w ℓ)‖ ^ 2 =
      ∑ i, ‖Qatlib.Foundations.PureStateMath.Inner (fun j => V j i) w‖ ^ 2 / (ℓ-rescaledEigenvalue lam r i) ^ 2 := by
  let b : QState I := fun i => Qatlib.Foundations.PureStateMath.Inner (fun j => V j i) w /
    ((ℓ : ℂ)-(rescaledEigenvalue lam r i : ℂ))
  have hi := inner_applyGate hV b b
  change Qatlib.Foundations.PureStateMath.Inner (rankOneSecularState V lam r w ℓ) (rankOneSecularState V lam r w ℓ) =
    Qatlib.Foundations.PureStateMath.Inner b b at hi
  rw [norm_toEuclidean_sq_eq_re_inner, hi, inner_self, Complex.re_sum]
  simp only [Complex.ofReal_re]
  apply Finset.sum_congr rfl
  intro i _
  simp only [b, norm_div, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, div_pow, sq_abs]

/-- A secular root away from the rescaled spectrum yields a normalized search-Hamiltonian
eigenstate whose squared overlap with `w` is the inverse reciprocal second moment. -/
theorem rank_one_normalized_secular_state
    (V : Matrix I I ℂ) (lam : I → ℝ) (r : ℝ) (w : QState I) (ℓ : ℝ)
    (hV : V ∈ Matrix.unitaryGroup I ℂ)
    (hne : ∀ i, ℓ ≠ rescaledEigenvalue lam r i)
    (hroot : rankOneSecularFunction V lam r w ℓ = 1) :
    ∃ x : QState I,
      searchHamiltonian V lam r w *ᵥ x = (ℓ : ℂ) • x ∧ Normalized x ∧
      ‖Qatlib.Foundations.PureStateMath.Inner w x‖ ^ 2 =
        (∑ i, ‖Qatlib.Foundations.PureStateMath.Inner (fun j => V j i) w‖ ^ 2 / (ℓ-rescaledEigenvalue lam r i) ^ 2)⁻¹ := by
  let u := rankOneSecularState V lam r w ℓ
  let n := ‖toEuclidean_fromVec u‖
  have hwu : Qatlib.Foundations.PureStateMath.Inner w u = 1 := by
    rw [rankOneSecularState_overlap, hroot, Complex.ofReal_one]
  have hn : n ≠ 0 := by
    intro hz
    have he : toEuclidean_fromVec u = 0 := norm_eq_zero.1 hz
    have hu : u = 0 := congrArg WithLp.ofLp he
    rw [hu] at hwu
    simp [Qatlib.Foundations.PureStateMath.Inner] at hwu
  let x : QState I := (n⁻¹ : ℂ) • u
  refine ⟨x, ?_, ?_, ?_⟩
  · change searchHamiltonian V lam r w *ᵥ ((n⁻¹ : ℂ) • u) = _
    rw [Matrix.mulVec_smul, rank_one_secular_state_eigen V lam r w ℓ hV hne hroot,
      smul_comm]
  · apply (normalized_iff_norm_toEuclidean_fromVec x).2
    change ‖(n⁻¹ : ℂ) • toEuclidean_fromVec u‖ = 1
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀ hn]
  · change ‖Qatlib.Foundations.PureStateMath.Inner w ((n⁻¹ : ℂ) • u)‖ ^ 2 = _
    rw [inner_smul_state, hwu, mul_one, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _), inv_pow]
    congr 1
    exact rankOneSecularState_norm_sq V lam r w ℓ hV

/-- For a search eigenstate with eigenvalue different from one, express its overlap with the
distinguished eigenvalue-one column using its overlap with `w` and the spectral shift. -/
theorem search_eigenstate_overlap_identity
    (V : Matrix I I ℂ) (lam : I → ℝ) (σ : I) (r : ℝ) (w x : QState I)
    (hV : V ∈ Matrix.unitaryGroup I ℂ) (hlamσ : lam σ = 1) (_hw : Normalized w)
    (ℓ : ℝ) (hℓ : ℓ ≠ 1)
    (hx : searchHamiltonian V lam r w *ᵥ x = (ℓ : ℂ) • x) :
    Qatlib.Foundations.PureStateMath.Inner (fun j => V j σ) x =
      Qatlib.Foundations.PureStateMath.Inner (fun j => V j σ) w * Qatlib.Foundations.PureStateMath.Inner w x / ((ℓ : ℂ) - 1) := by
  let s : QState I := fun j => V j σ
  have he : spectralHamiltonian V lam *ᵥ s = s := by
    simpa [s, hlamσ] using spectralHamiltonian_eigen V lam σ hV
  have hi : Qatlib.Foundations.PureStateMath.Inner s (spectralHamiltonian V lam *ᵥ x) = Qatlib.Foundations.PureStateMath.Inner s x := by
    rw [inner_mulVec_adjoint, (spectralHamiltonian_isHermitian V lam).eq, he]
  have hh := congrArg (Qatlib.Foundations.PureStateMath.Inner s) hx
  simp only [searchHamiltonian, Matrix.add_mulVec, Matrix.sub_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec, rankOneProjector_mulVec,
    inner_add_state, inner_sub_state] at hh
  have hr (a : ℝ) (y : QState I) : Qatlib.Foundations.PureStateMath.Inner s (a • y) = (a : ℂ) * Qatlib.Foundations.PureStateMath.Inner s y := by
    simpa only [Complex.real_smul] using! inner_smul_state s y (a : ℂ)
  rw [hr, hr, inner_smul_state, inner_smul_state, hi] at hh
  have hn : (ℓ : ℂ) - 1 ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hℓ
  apply (eq_div_iff hn).2
  simp only [Complex.ofReal_add, Complex.ofReal_one] at hh
  change Qatlib.Foundations.PureStateMath.Inner s x *
      ((ℓ : ℂ) - 1) = Qatlib.Foundations.PureStateMath.Inner s w * Qatlib.Foundations.PureStateMath.Inner w x
  linear_combination -hh

/-- The squared overlap of a search eigenstate with the distinguished column equals its squared
overlap with `w` times the distinguished weight divided by the squared spectral shift. -/
theorem search_eigenstate_top_overlap_sq
    (V : Matrix I I ℂ) (lam : I → ℝ) (σ : I) (r : ℝ) (w x : QState I)
    (hV : V ∈ Matrix.unitaryGroup I ℂ) (hlamσ : lam σ = 1) (hw : Normalized w)
    (ℓ : ℝ) (hℓ : ℓ ≠ 1)
    (hx : searchHamiltonian V lam r w *ᵥ x = (ℓ : ℂ) • x) :
    ‖Qatlib.Foundations.PureStateMath.Inner (fun j => V j σ) x‖ ^ 2 =
      (‖Qatlib.Foundations.PureStateMath.Inner w (fun j => V j σ)‖ ^ 2 / (ℓ-1) ^ 2) * ‖Qatlib.Foundations.PureStateMath.Inner w x‖ ^ 2 := by
  rw [search_eigenstate_overlap_identity V lam σ r w x hV hlamσ hw ℓ hℓ hx,
    norm_div, norm_mul, div_pow, mul_pow]
  have hs : ‖Qatlib.Foundations.PureStateMath.Inner (fun j => V j σ) w‖ = ‖Qatlib.Foundations.PureStateMath.Inner w (fun j => V j σ)‖ := by
    rw [← inner_conj_state, norm_star]
  have hd : ‖(ℓ : ℂ)-1‖ ^ 2 = (ℓ-1) ^ 2 := by
    rw [show (ℓ : ℂ)-1 = ((ℓ-1 : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hs, hd]
  ring

/-- Under the spectral, calibration, small-overlap, and root hypotheses, construct normalized
eigenstates at `1 + δp` and `1 - δm` with explicit lower bounds on their overlaps with both
`w` and the distinguished column. -/
theorem rank_one_two_level_states
    (V : Matrix I I ℂ) (lam : I → ℝ) (σ : I) (c r : ℝ) (w : QState I) (δp δm : ℝ)
    (hV : V ∈ Matrix.unitaryGroup I ℂ) (hlamσ : lam σ = 1)
    (hlamc : ∀ i, i ≠ σ → |lam i| ≤ c) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hw : Normalized w) (hrlo : -c/(1+c) ≤ r) (_hrhi : r ≤ c/(1-c))
    (hεpos : 0 < ‖Qatlib.Foundations.PureStateMath.Inner w (fun j => V j σ)‖)
    (hεbound : ‖Qatlib.Foundations.PureStateMath.Inner w (fun j => V j σ)‖ ≤ searchOverlapBound c)
    (hcal : ∑ i ∈ Finset.univ \ {σ}, ‖Qatlib.Foundations.PureStateMath.Inner (fun j => V j i) w‖ ^ 2 /
        (1-rescaledEigenvalue lam r i) = 1-‖Qatlib.Foundations.PureStateMath.Inner w (fun j => V j σ)‖ ^ 2)
    (hpLo : ‖Qatlib.Foundations.PureStateMath.Inner w (fun j => V j σ)‖*Real.sqrt (spectralGapParam c/2) ≤ δp)
    (hpHi : δp ≤ spectralGapParam c/2)
    (hmLo : ‖Qatlib.Foundations.PureStateMath.Inner w (fun j => V j σ)‖*Real.sqrt (spectralGapParam c/2) ≤ δm)
    (hmHi : δm ≤ spectralGapParam c/2)
    (hrootp : rankOneSecularFunction V lam r w (1+δp) = 1)
    (hrootm : rankOneSecularFunction V lam r w (1-δm) = 1) :
    ∃ up um : QState I,
      searchHamiltonian V lam r w *ᵥ up = ((1+δp : ℝ) : ℂ) • up ∧
      searchHamiltonian V lam r w *ᵥ um = ((1-δm : ℝ) : ℂ) • um ∧
      Normalized up ∧ Normalized um ∧
      spectralGapParam c/3 ≤ ‖Qatlib.Foundations.PureStateMath.Inner w up‖ ^ 2 ∧
      spectralGapParam c/6 ≤ ‖Qatlib.Foundations.PureStateMath.Inner w um‖ ^ 2 ∧
      (4/9 : ℝ) ≤ ‖Qatlib.Foundations.PureStateMath.Inner (fun j => V j σ) up‖ ^ 2 ∧
      (1/9 : ℝ) ≤ ‖Qatlib.Foundations.PureStateMath.Inner (fun j => V j σ) um‖ ^ 2 := by
  let S := Finset.univ \ {σ}
  let a : I → ℝ := fun i => ‖Qatlib.Foundations.PureStateMath.Inner (fun j => V j i) w‖ ^ 2
  let g := fun i => 1-rescaledEigenvalue lam r i
  let ε := ‖Qatlib.Foundations.PureStateMath.Inner w (fun j => V j σ)‖
  let ν := spectralGapParam c
  have hν : 0 < ν := spectral_gap_param_pos hc0 hc1
  have hν1 : ν ≤ 1 := spectral_gap_param_le_one hc0 hc1
  have hhalf : ε ≤ 1/2 := (le_min_iff.1 hεbound).2
  have hp : 0 < δp := (mul_pos hεpos (Real.sqrt_pos.2 (by linarith))).trans_le hpLo
  have hm : 0 < δm := (mul_pos hεpos (Real.sqrt_pos.2 (by linarith))).trans_le hmLo
  have hgap (i : I) (hi : i ∈ S) : ν ≤ g i := by
    have hne : i ≠ σ := by simpa [S] using hi
    exact rescaled_spectral_gap_lower_bound lam c r i hc0 hc1 hrlo (hlamc i hne)
  have hσ : rescaledEigenvalue lam r σ = 1 := by unfold rescaledEigenvalue; rw [hlamσ]; ring
  have hnep (i : I) : 1+δp ≠ rescaledEigenvalue lam r i := by
    by_cases hi : i = σ
    · subst i; rw [hσ]; linarith
    · have hb := hgap i (by simpa [S] using hi)
      dsimp [g] at hb
      linarith
  have hnem (i : I) : 1-δm ≠ rescaledEigenvalue lam r i := by
    by_cases hi : i = σ
    · subst i; rw [hσ]; linarith
    · have hb := hgap i (by simpa [S] using hi)
      dsimp [g] at hb
      linarith
  have htot : (∑ i ∈ S, a i) = 1-ε ^ 2 := spectral_weights_off_top V w σ hV hw
  have hca : (∑ i ∈ S, a i/g i) = ∑ i ∈ S, a i := hcal.trans htot.symm
  have hrp : ε ^ 2/δp + (∑ i ∈ S, a i/(g i+δp)) = 1 := by
    rw [rankOneSecularFunction_shift_split V lam r w σ hlamσ δp] at hrootp
    exact hrootp
  have hrm : -(ε ^ 2/δm) + (∑ i ∈ S, a i/(g i-δm)) = 1 := by
    rw [show 1-δm = 1+(-δm) by ring,
      rankOneSecularFunction_shift_split V lam r w σ hlamσ (-δm)] at hrootm
    simpa only [sub_eq_add_neg, div_neg, S, a, g, ε] using hrootm
  have hb := rank_one_scalar_overlap_bounds S a g ν ε δp δm
    (fun i _ => sq_nonneg _) hν hν1 hgap hεpos hhalf htot hca hpLo hpHi hmLo hmHi hrp hrm
  obtain ⟨up, heup, hnup, hγp⟩ := rank_one_normalized_secular_state V lam r w (1+δp) hV hnep hrootp
  obtain ⟨um, heum, hnum, hγm⟩ := rank_one_normalized_secular_state V lam r w (1-δm) hV hnem hrootm
  rw [rank_one_second_moment_shift_split V lam r w σ hlamσ δp] at hγp
  have hsplit := rank_one_second_moment_shift_split V lam r w σ hlamσ (-δm)
  have hsplitm : (∑ i, ‖Qatlib.Foundations.PureStateMath.Inner (fun j => V j i) w‖ ^ 2 /
      ((1-δm)-rescaledEigenvalue lam r i) ^ 2) =
      ε ^ 2/δm ^ 2 + ∑ i ∈ S, a i/(g i-δm) ^ 2 := by
    simpa only [sub_eq_add_neg, neg_sq, S, a, g, ε] using hsplit
  rw [hsplitm] at hγm
  refine ⟨up, um, heup, heum, hnup, hnum, ?_, ?_, ?_, ?_⟩
  · rw [hγp]; exact hb.1
  · rw [hγm]; exact hb.2.1
  · rw [search_eigenstate_top_overlap_sq V lam σ r w up hV hlamσ hw (1+δp)
      (by linarith) heup, add_sub_cancel_left, hγp]
    exact hb.2.2.1
  · rw [search_eigenstate_top_overlap_sq V lam σ r w um hV hlamσ hw (1-δm)
      (by linarith) heum, show (1-δm-1) ^ 2 = δm ^ 2 by ring, hγm]
    exact hb.2.2.2

/-- If a matrix is within operator norm `η` of the outer product of `s`, a normalized
eigenvector with real eigenvalue `ℓ` has squared overlap with `s` at least `ℓ - η`. -/
theorem operator_norm_overlap_stability
    (M : Matrix I I ℂ) (s x : QState I) (η ℓ : ℝ)
    (_hs : Normalized s) (hx : Normalized x) (_hη : 0 ≤ η)
    (hℓ : M *ᵥ x = (ℓ : ℂ) • x)
    (hnorm : ‖M - rankOneProjector s‖ ≤ η) :
    ℓ - η ≤ ‖Qatlib.Foundations.PureStateMath.Inner s x‖ ^ 2 := by
  have hxn : ‖toEuclidean_fromVec x‖ = 1 :=
    (normalized_iff_norm_toEuclidean_fromVec x).1 hx
  have hact : Qatlib.Foundations.PureStateMath.Inner x ((M - rankOneProjector s) *ᵥ x) =
      ((ℓ - ‖Qatlib.Foundations.PureStateMath.Inner s x‖ ^ 2 : ℝ) : ℂ) := by
    rw [Matrix.sub_mulVec, hℓ, rankOneProjector_mulVec, inner_sub_state,
      inner_smul_state, inner_smul_state, (normalized_iff_inner_self x).1 hx,
      ← inner_conj_state s x]
    simp only [mul_one, Complex.ofReal_sub, Complex.ofReal_pow]
    rw [RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [Complex.ofReal_pow]
  have hcs : ‖Qatlib.Foundations.PureStateMath.Inner x ((M - rankOneProjector s) *ᵥ x)‖ ≤ η := by
    have h := norm_inner_le_norm (𝕜 := ℂ) (toEuclidean_fromVec x)
      (toEuclidean_fromVec ((M - rankOneProjector s) *ᵥ x))
    rw [inner_euclidean_fromVec, hxn, one_mul] at h
    have hm := Matrix.l2_opNorm_mulVec (M - rankOneProjector s) (toEuclidean_fromVec x)
    change ‖toEuclidean_fromVec ((M - rankOneProjector s) *ᵥ x)‖ ≤
      ‖M - rankOneProjector s‖ * ‖toEuclidean_fromVec x‖ at hm
    rw [hxn, mul_one] at hm
    exact h.trans (hm.trans hnorm)
  rw [hact, Complex.norm_real, Real.norm_eq_abs] at hcs
  linarith [(le_abs_self (ℓ - ‖Qatlib.Foundations.PureStateMath.Inner s x‖ ^ 2)).trans hcs]

/-- The matrix exponential acts on an eigenvector by the scalar exponential of its eigenvalue. -/
theorem matrix_exp_mulVec_of_eigen (A : Matrix I I ℂ) (u : QState I) (z : ℂ)
    (hu : A *ᵥ u = z • u) :
    NormedSpace.exp A *ᵥ u = Complex.exp z • u := by
  let L : Matrix I I ℂ →L[ℂ] QState I :=
    ((Matrix.mulVecBilin ℂ ℂ).flip u).toContinuousLinearMap
  have hp (n : ℕ) : A ^ n *ᵥ u = z ^ n • u := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hu, smul_smul]
      rw [pow_succ, mul_comm]
  have hm := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A).mapL L
  have hs := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) z).smul_const u
  have he : (fun n => L ((n.factorial : ℂ)⁻¹ • A ^ n)) =
      (fun n => (((n.factorial : ℂ)⁻¹ • z ^ n) • u)) := by
    funext n
    change ((n.factorial : ℂ)⁻¹ • A ^ n) *ᵥ u = _
    rw [Matrix.smul_mulVec, hp, smul_smul]
    rfl
  rw [he] at hm
  rw [← Complex.exp_eq_exp_ℂ] at hs
  exact hm.unique hs

/-- Hamiltonian evolution multiplies an eigenvector of real eigenvalue `ℓ` by the phase `exp (-i
* t * ℓ)`. -/
theorem hamiltonianEvolution_eigenvector
    (H : Matrix I I ℂ) (u : QState I) (ℓ t : ℝ)
    (hu : H *ᵥ u = (ℓ : ℂ) • u) :
    HamiltonianEvolution H t *ᵥ u =
      Complex.exp ((-Complex.I*(t : ℂ))*(ℓ : ℂ)) • u := by
  unfold HamiltonianEvolution
  apply matrix_exp_mulVec_of_eigen
  rw [Matrix.smul_mulVec, hu, smul_smul]

omit [DecidableEq I] in

/-- Scaling the first state-inner-product argument multiplies the result by the conjugate
scalar. -/
theorem inner_smul_left_state (s x : QState I) (a : ℂ) :
    Qatlib.Foundations.PureStateMath.Inner (a • s) x = star a * Qatlib.Foundations.PureStateMath.Inner s x := by
  rw [← inner_euclidean_fromVec]
  change inner ℂ (a • toEuclidean_fromVec s) (toEuclidean_fromVec x) = _
  rw [inner_smul_left, inner_euclidean_fromVec]
  rfl

/-- For a Hermitian Hamiltonian, the adjoint of evolution at time `t` equals evolution at time
`-t`. -/
theorem hamiltonianEvolution_conjTranspose
    (H : Matrix I I ℂ) (hH : H.IsHermitian) (t : ℝ) :
    (HamiltonianEvolution H t)ᴴ = HamiltonianEvolution H (-t) := by
  unfold HamiltonianEvolution
  rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hH.eq]
  congr 2
  simp [RCLike.star_def, Complex.ofReal_neg]

/-- Adding a real scalar multiple of the identity to a Hamiltonian changes its evolution only by
the corresponding global phase. -/
theorem hamiltonianEvolution_shift_mulVec
    (H : Matrix I I ℂ) (a t : ℝ) (u : QState I) :
    HamiltonianEvolution (H+a • (1 : Matrix I I ℂ)) t *ᵥ u =
      Complex.exp ((-Complex.I*(t : ℂ))*(a : ℂ)) • (HamiltonianEvolution H t *ᵥ u) := by
  let z := -Complex.I*(t : ℂ)
  have he : z • (H+a • (1 : Matrix I I ℂ)) =
      z • H + (z*(a : ℂ)) • (1 : Matrix I I ℂ) := by
    ext i j
    simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, Complex.real_smul]
    ring
  unfold HamiltonianEvolution
  change NormedSpace.exp (z • (H+a • (1 : Matrix I I ℂ))) *ᵥ u = _
  rw [he, Matrix.exp_add_of_commute _ _ ((Commute.one_right (z • H)).smul_right (z*(a : ℂ))),
    ← Matrix.mulVec_mulVec,
    matrix_exp_mulVec_of_eigen ((z*(a : ℂ)) • (1 : Matrix I I ℂ)) u (z*(a : ℂ))
      (by rw [Matrix.smul_mulVec, Matrix.one_mulVec]), Matrix.mulVec_smul]

/-- For Hermitian `H` satisfying `H s = s + a • w` with nonzero `a`, the transition amplitudes
from `s` to `w` have equal magnitudes at opposite times. -/
theorem hamiltonianEvolution_rank_one_reciprocity
    (H : Matrix I I ℂ) (s w : QState I) (a : ℂ)
    (hH : H.IsHermitian) (ha : a ≠ 0) (hHs : H *ᵥ s = s+a • w) (t : ℝ) :
    ‖Qatlib.Foundations.PureStateMath.Inner w (HamiltonianEvolution H (-t) *ᵥ s)‖ =
      ‖Qatlib.Foundations.PureStateMath.Inner w (HamiltonianEvolution H t *ᵥ s)‖ := by
  let B := H-(1 : Matrix I I ℂ)
  have hB : B.IsHermitian := hH.sub Matrix.isHermitian_one
  have hBs : B *ᵥ s = a • w := by
    rw [Matrix.sub_mulVec, hHs, Matrix.one_mulVec, add_sub_cancel_left]
  have hBE (v : ℝ) : Commute B (HamiltonianEvolution H v) := by
    have h := ((Commute.refl H).smul_right (-Complex.I*(v : ℂ))).exp_right
    exact h.sub_left (Commute.one_left _)
  have hformula (v : ℝ) : Qatlib.Foundations.PureStateMath.Inner s ((B*HamiltonianEvolution H v) *ᵥ s) =
      star a * Qatlib.Foundations.PureStateMath.Inner w (HamiltonianEvolution H v *ᵥ s) := by
    rw [← Matrix.mulVec_mulVec, inner_mulVec_adjoint, hB.eq, hBs, inner_smul_left_state]
  have hmat : (B*HamiltonianEvolution H t)ᴴ = B*HamiltonianEvolution H (-t) := by
    rw [Matrix.conjTranspose_mul, hB.eq, hamiltonianEvolution_conjTranspose H hH t]
    exact (hBE (-t)).eq.symm
  have hstar : star (Qatlib.Foundations.PureStateMath.Inner s ((B*HamiltonianEvolution H t) *ᵥ s)) =
      Qatlib.Foundations.PureStateMath.Inner s ((B*HamiltonianEvolution H (-t)) *ᵥ s) := by
    rw [inner_conj_state, ← hmat, inner_mulVec_adjoint, Matrix.conjTranspose_conjTranspose]
  have hn := congrArg norm hstar
  simp only [norm_star, hformula, norm_mul] at hn
  exact (mul_left_cancel₀ (norm_ne_zero_iff.2 ha) hn).symm

/-- The coefficient `δp * δm` divided by the distinguished-column overlap with `w` and by `δp +
δm`. -/
noncomputable def rankOneResonantCoefficient (V : Matrix I I ℂ) (w : QState I)
    (σ : I) (δp δm : ℝ) : ℂ :=
  ((δp*δm : ℝ) : ℂ) / (Qatlib.Foundations.PureStateMath.Inner (fun j => V j σ) w * ((δp+δm : ℝ) : ℂ))

omit [DecidableEq I] in

/-- For positive shifts, the norm of the resonant coefficient is `δp * δm` divided by the
overlap magnitude times `δp + δm`. -/
theorem rankOneResonantCoefficient_norm (V : Matrix I I ℂ) (w : QState I)
    (σ : I) (δp δm : ℝ) (hp : 0 < δp) (hm : 0 < δm) :
    ‖rankOneResonantCoefficient V w σ δp δm‖ =
      δp*δm/(‖Qatlib.Foundations.PureStateMath.Inner w (fun j => V j σ)‖*(δp+δm)) := by
  have hs : ‖Qatlib.Foundations.PureStateMath.Inner (fun j => V j σ) w‖ = ‖Qatlib.Foundations.PureStateMath.Inner w (fun j => V j σ)‖ := by
    rw [← inner_conj_state, norm_star]
  simp only [rankOneResonantCoefficient, norm_div, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hp, abs_of_pos hm, abs_of_pos (add_pos hp hm), hs]

/-- Multiplication by a unitary matrix preserves the squared Euclidean norm of a state. -/
theorem unitary_mulVec_euclidean_norm_sq
    (V : Matrix I I ℂ) (x : QState I) (hV : V ∈ Matrix.unitaryGroup I ℂ) :
    ‖toEuclidean_fromVec (V *ᵥ x)‖ ^ 2 = ‖toEuclidean_fromVec x‖ ^ 2 := by
  rw [norm_toEuclidean_sq_eq_re_inner, norm_toEuclidean_sq_eq_re_inner]
  exact congrArg Complex.re (inner_applyGate hV x x)

section ResonantRemainder
set_option maxHeartbeats 1000000

/-- Express the squared error in representing the distinguished column by a scaled difference of
two secular states as an explicit weighted sum over the other columns. -/
theorem rank_one_resonant_remainder_norm_sq
    (V : Matrix I I ℂ) (lam : I → ℝ) (w : QState I) (σ : I) (r ν δp δm : ℝ)
    (hV : V ∈ Matrix.unitaryGroup I ℂ) (hlamσ : lam σ = 1)
    (hε : 0 < ‖Qatlib.Foundations.PureStateMath.Inner w (fun j => V j σ)‖)
    (_hν : 0 < ν) (hp : 0 < δp) (hm : 0 < δm) (hmHi : δm ≤ ν/2)
    (hgap : ∀ i, i ≠ σ → ν ≤ 1-rescaledEigenvalue lam r i) :
    ‖toEuclidean_fromVec ((fun j => V j σ) - rankOneResonantCoefficient V w σ δp δm •
      (rankOneSecularState V lam r w (1+δp)-rankOneSecularState V lam r w (1-δm)))‖ ^ 2 =
      (δp*δm/‖Qatlib.Foundations.PureStateMath.Inner w (fun j => V j σ)‖) ^ 2 *
        ∑ i ∈ Finset.univ \ {σ}, ‖Qatlib.Foundations.PureStateMath.Inner (fun j => V j i) w‖ ^ 2 /
          (((1-rescaledEigenvalue lam r i)+δp)*((1-rescaledEigenvalue lam r i)-δm)) ^ 2 := by
  let a : QState I := fun i => Qatlib.Foundations.PureStateMath.Inner (fun j => V j i) w
  let g := fun i => 1-rescaledEigenvalue lam r i
  let k := rankOneResonantCoefficient V w σ δp δm
  let bp : QState I := fun i => a i / (((1+δp : ℝ) : ℂ)-(rescaledEigenvalue lam r i : ℂ))
  let bm : QState I := fun i => a i / (((1-δm : ℝ) : ℂ)-(rescaledEigenvalue lam r i : ℂ))
  let e : QState I := Pi.single σ 1 - k • (bp-bm)
  have hs : ‖a σ‖ = ‖Qatlib.Foundations.PureStateMath.Inner w (fun j => V j σ)‖ := by
    rw [← inner_conj_state, norm_star]
  have haσ : a σ ≠ 0 := norm_ne_zero_iff.1 (by rw [hs]; exact hε.ne')
  have hσ : rescaledEigenvalue lam r σ = 1 := by unfold rescaledEigenvalue; rw [hlamσ]; ring
  have hp0 : (δp : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hm0 : (δm : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hsum0 : ((δp+δm : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (add_pos hp hm).ne'
  push_cast at hsum0
  have hcoord : (fun j => V j σ) - k •
      (rankOneSecularState V lam r w (1+δp)-rankOneSecularState V lam r w (1-δm)) = V *ᵥ e := by
    change V.col σ - k • (V *ᵥ bp - V *ᵥ bm) = V *ᵥ (Pi.single σ 1-k • (bp-bm))
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_single_one]
  have heσ : e σ = 0 := by
    simp only [e, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, bp, bm, hσ,
      Complex.ofReal_one, Complex.ofReal_add, Complex.ofReal_sub, Pi.single_eq_same]
    dsimp [k, rankOneResonantCoefficient]
    change 1 - ((δp*δm : ℝ) : ℂ)/(a σ*((δp+δm : ℝ) : ℂ)) *
      (a σ/((1 : ℂ)+(δp : ℂ)-1)-a σ/((1 : ℂ)-(δm : ℂ)-1)) = 0
    rw [add_sub_cancel_left, show (1 : ℂ)-(δm : ℂ)-1 = -(δm : ℂ) by ring]
    push_cast
    field_simp [haσ, hp0, hm0, hsum0]
    ring
  have hei (i : I) (hi : i ≠ σ) : e i =
      (((δp*δm : ℝ) : ℂ)/a σ) * a i / (((g i+δp)*(g i-δm) : ℝ) : ℂ) := by
    have hgp : 0 < g i+δp := by dsimp [g]; linarith [hgap i hi]
    have hgm : 0 < g i-δm := by dsimp [g]; linarith [hgap i hi]
    have hgp0 : ((g i+δp : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hgp.ne'
    have hgm0 : ((g i-δm : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hgm.ne'
    have hdp : ((1+δp : ℝ) : ℂ)-(rescaledEigenvalue lam r i : ℂ) = ((g i+δp : ℝ) : ℂ) := by
      dsimp [g]; push_cast; ring
    have hdm : ((1-δm : ℝ) : ℂ)-(rescaledEigenvalue lam r i : ℂ) = ((g i-δm : ℝ) : ℂ) := by
      dsimp [g]; push_cast; ring
    have hz : (Pi.single σ (1 : ℂ) : QState I) i = 0 := by simp [hi]
    simp only [e, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, bp, bm, hz, hdp, hdm]
    dsimp [k, rankOneResonantCoefficient]
    change 0 - ((δp*δm : ℝ) : ℂ)/(a σ*((δp+δm : ℝ) : ℂ)) *
      (a i/((g i+δp : ℝ) : ℂ)-a i/((g i-δm : ℝ) : ℂ)) = _
    push_cast at hgp0 hgm0 ⊢
    field_simp [haσ, hsum0, hgp0, hgm0]
    ring
  rw [hcoord, unitary_mulVec_euclidean_norm_sq V e hV, norm_toEuclidean_fromVec_sq,
    ← Finset.sum_erase_add _ _ (Finset.mem_univ σ), heσ]
  simp only [norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero]
  rw [Finset.sdiff_singleton_eq_erase, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hne : i ≠ σ := (Finset.mem_erase.1 hi).1
  rw [hei i hne]
  have hgp : 0 ≤ g i+δp := by
    have hg := hgap i hne
    change ν ≤ g i at hg
    linarith
  have hgm : 0 ≤ g i-δm := by
    have hg := hgap i hne
    change ν ≤ g i at hg
    linarith
  simp only [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hp, abs_of_pos hm, abs_of_nonneg hgp, abs_of_nonneg hgm, hs,
    div_pow, mul_pow, a, g]
  ring

end ResonantRemainder

/-- Under calibration, spectral-gap, and secular-root hypotheses, the squared resonant
approximation error is at most four times the distinguished overlap squared divided by
`ν^2`. -/
theorem rank_one_resonant_remainder_bound
    (V : Matrix I I ℂ) (lam : I → ℝ) (w : QState I) (σ : I) (r ν δp δm : ℝ)
    (hV : V ∈ Matrix.unitaryGroup I ℂ) (hlamσ : lam σ = 1) (hw : Normalized w)
    (hε : 0 < ‖Qatlib.Foundations.PureStateMath.Inner w (fun j => V j σ)‖) (hεhalf : ‖Qatlib.Foundations.PureStateMath.Inner w (fun j => V j σ)‖ ≤ 1/2)
    (hν : 0 < ν) (hp : 0 < δp) (hm : 0 < δm) (hpHi : δp ≤ ν/2) (hmHi : δm ≤ ν/2)
    (hgap : ∀ i, i ≠ σ → ν ≤ 1-rescaledEigenvalue lam r i)
    (hcal : ∑ i ∈ Finset.univ \ {σ}, ‖Qatlib.Foundations.PureStateMath.Inner (fun j => V j i) w‖ ^ 2 /
        (1-rescaledEigenvalue lam r i) = 1-‖Qatlib.Foundations.PureStateMath.Inner w (fun j => V j σ)‖ ^ 2)
    (hrootp : rankOneSecularFunction V lam r w (1+δp) = 1)
    (hrootm : rankOneSecularFunction V lam r w (1-δm) = 1) :
    ‖toEuclidean_fromVec ((fun j => V j σ) - rankOneResonantCoefficient V w σ δp δm •
      (rankOneSecularState V lam r w (1+δp)-rankOneSecularState V lam r w (1-δm)))‖ ^ 2 ≤
      4*‖Qatlib.Foundations.PureStateMath.Inner w (fun j => V j σ)‖ ^ 2/ν ^ 2 := by
  let S := Finset.univ \ {σ}
  let a := fun i => ‖Qatlib.Foundations.PureStateMath.Inner (fun j => V j i) w‖ ^ 2
  let g := fun i => 1-rescaledEigenvalue lam r i
  let ε := ‖Qatlib.Foundations.PureStateMath.Inner w (fun j => V j σ)‖
  have htot : (∑ i ∈ S, a i) = 1-ε ^ 2 := spectral_weights_off_top V w σ hV hw
  have hca : (∑ i ∈ S, a i/g i) = ∑ i ∈ S, a i := hcal.trans htot.symm
  have hg (i : I) (hi : i ∈ S) : ν ≤ g i := hgap i (by simpa [S] using hi)
  have hrp : ε ^ 2/δp + (∑ i ∈ S, a i/(g i+δp)) = 1 := by
    rw [rankOneSecularFunction_shift_split V lam r w σ hlamσ δp] at hrootp
    exact hrootp
  have hrm : -(ε ^ 2/δm) + (∑ i ∈ S, a i/(g i-δm)) = 1 := by
    rw [show 1-δm = 1+(-δm) by ring,
      rankOneSecularFunction_shift_split V lam r w σ hlamσ (-δm)] at hrootm
    simpa only [sub_eq_add_neg, div_neg, S, a, g, ε] using hrootm
  rw [rank_one_resonant_remainder_norm_sq V lam w σ r ν δp δm hV hlamσ hε hν hp hm hmHi hgap]
  exact rank_one_scalar_remainder_bound S a g ν ε δp δm (fun i _ => sq_nonneg _)
    hν hg hε hεhalf hp hm hpHi hmHi htot hca hrp hrm

/-- At time `π / (δp + δm)`, the phases associated with eigenvalues `1 - δm` and `1 + δp` differ
by a minus sign. -/
theorem rank_one_resonant_phase_flip (δp δm : ℝ) (hp : 0 < δp) (hm : 0 < δm) :
    Complex.exp ((-Complex.I*((Real.pi/(δp+δm) : ℝ) : ℂ))*((1-δm : ℝ) : ℂ)) =
      -Complex.exp ((-Complex.I*((Real.pi/(δp+δm) : ℝ) : ℂ))*((1+δp : ℝ) : ℂ)) := by
  have hn : ((δp+δm : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (add_pos hp hm).ne'
  push_cast at hn
  have he : (-Complex.I*((Real.pi/(δp+δm) : ℝ) : ℂ))*((1-δm : ℝ) : ℂ) =
      (-Complex.I*((Real.pi/(δp+δm) : ℝ) : ℂ))*((1+δp : ℝ) : ℂ)+(Real.pi : ℂ)*Complex.I := by
    push_cast
    field_simp [hn]
    ring
  rw [he, Complex.exp_add_pi_mul_I]

/-- If the two eigenstates have overlap one with `w`, evolution of `k • (up - um)` at the
resonant time has overlap magnitude `2 * ‖k‖` with `w`. -/
theorem rank_one_resonant_main_amplitude
    (H : Matrix I I ℂ) (w up um : QState I) (k : ℂ) (δp δm : ℝ)
    (hp : 0 < δp) (hm : 0 < δm)
    (hup : H *ᵥ up = ((1+δp : ℝ) : ℂ) • up)
    (hum : H *ᵥ um = ((1-δm : ℝ) : ℂ) • um)
    (hwu : Qatlib.Foundations.PureStateMath.Inner w up = 1) (hwm : Qatlib.Foundations.PureStateMath.Inner w um = 1) :
    ‖Qatlib.Foundations.PureStateMath.Inner w (HamiltonianEvolution H (Real.pi/(δp+δm)) *ᵥ (k • (up-um)))‖ = 2*‖k‖ := by
  rw [Matrix.mulVec_smul, Matrix.mulVec_sub,
    hamiltonianEvolution_eigenvector H up (1+δp) _ hup,
    hamiltonianEvolution_eigenvector H um (1-δm) _ hum,
    inner_smul_state, inner_sub_state, inner_smul_state, inner_smul_state,
    hwu, hwm, mul_one, mul_one, rank_one_resonant_phase_flip δp δm hp hm]
  let p := Complex.exp ((-Complex.I*((Real.pi/(δp+δm) : ℝ) : ℂ))*((1+δp : ℝ) : ℂ))
  have hp1 : ‖p‖ = 1 := by
    have he : (-Complex.I*((Real.pi/(δp+δm) : ℝ) : ℂ))*((1+δp : ℝ) : ℂ) =
        ((-(Real.pi/(δp+δm))*(1+δp) : ℝ) : ℂ)*Complex.I := by push_cast; ring
    dsimp [p]
    rw [he, Complex.norm_exp_ofReal_mul_I]
  change ‖k*(p-(-p))‖ = _
  rw [show k*(p-(-p)) = (2 : ℂ)*k*p by ring, norm_mul, norm_mul, hp1]
  norm_num

/-- For a Hermitian Hamiltonian, the stated lower bound on the resonant coefficient and upper
bound on the approximation remainder imply squared transition amplitude at least `ν / 8` at
the resonant time. -/
theorem rank_one_resonant_probability_bound
    (H : Matrix I I ℂ) (w s up um : QState I) (k : ℂ) (ν δp δm : ℝ)
    (hH : H.IsHermitian) (hw : Normalized w) (hν : 0 < ν)
    (hp : 0 < δp) (hm : 0 < δm)
    (hup : H *ᵥ up = ((1+δp : ℝ) : ℂ) • up)
    (hum : H *ᵥ um = ((1-δm : ℝ) : ℂ) • um)
    (hwu : Qatlib.Foundations.PureStateMath.Inner w up = 1) (hwm : Qatlib.Foundations.PureStateMath.Inner w um = 1)
    (hk : (2/3 : ℝ)*Real.sqrt ν ≤ 2*‖k‖)
    (hrem : ‖toEuclidean_fromVec (s-k • (up-um))‖ ^ 2 ≤ ν/16) :
    ν/8 ≤ ‖Qatlib.Foundations.PureStateMath.Inner w (HamiltonianEvolution H (Real.pi/(δp+δm)) *ᵥ s)‖ ^ 2 := by
  let t := Real.pi/(δp+δm)
  let q := k • (up-um)
  let e := s-q
  have hmain : ‖Qatlib.Foundations.PureStateMath.Inner w (HamiltonianEvolution H t *ᵥ q)‖ = 2*‖k‖ :=
    rank_one_resonant_main_amplitude H w up um k δp δm hp hm hup hum hwu hwm
  have hnorm := unitary_mulVec_euclidean_norm_sq (HamiltonianEvolution H t) e
    (hamiltonianEvolution_unitary hH t)
  have he : ‖toEuclidean_fromVec (HamiltonianEvolution H t *ᵥ e)‖ ≤ Real.sqrt ν/4 := by
    have hs := Real.sq_sqrt hν.le
    have hn := norm_nonneg (toEuclidean_fromVec (HamiltonianEvolution H t *ᵥ e))
    have hsn := Real.sqrt_nonneg ν
    change ‖toEuclidean_fromVec e‖ ^ 2 ≤ ν/16 at hrem
    nlinarith only [hnorm, hrem, hs, hn, hsn]
  have hcs := norm_inner_le_norm (𝕜 := ℂ) (toEuclidean_fromVec w)
    (toEuclidean_fromVec (HamiltonianEvolution H t *ᵥ e))
  rw [inner_euclidean_fromVec, (normalized_iff_norm_toEuclidean_fromVec w).1 hw, one_mul] at hcs
  have herr :
      ‖Qatlib.Foundations.PureStateMath.Inner w
      (HamiltonianEvolution H t *ᵥ e)‖ ≤ Real.sqrt ν/4 := hcs.trans he
  have htri : ‖Qatlib.Foundations.PureStateMath.Inner w (HamiltonianEvolution H t *ᵥ q)‖ ≤
      ‖Qatlib.Foundations.PureStateMath.Inner w (HamiltonianEvolution H t *ᵥ s)‖ + ‖Qatlib.Foundations.PureStateMath.Inner w (HamiltonianEvolution H t *ᵥ e)‖ := by
    rw [show q = s-e by dsimp [e]; abel, Matrix.mulVec_sub, inner_sub_state]
    exact norm_sub_le _ _
  rw [hmain] at htri
  have hl : (5/12 : ℝ)*Real.sqrt ν ≤ ‖Qatlib.Foundations.PureStateMath.Inner w (HamiltonianEvolution H t *ᵥ s)‖ := by
    linarith only [htri, herr, hk]
  have hsq := mul_self_le_mul_self (by positivity : 0 ≤ (5/12 : ℝ)*Real.sqrt ν) hl
  nlinarith only [hsq, Real.sq_sqrt hν.le]

end Qatlib.Concepts.WalkSearch.RankOneSpectralSearch.RankOneSpectralSearch
