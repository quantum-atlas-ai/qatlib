/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.GroverInterp.GroverGeometryAux
import Qatlib.Concepts.WalkFind.GroverInterp.UnitarySpectrumAux
import Qatlib.Concepts.WalkFind.GroverInterp.GroverTrigAux
import Mathlib.Topology.Order.IntermediateValue
import Qatlib.Concepts.WalkFind.GroverInterp.GroverResolventAux
import Qatlib.Concepts.WalkFind.GroverInterp.GroverInterpolationStat
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Instances.Matrix

/-!
# Grover interpolation via secular equations

This module proves `GroverInterpolation` by analyzing the resolvent of a unitary walk and its
product with a reflection. The scalar `groverSecularScalar` encodes the eigenphase equation;
spectral decompositions and normalization estimates give an iteration bound and a lower bound on
the target overlap.

The mathematical background is developed in [Ambainis2007ElementDistinctness].

## Main statements

* `grover_small_overlap_root`: constructs a secular root in an explicit phase interval.
* `groverInterpolation`: proves the interpolation statement for a walk with the stated phase
  gap.

## References

* [Ambainis, 2007][Ambainis2007ElementDistinctness]
-/

set_option warningAsError false

namespace Qatlib.Concepts.WalkFind.GroverInterp

open Matrix

/-- If the initial overlap is at least `ε^3 / 1000`, zero iterations satisfy the required
overlap and iteration bounds. -/
theorem groverInterpolation_at_zero (m : ℕ) (ε α : ℝ)
    (hε : 0 < ε) (hα : 0 < α) (hbig : ε^3 / 1000 ≤ α)
    (Uf Uw : Matrix (Fin m) (Fin m) ℂ) (start good : Fin m → ℂ)
    (hoverlap : (∑ i, star (good i) * start i) = (α : ℂ)) :
    ∃ t : ℕ, (t : ℝ) ≤ 8 / (ε * α) ∧
      ε^3 / 1000 ≤ ‖∑ i, star (good i) * ((Uw * Uf)^t *ᵥ start) i‖ := by
  refine ⟨0, ?_, ?_⟩
  · simp only [Nat.cast_zero]
    positivity
  · simpa only [pow_zero, Matrix.one_mulVec, hoverlap, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hα] using! hbig

/-- For `0 < ε ≤ 1`, an initial overlap of at least `ε^2 / 200` already satisfies the
interpolation conclusion. -/
theorem groverInterpolation_large_overlap (m : ℕ) (ε α : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hα : 0 < α) (hlarge : ε^2 / 200 ≤ α)
    (Uf Uw : Matrix (Fin m) (Fin m) ℂ) (start good : Fin m → ℂ)
    (hoverlap : (∑ i, star (good i) * start i) = (α : ℂ)) :
    ∃ t : ℕ, (t : ℝ) ≤ 8 / (ε * α) ∧
      ε^3 / 1000 ≤ ‖∑ i, star (good i) * ((Uw * Uf)^t *ᵥ start) i‖ := by
  apply groverInterpolation_at_zero m ε α hε hα _ Uf Uw start good hoverlap
  have hmul := mul_nonneg (sq_nonneg ε) (sub_nonneg.mpr hε1)
  nlinarith [sq_nonneg ε]

/-- A map that negates the unit vector `good` and fixes its orthogonal complement acts by
subtracting twice the projection onto `good`. -/
theorem groverReflection_action {m : ℕ} (Uf : Matrix (Fin m) (Fin m) ℂ)
    (good : Fin m → ℂ) (hn : (∑ i, ‖good i‖^2) = 1)
    (hgood : Uf *ᵥ good = -good)
    (hfix : ∀ v : Fin m → ℂ, (∑ i, star (v i)*good i) = 0 → Uf *ᵥ v = v)
    (v : Fin m → ℂ) :
    Uf *ᵥ v = v - (2 * ∑ i, star (good i)*v i) • good := by
  let c : ℂ := ∑ i, star (good i)*v i
  have hgn : star good ⬝ᵥ good = 1 := by
    have he (i : Fin m) : star (good i)*good i = ((‖good i‖^2 : ℝ) : ℂ) := by
      rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    simp only [dotProduct, Pi.star_apply, he, ← Complex.ofReal_sum, hn, Complex.ofReal_one]
  have hvc : star v ⬝ᵥ good = star c := by
    simp only [dotProduct, Pi.star_apply, c, star_sum, star_mul, star_star]
  have hw : star (v-c • good) ⬝ᵥ good = 0 := by
    rw [star_sub, sub_dotProduct, star_smul, smul_dotProduct, hgn, hvc]
    simp
  have h := hfix (v-c • good) hw
  rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hgood, smul_neg, sub_neg_eq_add] at h
  change Uf *ᵥ v = v - (2*c) • good
  calc
    _ = (v-c • good)-c • good := eq_sub_iff_add_eq.mpr h
    _ = _ := by module

/-- Distinct ordered phases in `[0, 2π)` have distinct complex exponentials. -/
theorem grover_phase_ne_of_order (a b : ℝ) (ha : 0 ≤ a) (hab : a < b)
    (hb : b < 2 * Real.pi) :
    Complex.exp (Complex.I * a) ≠ Complex.exp (Complex.I * b) := by
  intro h
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  have hi : a = b + (n : ℝ) * (2 * Real.pi) := by
    simpa using! congrArg Complex.im hn
  have hnlo : (-1 : ℝ) < n := by nlinarith [Real.pi_pos]
  have hnhi : (n : ℝ) < 0 := by nlinarith [Real.pi_pos]
  have hnlo' : (-1 : ℤ) < n := by exact_mod_cast hnlo
  have hnhi' : n < 0 := by exact_mod_cast hnhi
  omega

/-- An eigenvector of a unitary matrix with eigenvalue different from one is orthogonal to every
fixed vector. -/
theorem grover_eigenvector_orthogonal_start (m : ℕ)
    (U : Matrix (Fin m) (Fin m) ℂ) (start w : Fin m → ℂ) (z : ℂ)
    (hu : star U * U = 1) (hstart : U *ᵥ start = start)
    (heigen : U *ᵥ w = z • w) (hz : z ≠ 1) :
    (∑ i, star (w i) * start i) = 0 := by
  have hadj : star U *ᵥ start = start := by
    calc
      _ = star U *ᵥ (U *ᵥ start) := by rw [hstart]
      _ = start := by rw [Matrix.mulVec_mulVec, hu, Matrix.one_mulVec]
  have hrow : star start ᵥ* U = star start := by
    simpa only [Matrix.star_mulVec, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose] using! congrArg star hadj
  have hc : z * (star start ⬝ᵥ w) = star start ⬝ᵥ w := by
    calc
      _ = star start ⬝ᵥ (U *ᵥ w) := by rw [heigen, dotProduct_smul, smul_eq_mul]
      _ = _ := by rw [Matrix.dotProduct_mulVec, hrow]
  have hc0 : star start ⬝ᵥ w = 0 := by
    have hm : (z - 1) * (star start ⬝ᵥ w) = 0 := by linear_combination hc
    exact (mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr hz)
  have hs : star (∑ i, star (w i) * start i) = 0 := by
    simpa [dotProduct, star_sum, star_mul, mul_comm] using! hc0
  exact star_eq_zero.mp hs

/-- The resolvent matrix at a phase strictly between zero and `ε` is invertible under the stated
spectral phase condition. -/
theorem grover_resolvent_isUnit (m : ℕ) (ε β : ℝ) (_hε : 0 < ε) (hε1 : ε ≤ 1)
    (hβ : 0 < β) (hβε : β < ε)
    (U : Matrix (Fin m) (Fin m) ℂ) (start : Fin m → ℂ)
    (hu : star U * U = 1) (hstart : U *ᵥ start = start)
    (hphase : ∀ (ν : ℂ) (v : Fin m → ℂ), U *ᵥ v = ν • v →
      (∑ i, star (v i) * start i) = 0 → v ≠ 0 →
      ∃ θ : ℝ, ε ≤ θ ∧ θ ≤ 2 * Real.pi - ε ∧ θ ≠ Real.pi ∧
        ν = Complex.exp (Complex.I * θ)) :
    IsUnit (U - Complex.exp (Complex.I * β) • (1 : Matrix (Fin m) (Fin m) ℂ)) := by
  classical
  let z := Complex.exp (Complex.I * β)
  have hz : z ≠ 1 := by
    by_contra h
    have hx := grover_phase_ne_of_order 0 β (by norm_num) hβ
    have htop : β < 2 * Real.pi := by linarith [Real.pi_gt_three]
    apply hx htop
    simpa [z] using! h.symm
  have hker (w : Fin m → ℂ)
      (hw : (U - z • (1 : Matrix (Fin m) (Fin m) ℂ)) *ᵥ w = 0) : w = 0 := by
    have he : U *ᵥ w = z • w := by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hw
      exact sub_eq_zero.mp hw
    by_contra hnw
    have ho := grover_eigenvector_orthogonal_start m U start w z hu hstart he hz
    obtain ⟨θ, hlo, hhi, _, heq⟩ := hphase z w he ho hnw
    exact grover_phase_ne_of_order β θ hβ.le (hβε.trans_le hlo) (by linarith) heq
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y hxy
  have hw : (U - z • (1 : Matrix (Fin m) (Fin m) ℂ)) *ᵥ (x - y) = 0 := by
    rw [Matrix.mulVec_sub, hxy, sub_self]
  exact sub_eq_zero.mp (hker (x - y) hw)

/-- A resolvent vector whose overlap with `good` equals one half is a nonzero eigenvector of `U
* Uf` with eigenvalue `z`. -/
theorem grover_resolvent_search_eigenvector (m : ℕ)
    (Uf U : Matrix (Fin m) (Fin m) ℂ) (good : Fin m → ℂ) (z : ℂ)
    (hn : (∑ i, ‖good i‖ ^ 2) = 1) (hgood : Uf *ᵥ good = -good)
    (hfix : ∀ v : Fin m → ℂ, (∑ i, star (v i) * good i) = 0 → Uf *ᵥ v = v)
    (hinv : IsUnit (U - z • (1 : Matrix (Fin m) (Fin m) ℂ)))
    (hroot : (∑ i, star (good i) *
      ((U - z • (1 : Matrix (Fin m) (Fin m) ℂ))⁻¹ *ᵥ (U *ᵥ good)) i) = 1 / 2) :
    let y := (U - z • (1 : Matrix (Fin m) (Fin m) ℂ))⁻¹ *ᵥ (U *ᵥ good)
    (U * Uf) *ᵥ y = z • y ∧ y ≠ 0 := by
  classical
  let A := U - z • (1 : Matrix (Fin m) (Fin m) ℂ)
  let y := A⁻¹ *ᵥ (U *ᵥ good)
  change (U * Uf) *ᵥ y = z • y ∧ y ≠ 0
  have hAy : U *ᵥ y - z • y = U *ᵥ good := by
    have hd := (Matrix.isUnit_iff_isUnit_det A).mp hinv
    have he : A *ᵥ y = U *ᵥ good := by
      dsimp only [y]
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hd, Matrix.one_mulVec]
    simpa only [A, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] using! he
  have hc : (2 : ℂ) * (∑ i, star (good i) * y i) = 1 := by
    change (2 : ℂ) * (∑ i, star (good i) *
      ((U - z • (1 : Matrix (Fin m) (Fin m) ℂ))⁻¹ *ᵥ (U *ᵥ good)) i) = 1
    rw [hroot]
    norm_num
  constructor
  · rw [← Matrix.mulVec_mulVec, groverReflection_action Uf good hn hgood hfix y,
      hc, one_smul, Matrix.mulVec_sub]
    rw [sub_eq_iff_eq_add] at hAy
    rw [hAy]
    module
  · intro hzero
    simp [hzero] at hc

/-- For a unitary matrix, a unit target vector, and a resolvent parameter on the unit circle,
the resolvent overlap has real part one half. -/
theorem grover_resolvent_real_part (m : ℕ)
    (U : Matrix (Fin m) (Fin m) ℂ) (good : Fin m → ℂ) (z : ℂ)
    (hu : star U * U = 1) (hgood : (∑ i, ‖good i‖ ^ 2) = 1)
    (hz : star z * z = 1)
    (hinv : IsUnit (U - z • (1 : Matrix (Fin m) (Fin m) ℂ))) :
    (∑ i, star (good i) *
      ((U - z • (1 : Matrix (Fin m) (Fin m) ℂ))⁻¹ *ᵥ (U *ᵥ good)) i).re = 1 / 2 := by
  classical
  let A := U - z • (1 : Matrix (Fin m) (Fin m) ℂ)
  let y := A⁻¹ *ᵥ (U *ᵥ good)
  change (star good ⬝ᵥ y).re = 1 / 2
  have hAy : U *ᵥ (y - good) = z • y := by
    have hd := (Matrix.isUnit_iff_isUnit_det A).mp hinv
    have he : A *ᵥ y = U *ᵥ good := by
      dsimp only [y]
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hd, Matrix.one_mulVec]
    have he' : U *ᵥ y - z • y = U *ᵥ good := by
      simpa only [A, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] using! he
    rw [sub_eq_iff_eq_add] at he'
    rw [Matrix.mulVec_sub, he']
    module
  have hunit (x : Fin m → ℂ) : star (U *ᵥ x) ⬝ᵥ (U *ᵥ x) = star x ⬝ᵥ x := by
    have hu' := hu
    rw [Matrix.star_eq_conjTranspose] at hu'
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
      hu', Matrix.vecMul_one]
  have hgg : star good ⬝ᵥ good = 1 := by
    have he (i : Fin m) : star (good i) * good i = ((‖good i‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    simp only [dotProduct, Pi.star_apply, he, ← Complex.ofReal_sum, hgood, Complex.ofReal_one]
  have hconj : star y ⬝ᵥ good = star (star good ⬝ᵥ y) := by
    simp [dotProduct, star_sum, star_mul, mul_comm]
  have he := hunit (y - good)
  rw [hAy, star_smul, smul_dotProduct, dotProduct_smul, smul_smul,
    hz, one_smul, star_sub, sub_dotProduct, dotProduct_sub,
    dotProduct_sub, hconj, hgg] at he
  have hre := congrArg Complex.re he
  simp only [Complex.sub_re, Complex.star_def, Complex.conj_re, Complex.one_re] at hre
  linarith

/-- The imaginary part of the overlap of `good` with the resolvent vector at phase `β`. -/
noncomputable def groverSecularScalar (m : ℕ)
    (U : Matrix (Fin m) (Fin m) ℂ) (good : Fin m → ℂ) (β : ℝ) : ℝ :=
  (star good ⬝ᵥ
    ((U - Complex.exp (Complex.I * β) • (1 : Matrix (Fin m) (Fin m) ℂ))⁻¹ *ᵥ
      (U *ᵥ good))).im

/-- Under the spectral phase condition, the secular scalar is continuous on the open interval
`(0, ε)`. -/
theorem grover_secular_continuousOn (m : ℕ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (U : Matrix (Fin m) (Fin m) ℂ) (start good : Fin m → ℂ)
    (hu : star U * U = 1) (hstart : U *ᵥ start = start)
    (hphase : ∀ (ν : ℂ) (v : Fin m → ℂ), U *ᵥ v = ν • v →
      (∑ i, star (v i) * start i) = 0 → v ≠ 0 →
      ∃ θ : ℝ, ε ≤ θ ∧ θ ≤ 2 * Real.pi - ε ∧ θ ≠ Real.pi ∧
        ν = Complex.exp (Complex.I * θ)) :
    ContinuousOn (groverSecularScalar m U good) (Set.Ioo 0 ε) := by
  intro β hβ
  let A : ℝ → Matrix (Fin m) (Fin m) ℂ := fun b =>
    U - Complex.exp (Complex.I * b) • (1 : Matrix (Fin m) (Fin m) ℂ)
  have hA : Continuous A := by dsimp only [A]; fun_prop
  have hi := grover_resolvent_isUnit m ε β hε hε1 hβ.1 hβ.2 U start hu hstart hphase
  have hd : IsUnit (A β).det := (Matrix.isUnit_iff_isUnit_det _).mp hi
  have hdi : ContinuousAt Ring.inverse (A β).det := by
    rw [← hd.unit_spec]
    exact NormedRing.inverse_continuousAt hd.unit
  have hinv : ContinuousAt (fun b => (A b)⁻¹) β :=
    (continuousAt_matrix_inv _ hdi).comp hA.continuousAt
  have hF : Continuous (fun B : Matrix (Fin m) (Fin m) ℂ =>
      (star good ⬝ᵥ (B *ᵥ (U *ᵥ good))).im) := by
    unfold dotProduct Matrix.mulVec
    fun_prop
  exact (hF.continuousAt.comp hinv).continuousWithinAt

/-- The resolvent overlap splits into the fixed-vector contribution `α^2 / (1 - z)` and the
contribution from `good - α • start`. -/
theorem grover_resolvent_overlap_decomposition (m : ℕ) (α : ℝ)
    (U : Matrix (Fin m) (Fin m) ℂ) (start good : Fin m → ℂ) (z : ℂ)
    (hu : star U * U = 1) (hstart : U *ᵥ start = start)
    (hsn : (∑ i, ‖start i‖ ^ 2) = 1)
    (hoverlap : (∑ i, star (good i) * start i) = (α : ℂ))
    (hz : z ≠ 1) (hinv : IsUnit (U - z • (1 : Matrix (Fin m) (Fin m) ℂ))) :
    let A := U - z • (1 : Matrix (Fin m) (Fin m) ℂ)
    let b := good - (α : ℂ) • start
    star good ⬝ᵥ (A⁻¹ *ᵥ (U *ᵥ good)) =
      (α : ℂ) ^ 2 / (1 - z) + star b ⬝ᵥ (A⁻¹ *ᵥ (U *ᵥ b)) := by
  classical
  let A := U - z • (1 : Matrix (Fin m) (Fin m) ℂ)
  let b := good - (α : ℂ) • start
  let y := A⁻¹ *ᵥ (U *ᵥ good)
  let yb := A⁻¹ *ᵥ (U *ᵥ b)
  change star good ⬝ᵥ y = (α : ℂ) ^ 2 / (1 - z) + star b ⬝ᵥ yb
  have hd := (Matrix.isUnit_iff_isUnit_det A).mp hinv
  have hzn : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have hAstart : A *ᵥ start = (1 - z) • start := by
    dsimp only [A]
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hstart]
    module
  have hInvStart : A⁻¹ *ᵥ start = (1 - z)⁻¹ • start := by
    have he := congrArg (fun x => A⁻¹ *ᵥ x) hAstart
    change A⁻¹ *ᵥ (A *ᵥ start) = A⁻¹ *ᵥ ((1 - z) • start) at he
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hd, Matrix.one_mulVec,
      Matrix.mulVec_smul] at he
    have ht := congrArg (fun x => (1 - z)⁻¹ • x) he
    simpa only [smul_smul, inv_mul_cancel₀ hzn, one_smul] using! ht.symm
  have hy : y = (α / (1 - z) : ℂ) • start + yb := by
    dsimp only [yb, b]
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hstart,
      Matrix.mulVec_sub, Matrix.mulVec_smul, hInvStart, smul_smul]
    dsimp only [y]
    rw [div_eq_mul_inv]
    module
  have hsn' : star start ⬝ᵥ start = 1 := by
    have he (i : Fin m) : star (start i) * start i = ((‖start i‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    simp only [dotProduct, Pi.star_apply, he, ← Complex.ofReal_sum, hsn, Complex.ofReal_one]
  have hbs : star b ⬝ᵥ start = 0 := by
    simp only [b, star_sub, sub_dotProduct, star_smul, smul_dotProduct,
      Complex.star_def, Complex.conj_ofReal, hsn', smul_eq_mul, mul_one]
    exact sub_eq_zero.mpr hoverlap
  have hsg : star start ⬝ᵥ good = (α : ℂ) := by
    have he := congrArg star hoverlap
    simpa [dotProduct, star_sum, star_mul, mul_comm] using! he
  have hadj : star U *ᵥ start = start := by
    calc
      _ = star U *ᵥ (U *ᵥ start) := by rw [hstart]
      _ = start := by rw [Matrix.mulVec_mulVec, hu, Matrix.one_mulVec]
  have hrow : star start ᵥ* U = star start := by
    simpa only [Matrix.star_mulVec, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose] using! congrArg star hadj
  have hAy : U *ᵥ y - z • y = U *ᵥ good := by
    have he : A *ᵥ y = U *ᵥ good := by
      dsimp only [y]
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hd, Matrix.one_mulVec]
    simpa only [A, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] using! he
  have hsY : star start ⬝ᵥ y = (α / (1 - z) : ℂ) := by
    have he := congrArg (fun x => star start ⬝ᵥ x) hAy
    change star start ⬝ᵥ (U *ᵥ y - z • y) = star start ⬝ᵥ (U *ᵥ good) at he
    have hfun (x : Fin m → ℂ) : star start ⬝ᵥ (U *ᵥ x) = star start ⬝ᵥ x := by
      rw [Matrix.dotProduct_mulVec, hrow]
    rw [dotProduct_sub, hfun y, hfun good, dotProduct_smul, hsg, smul_eq_mul] at he
    apply (eq_div_iff hzn).mpr
    linear_combination he
  have hgs : star good = (α : ℂ) • star start + star b := by
    simp only [b, star_sub, star_smul, Complex.star_def, Complex.conj_ofReal]
    module
  rw [hgs, add_dotProduct, smul_dotProduct, hsY, hy, dotProduct_add,
    dotProduct_smul, hbs, smul_zero, zero_add, smul_eq_mul]
  ring

/-- Entrywise complex conjugation commutes with the matrix inverse. -/
theorem grover_conjugate_inverse (m : ℕ) (A : Matrix (Fin m) (Fin m) ℂ) :
    (A⁻¹).map star = (A.map star)⁻¹ := by
  have h := Matrix.conjTranspose_nonsing_inv A.transpose
  rw [← Matrix.transpose_nonsing_inv] at h
  simpa only [Matrix.conjTranspose_transpose] using! h

/-- Complex conjugation of a matrix-vector product equals the product of the entrywise
conjugates. -/
private theorem conjugate_mulVec (m : ℕ) (A : Matrix (Fin m) (Fin m) ℂ)
    (v : Fin m → ℂ) :
    star (A *ᵥ v) = A.map star *ᵥ star v := by
  funext i
  simp [Matrix.mulVec,dotProduct,star_sum,star_mul,mul_comm]

/-- For real matrix and vector entries, conjugating the resolvent overlap conjugates its
spectral parameter. -/
theorem grover_resolvent_overlap_conjugate (m : ℕ)
    (U : Matrix (Fin m) (Fin m) ℂ) (good : Fin m → ℂ) (z : ℂ)
    (hU : ∀ i j, (U i j).im = 0) (hg : ∀ i, (good i).im = 0) :
    star (star good ⬝ᵥ ((U-z • (1 : Matrix (Fin m) (Fin m) ℂ))⁻¹ *ᵥ (U *ᵥ good))) =
      star good ⬝ᵥ ((U-star z • (1 : Matrix (Fin m) (Fin m) ℂ))⁻¹ *ᵥ (U *ᵥ good)) := by
  have hUr : U.map star = U := by
    ext i j
    exact Complex.conj_eq_iff_im.mpr (hU i j)
  have hgr : star good = good := by
    funext i
    exact Complex.conj_eq_iff_im.mpr (hg i)
  have he : (U-z • (1 : Matrix (Fin m) (Fin m) ℂ)).map star =
      U-star z • (1 : Matrix (Fin m) (Fin m) ℂ) := by
    ext i j
    change star (U i j - z*(if i = j then 1 else 0)) =
      U i j - star z*(if i = j then 1 else 0)
    have hc : ∀ i j, star (U i j) = U i j := fun i j => Complex.conj_eq_iff_im.mpr (hU i j)
    by_cases hij : i = j <;> simp [hij,hc]
  have hs (y : Fin m → ℂ) : star (star good ⬝ᵥ y) = good ⬝ᵥ star y := by
    simp [dotProduct,star_sum,star_mul,mul_comm]
  rw [hs,conjugate_mulVec,grover_conjugate_inverse,he,conjugate_mulVec,hUr]
  simp only [hgr]

/-- For real matrix and target entries, the secular scalar is an odd function of the phase. -/
theorem grover_secular_neg (m : ℕ) (U : Matrix (Fin m) (Fin m) ℂ) (good : Fin m → ℂ)
    (hU : ∀ i j, (U i j).im = 0) (hg : ∀ i, (good i).im = 0) (β : ℝ) :
    groverSecularScalar m U good (-β) = -groverSecularScalar m U good β := by
  have hz : star (Complex.exp (Complex.I*β)) = Complex.exp (Complex.I*(-β)) := by
    simp [← Complex.exp_conj]
  have h := grover_resolvent_overlap_conjugate m U good (Complex.exp (Complex.I*β)) hU hg
  rw [hz] at h
  have he := congrArg Complex.im h
  simpa [groverSecularScalar,Complex.star_def] using! he.symm

 /-- For an entrywise real matrix, invertibility of a resolvent is preserved by conjugating its
 parameter. -/
 theorem grover_real_resolvent_isUnit_conjugate (m : ℕ)
    (U : Matrix (Fin m) (Fin m) ℂ) (z : ℂ)
    (hU : ∀ i j, (U i j).im = 0)
    (hz : IsUnit (U - z • 1)) : IsUnit (U - star z • 1) := by
  have he : (U-z • (1 : Matrix (Fin m) (Fin m) ℂ)).map star =
      U-star z • (1 : Matrix (Fin m) (Fin m) ℂ) := by
    ext i j
    change star (U i j - z*(if i = j then 1 else 0)) =
      U i j - star z*(if i = j then 1 else 0)
    have hc : ∀ i j, star (U i j) = U i j := fun i j => Complex.conj_eq_iff_im.mpr (hU i j)
    by_cases hij : i = j <;> simp [hij,hc]
  rw [Matrix.isUnit_iff_isUnit_det]
  have hd := (Matrix.isUnit_iff_isUnit_det _).mp hz
  have hs := isUnit_star.mpr hd
  have hm := (starRingEnd ℂ).map_det (U - z • (1 : Matrix (Fin m) (Fin m) ℂ))
  change star (U - z • (1 : Matrix (Fin m) (Fin m) ℂ)).det =
    ((U - z • (1 : Matrix (Fin m) (Fin m) ℂ)).map star).det at hm
  rw [he] at hm
  rw [← hm]
  exact hs

/-- The symmetric resolvent matrix is invertible, and its inverse expresses the secular scalar
after multiplication by `sin β`. -/
theorem grover_secular_symmetric_resolvent (m : ℕ)
    (U : Matrix (Fin m) (Fin m) ℂ) (good : Fin m → ℂ) (β : ℝ)
    (hu : star U * U = 1) (hU : ∀ i j, (U i j).im = 0)
    (hg : ∀ i, (good i).im = 0)
    (hinv : IsUnit (U - Complex.exp (Complex.I * β) • 1)) :
    let K := U + star U - ((2 * Real.cos β : ℝ) : ℂ) • 1
    IsUnit K ∧ groverSecularScalar m U good β =
      Real.sin β * (star good ⬝ᵥ (K⁻¹ *ᵥ good)).re := by
  let z := Complex.exp (Complex.I * β)
  have hw := grover_real_resolvent_isUnit_conjugate m U z hU hinv
  have hzw : star z * z = 1 := by
    rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    rw [show -Complex.I * (β : ℂ) + Complex.I * β = 0 by ring, Complex.exp_zero]
  have hzre : z.re = Real.cos β := by
    dsimp only [z]
    rw [mul_comm, Complex.exp_ofReal_mul_I_re]
  have hzim : z.im = Real.sin β := by
    dsimp only [z]
    rw [mul_comm, Complex.exp_ofReal_mul_I_im]
  have hsum : z + star z = ((2 * Real.cos β : ℝ) : ℂ) := by
    apply Complex.ext <;> simp only [Complex.add_re, Complex.add_im,
      Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
      Complex.ofReal_im, hzre]
    · ring
    · ring
  obtain ⟨hK, he⟩ := grover_paired_resolvent m U z (star z) hu hzw hinv hw
  rw [hsum] at hK he
  refine ⟨hK, ?_⟩
  have hs := grover_resolvent_overlap_conjugate m U good z hU hg
  have hd := congrArg (fun B => star good ⬝ᵥ (B *ᵥ good)) he

  rw [Matrix.sub_mulVec, dotProduct_sub, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at hd
  rw [← hs] at hd
  have him := congrArg Complex.im hd
  simp only [Complex.sub_im, Complex.star_def, Complex.conj_im, Complex.mul_im, Complex.sub_re,
    Complex.conj_re, sub_self, zero_mul, hzim] at him
  dsimp only [groverSecularScalar]
  change (star good ⬝ᵥ ((U-z • 1)⁻¹ *ᵥ (U *ᵥ good))).im = _
  linarith

/-- Opposite weak endpoint signs yield a secular root in `[a, b]` and a nonzero search
eigenvector at that phase. -/
theorem grover_secular_root_of_signs (m : ℕ) (ε a b : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (ha : 0 < a) (hab : a ≤ b) (hb : b < ε)
    (Uf U : Matrix (Fin m) (Fin m) ℂ) (start good : Fin m → ℂ)
    (hu : star U * U = 1) (hstart : U *ᵥ start = start)
    (hgn : (∑ i, ‖good i‖ ^ 2) = 1)
    (hgood : Uf *ᵥ good = -good)
    (hfix : ∀ v : Fin m → ℂ, (∑ i, star (v i) * good i) = 0 → Uf *ᵥ v = v)
    (hphase : ∀ (ν : ℂ) (v : Fin m → ℂ), U *ᵥ v = ν • v →
      (∑ i, star (v i) * start i) = 0 → v ≠ 0 →
      ∃ θ : ℝ, ε ≤ θ ∧ θ ≤ 2 * Real.pi - ε ∧ θ ≠ Real.pi ∧
        ν = Complex.exp (Complex.I * θ))
    (hlo : 0 ≤ groverSecularScalar m U good a)
    (hhi : groverSecularScalar m U good b ≤ 0) :
    ∃ β ∈ Set.Icc a b,
      let z := Complex.exp (Complex.I * β)
      let y := (U - z • (1 : Matrix (Fin m) (Fin m) ℂ))⁻¹ *ᵥ (U *ᵥ good)
      groverSecularScalar m U good β = 0 ∧
        (star good ⬝ᵥ y) = 1 / 2 ∧ (U * Uf) *ᵥ y = z • y ∧ y ≠ 0 := by
  have hc := grover_secular_continuousOn m ε hε hε1 U start good hu hstart hphase
  have hc' := hc.mono (Set.Icc_subset_Ioo ha hb)
  obtain ⟨β, hβ, hroot⟩ := intermediate_value_Icc' hab hc' (show (0 : ℝ) ∈
      Set.Icc (groverSecularScalar m U good b) (groverSecularScalar m U good a) from ⟨hhi, hlo⟩)
  let z := Complex.exp (Complex.I * β)
  let y := (U - z • (1 : Matrix (Fin m) (Fin m) ℂ))⁻¹ *ᵥ (U *ᵥ good)
  have hi := grover_resolvent_isUnit m ε β hε hε1 (ha.trans_le hβ.1)
    (hβ.2.trans_lt hb) U start hu hstart hphase
  have hz : star z * z = 1 := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    simp only [z, Complex.norm_exp_I_mul_ofReal, one_pow, Complex.ofReal_one]
  have hre := grover_resolvent_real_part m U good z hu hgn hz hi
  have hcomplex : star good ⬝ᵥ y = (1 / 2 : ℂ) := by
    apply Complex.ext
    · change (star good ⬝ᵥ y).re = 1 / 2 at hre
      convert! hre using 1
      norm_num
    · change (star good ⬝ᵥ y).im = 0 at hroot
      convert! hroot using 1
      norm_num
  have he := grover_resolvent_search_eigenvector m Uf U good z hgn hgood hfix hi hcomplex
  exact ⟨β, hβ, hroot, hcomplex, he⟩

/-- The imaginary part of `α^2 / (1 - exp (I * β))` equals `α^2 * sin β / (2 * (1 - cos β))`. -/
theorem grover_fixed_pole_im (α β : ℝ) :
    (((α : ℂ)^2 / (1 - Complex.exp (Complex.I * β))).im) =
      α^2 * Real.sin β / (2 * (1 - Real.cos β)) := by
  have hre : (Complex.exp (Complex.I * β)).re = Real.cos β := by
    rw [mul_comm, Complex.exp_ofReal_mul_I_re]
  have him : (Complex.exp (Complex.I * β)).im = Real.sin β := by
    rw [mul_comm, Complex.exp_ofReal_mul_I_im]
  have hnorm : Complex.normSq (1 - Complex.exp (Complex.I * β)) =
      2 * (1 - Real.cos β) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im, hre, him]
    nlinarith [Real.sin_sq_add_cos_sq β]
  rw [Complex.div_im, hnorm]
  simp only [← Complex.ofReal_pow, Complex.ofReal_re,
    Complex.ofReal_im, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, hre, him]
  ring

/-- An orthonormal eigenbasis expresses the secular scalar as a sum weighted by the squared
target coefficients. -/
theorem grover_secular_eigenbasis (m : ℕ)
    (U B : Matrix (Fin m) (Fin m) ℂ) (μ : Fin m → ℂ)
    (good : Fin m → ℂ) (β : ℝ)
    (hu : star U * U = 1) (hU : ∀ i j, (U i j).im = 0)
    (hg : ∀ i, (good i).im = 0) (hB : B * star B = 1)
    (hμ : ∀ j, ‖μ j‖ = 1)
    (he : ∀ j, U *ᵥ (fun i => B i j) = μ j • (fun i => B i j))
    (hinv : IsUnit (U - Complex.exp (Complex.I * β) • 1)) :
    groverSecularScalar m U good β = Real.sin β / 2 *
      ∑ j, ‖(star B *ᵥ good) j‖^2 / ((μ j).re - Real.cos β) := by
  let K := U + star U - ((2 * Real.cos β : ℝ) : ℂ) • 1
  obtain ⟨hK, hscalar⟩ := grover_secular_symmetric_resolvent m U good β hu hU hg hinv
  have heK (j : Fin m) : K *ᵥ (fun i => B i j) =
      ((2 * ((μ j).re - Real.cos β) : ℝ) : ℂ) • (fun i => B i j) := by
    have hnorm : star (μ j) * μ j = 1 := by
      rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
      simp only [hμ, one_pow, Complex.ofReal_one]
    exact grover_symmetric_eigenvector m U (fun i => B i j) (μ j) (Real.cos β) hu hnorm (he j)
  have hsum := grover_inverse_overlap_eigenbasis m K B
    (fun j => ((2 * ((μ j).re - Real.cos β) : ℝ) : ℂ)) hB hK heK good
  change groverSecularScalar m U good β = Real.sin β * (star good ⬝ᵥ (K⁻¹ *ᵥ good)).re at hscalar
  rw [hscalar, hsum, Complex.re_sum]
  have ht (j : Fin m) :
      (star ((star B *ᵥ good) j) * ((star B *ᵥ good) j) /
        ((2 * ((μ j).re - Real.cos β) : ℝ) : ℂ)).re =
      (‖(star B *ᵥ good) j‖^2 / ((μ j).re - Real.cos β)) / 2 := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq, ← Complex.ofReal_div, Complex.ofReal_re]
    rw [mul_comm 2, div_mul_eq_div_div]
  simp_rw [ht]
  rw [← Finset.sum_div]
  ring

/-- The secular scalar splits into the explicit fixed-vector pole and the scalar for the
orthogonal residual target. -/
theorem grover_secular_orthogonal_decomposition (m : ℕ) (α β : ℝ)
    (U : Matrix (Fin m) (Fin m) ℂ) (start good : Fin m → ℂ)
    (hu : star U * U = 1) (hstart : U *ᵥ start = start)
    (hsn : (∑ i, ‖start i‖ ^ 2) = 1)
    (hoverlap : (∑ i, star (good i) * start i) = (α : ℂ))
    (hz : Complex.exp (Complex.I * β) ≠ 1)
    (hinv : IsUnit (U - Complex.exp (Complex.I * β) • 1)) :
    groverSecularScalar m U good β =
      α^2 * Real.sin β / (2 * (1 - Real.cos β)) +
        groverSecularScalar m U (good - (α : ℂ) • start) β := by
  have h := grover_resolvent_overlap_decomposition m α U start good
    (Complex.exp (Complex.I * β)) hu hstart hsn hoverlap hz hinv
  dsimp only at h
  have hi := congrArg Complex.im h
  rw [Complex.add_im, grover_fixed_pole_im] at hi
  exact hi

/-- After removing the fixed-vector component, the secular scalar is the fixed pole minus a sum
over nonfixed eigenvalues, scaled by `sin β / 2`. -/
theorem grover_secular_nonfixed_eigenbasis (m : ℕ) (α β : ℝ)
    (U B : Matrix (Fin m) (Fin m) ℂ) (μ : Fin m → ℂ)
    (start good : Fin m → ℂ)
    (hu : star U * U = 1) (hU : ∀ i j, (U i j).im = 0)
    (hstart : U *ᵥ start = start) (hsr : ∀ i, (start i).im = 0)
    (hgr : ∀ i, (good i).im = 0) (hsn : (∑ i, ‖start i‖ ^ 2) = 1)
    (hoverlap : (∑ i, star (good i) * start i) = (α : ℂ))
    (hB : B * star B = 1) (hμ : ∀ j, ‖μ j‖ = 1)
    (he : ∀ j, U *ᵥ (fun i => B i j) = μ j • (fun i => B i j))
    (hzero : ∀ j, μ j = 1 → (star B *ᵥ (good - (α : ℂ) • start)) j = 0)
    (hz : Complex.exp (Complex.I * β) ≠ 1)
    (hinv : IsUnit (U - Complex.exp (Complex.I * β) • 1)) :
    groverSecularScalar m U good β = Real.sin β / 2 *
      (α^2 / (1 - Real.cos β) -
        ∑ j with μ j ≠ 1, ‖(star B *ᵥ (good - (α : ℂ) • start)) j‖^2 /
          (Real.cos β - (μ j).re)) := by
  classical
  let b := good - (α : ℂ) • start
  have hbr (i : Fin m) : (b i).im = 0 := by
    change (good i - (α : ℂ) * start i).im = 0
    simp [Complex.sub_im, Complex.mul_im, hgr, hsr]
  have hbscalar := grover_secular_eigenbasis m U B μ b β hu hU hbr hB hμ he hinv
  have hsum : (∑ j, ‖(star B *ᵥ b) j‖^2 / ((μ j).re - Real.cos β)) =
      -(∑ j with μ j ≠ 1, ‖(star B *ᵥ b) j‖^2 / (Real.cos β - (μ j).re)) := by
    rw [← Finset.sum_neg_distrib, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : μ j = 1
    · simp only [hj, ne_eq, not_true_eq_false, if_false]
      rw [show (star B *ᵥ b) j = 0 from hzero j hj]
      simp
    · simp only [hj, ne_eq, not_false_eq_true, if_true]
      rw [← neg_sub (Real.cos β) (μ j).re, div_neg]
  rw [hsum] at hbscalar
  rw [grover_secular_orthogonal_decomposition m α β U start good hu hstart hsn hoverlap hz hinv]
  change α^2 * Real.sin β / (2*(1-Real.cos β)) + groverSecularScalar m U b β = _
  rw [hbscalar]
  dsimp only [b]
  simp only [div_eq_mul_inv, _root_.mul_inv_rev]
  ring

/-- The secular scalar is expressed using separate fixed and nonfixed spectral weights and the
modified real eigenvalue denominators. -/
theorem grover_secular_gap_weights (m : ℕ)
    (U B : Matrix (Fin m) (Fin m) ℂ) (μ : Fin m → ℂ)
    (good : Fin m → ℂ) (α β : ℝ) (w s : Fin m → ℝ)
    (hu : star U * U = 1) (hU : ∀ i j, (U i j).im = 0)
    (hg : ∀ i, (good i).im = 0) (hB : B * star B = 1)
    (hμ : ∀ j, ‖μ j‖ = 1)
    (he : ∀ j, U *ᵥ (fun i => B i j) = μ j • (fun i => B i j))
    (hw : ∀ j, μ j = 1 → w j = 0) (hs : ∀ j, μ j ≠ 1 → s j = 0)
    (hsum : (∑ j, s j) = 1)
    (hweights : ∀ j, ‖(star B *ᵥ good) j‖^2 = w j + α^2 * s j)
    (hinv : IsUnit (U - Complex.exp (Complex.I * β) • 1)) :
    groverSecularScalar m U good β = Real.sin β / 2 *
      (α^2 / (1 - Real.cos β) - ∑ j,
        w j / (Real.cos β - if μ j = 1 then -1 else (μ j).re)) := by
  rw [grover_secular_eigenbasis m U B μ good β hu hU hg hB hμ he hinv]
  simp_rw [hweights]
  rw [grover_weighted_pole_split m μ w s α (Real.cos β) hw hs hsum]

/-- Under the small-overlap and spectral hypotheses, a secular root lies between `ε * α / sqrt
(2π)` and `13 * α / 5` and yields a nonzero search eigenvector
[Ambainis2007ElementDistinctness]. -/
theorem grover_small_overlap_root (m : ℕ) (ε α : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hα : 0 < α) (hsmall : α ≤ ε^2 / 200)
    (Uf U : Matrix (Fin m) (Fin m) ℂ) (start good : Fin m → ℂ)
    (hu : star U * U = 1) (hU : ∀ i j, (U i j).im = 0)
    (hg : ∀ i, (good i).im = 0)
    (hsn : (∑ i, ‖start i‖^2) = 1) (hgn : (∑ i, ‖good i‖^2) = 1)
    (hoverlap : (∑ i, star (good i) * start i) = (α : ℂ))
    (hstart : U *ᵥ start = start) (hgood : Uf *ᵥ good = -good)
    (hfix : ∀ v : Fin m → ℂ, (∑ i, star (v i) * good i) = 0 → Uf *ᵥ v = v)
    (hphase : ∀ (ν : ℂ) (v : Fin m → ℂ), U *ᵥ v = ν • v →
      (∑ i, star (v i) * start i) = 0 → v ≠ 0 →
      ∃ θ : ℝ, ε ≤ θ ∧ θ ≤ 2 * Real.pi - ε ∧ θ ≠ Real.pi ∧
        ν = Complex.exp (Complex.I * θ)) :
    ∃ β ∈ Set.Icc (ε * α / Real.sqrt (2 * Real.pi)) ((13/5 : ℝ)*α),
      let z := Complex.exp (Complex.I * β)
      let y := (U - z • (1 : Matrix (Fin m) (Fin m) ℂ))⁻¹ *ᵥ (U *ᵥ good)
      groverSecularScalar m U good β = 0 ∧
        (star good ⬝ᵥ y) = 1/2 ∧ (U * Uf) *ᵥ y = z • y ∧ y ≠ 0 := by
  classical
  let lo := ε * α / Real.sqrt (2 * Real.pi)
  let hi := (13/5 : ℝ)*α
  obtain ⟨B, μ, w, s, hB, hB', hμ, he, hw, _, hmass, hsums, hwfix, hsfix, hweights⟩ :=
    jw_unitary_gap_weights m ε α hε U start good hu hstart hsn hgn hoverlap hphase
  let eig := fun j => if μ j = 1 then (-1 : ℝ) else (μ j).re
  have heig := jw_unitary_basis_real_gap m ε hε U B start μ hu hB hstart he hphase
  have hsign := grover_weighted_endpoint_signs ε α hε hε1 hα hsmall w eig hw hmass heig
  have he2 : ε^2 ≤ ε := by nlinarith
  have ha1 : α ≤ 1/200 := by nlinarith
  have hsqrt : 1 ≤ Real.sqrt (2*Real.pi) := by
    have hs := Real.sq_sqrt (by positivity : 0 ≤ 2*Real.pi)
    have hn := Real.sqrt_nonneg (2*Real.pi)
    nlinarith [Real.pi_gt_three]
  have hlop : 0 < lo := by dsimp only [lo]; positivity
  have hloa : lo ≤ ε*α := by
    dsimp only [lo]
    exact div_le_self (by positivity) hsqrt
  have hhi : hi ≤ ε/2 := by dsimp only [hi]; nlinarith
  have hhip : 0 < hi := by dsimp only [hi]; positivity
  have hab : lo ≤ hi := by dsimp only [hi]; nlinarith [mul_nonneg hα.le (sub_nonneg.mpr hε1)]
  have hloeps : lo < ε := hloa.trans_lt (by nlinarith)
  have hhieps : hi < ε := hhi.trans_lt (by linarith)
  have hsinlo : 0 ≤ Real.sin lo := Real.sin_nonneg_of_nonneg_of_le_pi hlop.le
    (by linarith [Real.pi_gt_three])
  have hsinhi : 0 ≤ Real.sin hi := Real.sin_nonneg_of_nonneg_of_le_pi hhip.le
    (by linarith [Real.pi_gt_three])
  have hslo := grover_secular_gap_weights m U B μ good α lo w s hu hU hg hB' hμ he
    hwfix hsfix hsums hweights (grover_resolvent_isUnit m ε lo hε hε1 hlop hloeps U start hu hstart hphase)
  have hshi := grover_secular_gap_weights m U B μ good α hi w s hu hU hg hB' hμ he
    hwfix hsfix hsums hweights (grover_resolvent_isUnit m ε hi hε hε1 hhip hhieps U start hu hstart hphase)
  have hscalarlo : 0 ≤ groverSecularScalar m U good lo := by
    rw [hslo]
    exact mul_nonneg (div_nonneg hsinlo (by norm_num)) hsign.2
  have hscalarhi : groverSecularScalar m U good hi ≤ 0 := by
    rw [hshi]
    exact mul_nonpos_of_nonneg_of_nonpos (div_nonneg hsinhi (by norm_num)) hsign.1
  exact grover_secular_root_of_signs m ε lo hi hε hε1 hlop hab hhieps Uf U start good
    hu hstart hgn hgood hfix hphase hscalarlo hscalarhi

/-- The reflection about an entrywise real unit vector has entrywise real matrix coefficients. -/
theorem groverReflection_real (m : ℕ) (Uf : Matrix (Fin m) (Fin m) ℂ)
    (good : Fin m → ℂ) (hn : (∑ i, ‖good i‖^2) = 1)
    (hg : ∀ i, (good i).im = 0) (hgood : Uf *ᵥ good = -good)
    (hfix : ∀ v : Fin m → ℂ, (∑ i, star (v i)*good i) = 0 → Uf *ᵥ v = v) :
    ∀ i j, (Uf i j).im = 0 := by
  classical
  intro i j
  have h := congrFun (groverReflection_action Uf good hn hgood hfix (Pi.single j 1)) i
  simp [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite] at h
  rw [h]
  by_cases hij : i = j <;> simp [hij, Complex.sub_im, Complex.mul_im, hg]

/-- For an entrywise real matrix and target, conjugating the resolvent vector conjugates its
parameter. -/
theorem grover_conjugate_resolvent_vector (m : ℕ)
    (U : Matrix (Fin m) (Fin m) ℂ) (good : Fin m → ℂ) (z : ℂ)
    (hU : ∀ i j, (U i j).im = 0) (hg : ∀ i, (good i).im = 0) :
    star ((U-z • (1 : Matrix (Fin m) (Fin m) ℂ))⁻¹ *ᵥ (U *ᵥ good)) =
      (U-star z • (1 : Matrix (Fin m) (Fin m) ℂ))⁻¹ *ᵥ (U *ᵥ good) := by
  have hUr : U.map star = U := by
    ext i j
    exact Complex.conj_eq_iff_im.mpr (hU i j)
  have hgr : star good = good := by
    funext i
    exact Complex.conj_eq_iff_im.mpr (hg i)
  have hmap : (U-z • (1 : Matrix (Fin m) (Fin m) ℂ)).map star =
      U-star z • (1 : Matrix (Fin m) (Fin m) ℂ) := by
    ext i j
    change star (U i j-z*(if i=j then 1 else 0)) = U i j-star z*(if i=j then 1 else 0)
    have hc : ∀ i j, star (U i j) = U i j := fun i j => Complex.conj_eq_iff_im.mpr (hU i j)
    by_cases hij : i=j <;> simp [hij,hc]
  have hconj (A : Matrix (Fin m) (Fin m) ℂ) (v : Fin m → ℂ) :
      star (A *ᵥ v) = A.map star *ᵥ star v := by
    funext i
    simp [Matrix.mulVec,dotProduct,star_sum,star_mul,mul_comm]
  rw [hconj,grover_conjugate_inverse,hmap,hconj,hUr,hgr]

/-- The imaginary part of the resolvent vector equals `sin β` times the symmetric resolvent
inverse applied to `good`. -/
theorem grover_resolvent_imaginary_vector (m : ℕ)
    (U : Matrix (Fin m) (Fin m) ℂ) (good : Fin m → ℂ) (β : ℝ)
    (hu : star U * U = 1) (hU : ∀ i j, (U i j).im = 0)
    (hg : ∀ i, (good i).im = 0)
    (hinv : IsUnit (U - Complex.exp (Complex.I * β) • 1)) :
    let y := (U - Complex.exp (Complex.I * β) • 1)⁻¹ *ᵥ (U *ᵥ good)
    let K := U + star U - ((2 * Real.cos β : ℝ) : ℂ) • 1
    (fun i => ((y i).im : ℂ)) = (Real.sin β : ℂ) • (K⁻¹ *ᵥ good) := by
  let z := Complex.exp (Complex.I * β)
  have hw := grover_real_resolvent_isUnit_conjugate m U z hU hinv
  have hzw : star z*z=1 := by
    rw [Complex.star_def,← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq]
    simp only [z,Complex.norm_exp_I_mul_ofReal,one_pow,Complex.ofReal_one]
  have hzre : z.re = Real.cos β := by dsimp only [z]; rw [mul_comm,Complex.exp_ofReal_mul_I_re]
  have hzim : z.im = Real.sin β := by dsimp only [z]; rw [mul_comm,Complex.exp_ofReal_mul_I_im]
  have hsum : z+star z = ((2*Real.cos β : ℝ) : ℂ) := by
    apply Complex.ext <;> simp only [Complex.add_re,Complex.add_im,Complex.star_def,
      Complex.conj_re,Complex.conj_im,Complex.ofReal_re,Complex.ofReal_im,hzre] <;> ring
  obtain ⟨_, he⟩ := grover_paired_resolvent m U z (star z) hu hzw hinv hw
  rw [hsum] at he
  have hv := congrArg (fun A => A *ᵥ good) he

  rw [Matrix.sub_mulVec,← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,
    Matrix.smul_mulVec,← grover_conjugate_resolvent_vector m U good z hU hg] at hv
  funext i
  have hi := congrFun hv i
  simp only [Pi.sub_apply,Pi.star_apply,Pi.smul_apply,smul_eq_mul] at hi
  rw [Complex.im_eq_sub_conj,← Complex.star_def,hi]
  have hzsub : z-star z = (Real.sin β : ℂ)*(2*Complex.I) := by
    rw [Complex.star_def,Complex.sub_conj,hzim,Complex.ofReal_mul,Complex.ofReal_ofNat]
    ring
  rw [hzsub]
  change _ = (Real.sin β : ℂ)*_
  field_simp

/-- The product of the given real unitary walk and target reflection is unitary and entrywise
real. -/
theorem grover_search_real_unitary (m : ℕ) (Uf U : Matrix (Fin m) (Fin m) ℂ)
    (good : Fin m → ℂ) (huf : star Uf * Uf = 1) (hu : star U * U = 1)
    (hU : ∀ i j, (U i j).im = 0) (hn : (∑ i, ‖good i‖^2) = 1)
    (hg : ∀ i, (good i).im = 0) (hgood : Uf *ᵥ good = -good)
    (hfix : ∀ v : Fin m → ℂ, (∑ i, star (v i)*good i) = 0 → Uf *ᵥ v = v) :
    star (U*Uf)*(U*Uf)=1 ∧ ∀ i j, ((U*Uf) i j).im=0 := by
  constructor
  · rw [star_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (star U), hu,
      Matrix.one_mul, huf]
  · have hf := groverReflection_real m Uf good hn hg hgood hfix
    intro i j
    simp only [Matrix.mul_apply,Complex.im_sum,Complex.mul_im,hU,hf,mul_zero,zero_mul,
      add_zero,Finset.sum_const_zero]

/-- The squared Euclidean norm of the imaginary resolvent vector is a weighted sum of squared
inverse spectral denominators. -/
theorem grover_resolvent_imaginary_norm_sq (m : ℕ)
    (U B : Matrix (Fin m) (Fin m) ℂ) (μ : Fin m → ℂ)
    (good : Fin m → ℂ) (α β : ℝ) (w s : Fin m → ℝ)
    (hu : star U * U = 1) (hU : ∀ i j, (U i j).im = 0)
    (hg : ∀ i, (good i).im = 0) (hB : star B * B = 1) (hB' : B * star B = 1)
    (hμ : ∀ j, ‖μ j‖ = 1)
    (he : ∀ j, U *ᵥ (fun i => B i j) = μ j • (fun i => B i j))
    (hw : ∀ j, μ j = 1 → w j = 0) (hs : ∀ j, μ j ≠ 1 → s j = 0)
    (hsum : (∑ j, s j) = 1)
    (hweights : ∀ j, ‖(star B *ᵥ good) j‖^2 = w j + α^2 * s j)
    (hinv : IsUnit (U - Complex.exp (Complex.I * β) • 1)) :
    let y := (U - Complex.exp (Complex.I * β) • 1)⁻¹ *ᵥ (U *ᵥ good)
    (∑ i, ‖((y i).im : ℂ)‖^2) = Real.sin β ^ 2 / 4 *
      (α^2 / (1 - Real.cos β)^2 + ∑ j,
        w j / (Real.cos β - if μ j = 1 then -1 else (μ j).re)^2) := by
  let K := U + star U - ((2 * Real.cos β : ℝ) : ℂ) • 1
  obtain ⟨hK, _⟩ := grover_secular_symmetric_resolvent m U good β hu hU hg hinv
  have heK (j : Fin m) : K *ᵥ (fun i => B i j) =
      ((2 * ((μ j).re - Real.cos β) : ℝ) : ℂ) • (fun i => B i j) := by
    have hnorm : star (μ j) * μ j = 1 := by
      rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
      simp only [hμ, one_pow, Complex.ofReal_one]
    exact grover_symmetric_eigenvector m U (fun i => B i j) (μ j) (Real.cos β) hu hnorm (he j)
  have hnorm := jw_eigenbasis_inverse_norm_sq m K B
    (fun j => ((2 * ((μ j).re - Real.cos β) : ℝ) : ℂ)) hB hB' hK heK good
  have him := grover_resolvent_imaginary_vector m U good β hu hU hg hinv
  dsimp only at him
  (try dsimp only)
  simp_rw [show ∀ i, ‖((((U - Complex.exp (Complex.I * β) • 1)⁻¹ *ᵥ (U *ᵥ good)) i).im : ℂ)‖^2 =
      Real.sin β^2 * ‖(K⁻¹ *ᵥ good) i‖^2 from fun i => by
        have hi := congrFun him i
        rw [hi]
        simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, Complex.norm_real,
          Real.norm_eq_abs, sq_abs]
        rfl]
  rw [← Finset.mul_sum, hnorm]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow, hweights]
  have ht (j : Fin m) : (w j+α^2*s j)/(2^2*((μ j).re-Real.cos β)^2) =
      ((w j+α^2*s j)/((μ j).re-Real.cos β)^2)/4 := by
    rw [show (2:ℝ)^2=4 by norm_num, mul_comm 4, div_mul_eq_div_div]
  simp_rw [ht]
  rw [← Finset.sum_div, grover_weighted_pole_split_sq m μ w s α (Real.cos β) hw hs hsum]
  ring

/-- The overlap of the fixed vector `start` with the resolvent vector is `α / (1 - z)`. -/
theorem grover_resolvent_start_overlap (m : ℕ) (α : ℝ)
    (U : Matrix (Fin m) (Fin m) ℂ) (start good : Fin m → ℂ) (z : ℂ)
    (hu : star U*U=1) (hstart : U *ᵥ start=start)
    (hoverlap : (∑ i, star (good i)*start i)=(α:ℂ))
    (hz : z≠1) (hinv : IsUnit (U-z • (1 : Matrix (Fin m) (Fin m) ℂ))) :
    star start ⬝ᵥ ((U-z • 1)⁻¹ *ᵥ (U *ᵥ good)) = (α:ℂ)/(1-z) := by
  let A := U-z • (1 : Matrix (Fin m) (Fin m) ℂ)
  let y := A⁻¹ *ᵥ (U *ᵥ good)
  have hadj : star U *ᵥ start=start := by
    calc
      _ = star U *ᵥ (U *ᵥ start) := by rw [hstart]
      _ = start := by rw [Matrix.mulVec_mulVec,hu,Matrix.one_mulVec]
  have hrow : star start ᵥ* U=star start := by
    simpa only [Matrix.star_mulVec,Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose] using! congrArg star hadj
  have hsg : star start ⬝ᵥ good=(α:ℂ) := by
    have h := congrArg star hoverlap
    simpa [dotProduct,star_sum,star_mul,mul_comm] using! h
  have hAy : U *ᵥ y-z • y=U *ᵥ good := by
    have h : A *ᵥ y=U *ᵥ good := by
      dsimp only [y]
      rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _
        ((Matrix.isUnit_iff_isUnit_det _).mp hinv),Matrix.one_mulVec]
    simpa only [A,Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec] using! h
  have h := congrArg (fun v => star start ⬝ᵥ v) hAy

  have hfun (v : Fin m → ℂ) : star start ⬝ᵥ (U *ᵥ v) = star start ⬝ᵥ v := by
    rw [Matrix.dotProduct_mulVec,hrow]
  rw [dotProduct_sub,hfun y,hfun good,dotProduct_smul,smul_eq_mul,hsg] at h
  apply (eq_div_iff (sub_ne_zero.mpr hz.symm)).mpr
  linear_combination h

/-- The imaginary part of `α / (1 - exp (I * β))` equals `α * sin β / (2 * (1 - cos β))`. -/
theorem grover_fixed_resolvent_im (α β : ℝ) :
    (((α : ℂ) / (1 - Complex.exp (Complex.I * β))).im) =
      α * Real.sin β / (2 * (1 - Real.cos β)) := by
  have h := grover_fixed_pole_im 1 β
  norm_num only [Complex.ofReal_one,one_pow] at h
  rw [show (α : ℂ)/(1-Complex.exp (Complex.I*β)) =
    (α : ℂ)*(1/(1-Complex.exp (Complex.I*β))) by ring]
  rw [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,h]
  ring

/-- Taking the imaginary part commutes with the Hermitian pairing against an entrywise real
vector. -/
theorem grover_real_left_imag_dot (m : ℕ) (start y : Fin m → ℂ)
    (hsr : ∀ i, (start i).im = 0) :
    star start ⬝ᵥ (fun i => ((y i).im : ℂ)) = ((star start ⬝ᵥ y).im : ℂ) := by
  apply Complex.ext <;> simp only [dotProduct,Pi.star_apply,Complex.re_sum,Complex.im_sum,
    Complex.mul_re,Complex.mul_im,Complex.star_def,Complex.conj_re,Complex.conj_im,
    Complex.ofReal_re,Complex.ofReal_im,hsr,neg_zero,mul_zero,zero_mul,sub_zero,add_zero,
    Finset.sum_const_zero]

/-- The overlap of `start` with the imaginary resolvent vector equals `α * sin β / (2 * (1 - cos
β))`. -/
theorem grover_resolvent_imaginary_start_overlap (m : ℕ) (α β : ℝ)
    (U : Matrix (Fin m) (Fin m) ℂ) (start good : Fin m → ℂ)
    (hu : star U*U=1) (hstart : U *ᵥ start=start) (hsr : ∀ i, (start i).im=0)
    (hoverlap : (∑ i, star (good i)*start i)=(α:ℂ))
    (hz : Complex.exp (Complex.I*β)≠1)
    (hinv : IsUnit (U-Complex.exp (Complex.I*β) • (1 : Matrix (Fin m) (Fin m) ℂ))) :
    let y := (U-Complex.exp (Complex.I*β) • 1)⁻¹ *ᵥ (U *ᵥ good)
    star start ⬝ᵥ (fun i => ((y i).im : ℂ)) =
      ((α*Real.sin β/(2*(1-Real.cos β)) : ℝ) : ℂ) := by
  (try dsimp only)
  rw [grover_real_left_imag_dot m start _ hsr,
    grover_resolvent_start_overlap m α U start good _ hu hstart hoverlap hz hinv,
    grover_fixed_resolvent_im]

/-- Subtracting the real projection onto a unit vector reduces the squared Euclidean norm by the
square of that projection coefficient. -/
theorem grover_norm_sq_projection_residual (m : ℕ) (start v : Fin m → ℂ) (C : ℝ)
    (hsn : (∑ i, ‖start i‖^2)=1) (hproj : star start ⬝ᵥ v = (C:ℂ)) :
    (∑ i, ‖(v-(C:ℂ) • start) i‖^2) = (∑ i, ‖v i‖^2)-C^2 := by
  have hss : star start ⬝ᵥ start=1 := by
    rw [jw_star_dot_self,hsn,Complex.ofReal_one]
  have hvs : star v ⬝ᵥ start=(C:ℂ) := by
    have h := congrArg star hproj
    simpa [dotProduct,star_sum,star_mul,mul_comm] using! h
  apply Complex.ofReal_injective
  rw [← jw_star_dot_self, Complex.ofReal_sub, Complex.ofReal_pow]
  simp only [star_sub,sub_dotProduct,dotProduct_sub,star_smul,smul_dotProduct,
    dotProduct_smul,Complex.star_def,Complex.conj_ofReal,smul_eq_mul,hss,hproj,hvs]
  rw [jw_star_dot_self]
  ring

set_option maxHeartbeats 800000 in

/-- At a small-overlap secular root, the start projection coefficient is positive, the imaginary
vector has squared norm at most `36 / ε^2`, and its projection residual satisfies the stated
bound. -/
theorem grover_small_overlap_normalization_bounds (m : ℕ) (ε α β : ℝ)
    (hε : 0<ε) (hε1 : ε≤1) (hα : 0<α) (hsmall : α≤ε^2/200)
    (hβbounds : β ∈ Set.Icc (ε*α/Real.sqrt (2*Real.pi)) ((13/5:ℝ)*α))
    (U : Matrix (Fin m) (Fin m) ℂ) (start good : Fin m → ℂ)
    (hu : star U*U=1) (hU : ∀i j,(U i j).im=0)
    (hsr : ∀i,(start i).im=0) (hgr : ∀i,(good i).im=0)
    (hsn : (∑i,‖start i‖^2)=1) (hgn : (∑i,‖good i‖^2)=1)
    (hoverlap : (∑i,star (good i)*start i)=(α:ℂ)) (hstart : U *ᵥ start=start)
    (hphase : ∀ (ν : ℂ) (v : Fin m → ℂ), U *ᵥ v=ν • v →
      (∑i,star (v i)*start i)=0 → v≠0 →
      ∃θ : ℝ, ε≤θ ∧ θ≤2*Real.pi-ε ∧ θ≠Real.pi ∧ ν=Complex.exp (Complex.I*θ))
    (hroot : groverSecularScalar m U good β=0) :
    let y := (U-Complex.exp (Complex.I*β) • 1)⁻¹ *ᵥ (U *ᵥ good)
    let C := α*Real.sin β/(2*(1-Real.cos β))
    0<C ∧ (∑i,‖((y i).im:ℂ)‖^2)≤36/ε^2 ∧
      (∑i,‖((y i).im:ℂ)-(C:ℂ)*start i‖^2)≤(2*β/ε*C)^2 := by
  classical
  let y := (U-Complex.exp (Complex.I*β) • (1 : Matrix (Fin m) (Fin m) ℂ))⁻¹ *ᵥ (U *ᵥ good)
  let C := α*Real.sin β/(2*(1-Real.cos β))
  let d := 1-Real.cos β
  have hεsq : 0<ε^2 := sq_pos_of_pos hε
  have he2 : ε^2≤ε := by nlinarith
  have hβp : 0<β := lt_of_lt_of_le (by positivity) hβbounds.1
  have hβhalf : β≤ε/2 := by nlinarith [hβbounds.2]
  have hβtenth : β≤ε/10 := by nlinarith [hβbounds.2]
  have hβ1 : β≤1 := by linarith
  have hβeps : β<ε := by linarith
  have hspos : 0<Real.sin β := Real.sin_pos_of_pos_of_lt_pi hβp (by linarith [Real.pi_gt_three])
  have hds := grover_one_sub_cos_bounds β hβp.le hβ1
  have hdp : 0<d := by dsimp only [d]; nlinarith [sq_pos_of_pos hβp]
  have hCp : 0<C := by dsimp only [C]; positivity
  have hinv := grover_resolvent_isUnit m ε β hε hε1 hβp hβeps U start hu hstart hphase
  obtain ⟨B,μ,w,s,hB,hB',hμ,he,hw,_,hmass,hsums,hwfix,hsfix,hweights⟩ :=
    jw_unitary_gap_weights m ε α hε U start good hu hstart hsn hgn hoverlap hphase
  let eig := fun j => if μ j=1 then (-1:ℝ) else (μ j).re
  have heig := jw_unitary_basis_real_gap m ε hε U B start μ hu hB hstart he hphase
  have hscalar := grover_secular_gap_weights m U B μ good α β w s hu hU hgr hB' hμ he
    hwfix hsfix hsums hweights hinv
  rw [hroot] at hscalar
  have hfirst : (∑j,w j/(Real.cos β-eig j))=α^2/d := by
    have hz :=
        (mul_eq_zero.mp hscalar.symm).resolve_left (ne_of_gt (by positivity : 0<Real.sin β/2))
    exact (sub_eq_zero.mp hz).symm
  have hsecond := grover_weighted_inverse_square_bound ε β hε hε1 hβp.le hβhalf w eig hw heig
  rw [hfirst] at hsecond
  have hn := grover_resolvent_imaginary_norm_sq m U B μ good α β w s hu hU hgr hB hB' hμ he
    hwfix hsfix hsums hweights hinv
  change (∑i,‖((y i).im:ℂ)‖^2)=Real.sin β^2/4*(α^2/d^2+∑j,w j/(Real.cos β-eig j)^2) at hn
  have hN : (∑i,‖((y i).im:ℂ)‖^2)≤C^2*(1+3*β^2/ε^2) := by
    calc
      _ ≤ Real.sin β^2/4*(α^2/d^2+(6/ε^2)*(α^2/d)) := by
        rw [hn]
        exact mul_le_mul_of_nonneg_left (add_le_add_right hsecond _) (by positivity)
      _ = C^2*(1+6*d/ε^2) := by
        dsimp only [C,d]
        field_simp
        ring
      _ ≤ C^2*(1+3*β^2/ε^2) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg C)
        apply add_le_add_right
        exact div_le_div_of_nonneg_right (by dsimp only [d]; nlinarith [hds.2]) hεsq.le
  have hClow : C≤3*α/(2*β) := by
    have hsin := Real.sin_le hβp.le
    calc
      C ≤ α*β/(2*d) := by
        dsimp only [C]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsin hα.le) (by positivity)
      _ ≤ α*β/(2*(β^2/3)) := div_le_div_of_nonneg_left (by positivity) (by positivity)
        (by dsimp only [d]; nlinarith [hds.1])
      _ = _ := by field_simp
  have hsqrtp : 0<Real.sqrt (2*Real.pi) := by positivity
  have hsqrt3 : Real.sqrt (2*Real.pi)≤3 := by
    have hs := Real.sq_sqrt (by positivity : 0≤2*Real.pi)
    nlinarith [Real.sqrt_nonneg (2*Real.pi),Real.pi_lt_four]
  have hbproduct : ε*α≤3*β := by
    have h := (div_le_iff₀ hsqrtp).mp hβbounds.1
    nlinarith [mul_nonneg hβp.le (sub_nonneg.mpr hsqrt3)]
  have hCupper : C≤5/ε := hClow.trans (by
    apply (div_le_div_iff₀ (by positivity : 0<2*β) hε).mpr
    nlinarith only [hbproduct, hβp])
  have hC2 : C^2≤25/ε^2 := by
    have h := mul_self_le_mul_self hCp.le hCupper
    convert! h using 1 <;> ring
  have hratio : 1+3*β^2/ε^2≤36/25 := by
    have hsq : β^2≤ε^2/100 := by nlinarith
    have h := (div_le_iff₀ hεsq).mpr (show 3*β^2≤(11/25:ℝ)*ε^2 by nlinarith)
    linarith
  refine ⟨hCp,?_,?_⟩
  · calc
      _ ≤ C^2*(1+3*β^2/ε^2) := hN
      _ ≤ (25/ε^2)*(36/25) := mul_le_mul hC2 hratio (by positivity) (by positivity)
      _ = _ := by ring
  · have hz : Complex.exp (Complex.I*β)≠1 := by
      exact jw_phase_ne_one β hβp (by linarith [Real.pi_gt_three])
    have hproj :=
        grover_resolvent_imaginary_start_overlap m α β U start good hu hstart hsr hoverlap hz hinv
    have hr := grover_norm_sq_projection_residual m start (fun i => ((y i).im:ℂ)) C hsn hproj
    change (∑i,‖((y i).im:ℂ)-(C:ℂ)*start i‖^2)=(∑i,‖((y i).im:ℂ)‖^2)-C^2 at hr
    rw [hr]
    calc
      _ ≤ C^2*(3*β^2/ε^2) := by nlinarith only [hN]
      _ ≤ (2*β/ε*C)^2 := by
        have heq : (2*β/ε*C)^2=C^2*(4*β^2/ε^2) := by ring
        rw [heq]
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg C)
        apply div_le_div_of_nonneg_right _ hεsq.le
        nlinarith [sq_nonneg β]

/-- Taking the real part commutes with the Hermitian pairing against an entrywise real vector. -/
theorem grover_real_left_real_dot (m : ℕ) (good y : Fin m → ℂ)
    (hg : ∀i,(good i).im=0) :
    star good ⬝ᵥ (fun i => ((y i).re:ℂ)) = ((star good ⬝ᵥ y).re:ℂ) := by
  apply Complex.ext <;> simp only [dotProduct,Pi.star_apply,Complex.re_sum,Complex.im_sum,
    Complex.mul_re,Complex.mul_im,Complex.star_def,Complex.conj_re,Complex.conj_im,
    Complex.ofReal_re,Complex.ofReal_im,hg,neg_zero,mul_zero,zero_mul,sub_zero,add_zero,
    Finset.sum_const_zero]

set_option maxHeartbeats 1000000 in

/-- A real unitary walk satisfying the stated phase gap and reflection hypotheses achieves
overlap at least `ε^3 / 1000` within `8 / (ε * α)` iterations. -/
theorem groverInterpolation : GroverInterpolation := by
  intro m ε α hε hε1 hα _ Uf U start good huf hu hU hsr hgr hsn hgn hoverlap hgood hfix hstart hphase
  by_cases hlarge : ε^2/200≤α
  · exact groverInterpolation_large_overlap m ε α hε hε1 hα hlarge Uf U start good hoverlap
  have hsmall : α≤ε^2/200 := le_of_lt (lt_of_not_ge hlarge)
  obtain ⟨β,hβ,hroot,hyg,hy,_⟩ := grover_small_overlap_root m ε α hε hε1 hα hsmall Uf U start good
    hu hU hgr hsn hgn hoverlap hstart hgood hfix hphase
  let W := U*Uf
  let y := (U-Complex.exp (Complex.I*β) • (1 : Matrix (Fin m) (Fin m) ℂ))⁻¹ *ᵥ (U *ᵥ good)
  let v : EuclideanSpace ℂ (Fin m) := WithLp.toLp 2 (fun i => ((y i).im:ℂ))
  let u : EuclideanSpace ℂ (Fin m) := WithLp.toLp 2 (fun i => ((y i).re:ℂ))
  let S : EuclideanSpace ℂ (Fin m) := WithLp.toLp 2 start
  let G : EuclideanSpace ℂ (Fin m) := WithLp.toLp 2 good
  let σ := ‖v‖
  let C := α*Real.sin β/(2*(1-Real.cos β))
  have hβp : 0<β := lt_of_lt_of_le (by positivity) hβ.1
  have he2 : ε^2≤ε := by nlinarith
  have hβeps : β<ε := by nlinarith [hβ.2]
  have hβπ : β<Real.pi := by linarith [Real.pi_gt_three]
  have hinv := grover_resolvent_isUnit m ε β hε hε1 hβp hβeps U start hu hstart hphase
  have hz : Complex.exp (Complex.I*β)≠1 := jw_phase_ne_one β hβp (by linarith [Real.pi_gt_three])
  have hproj :=
      grover_resolvent_imaginary_start_overlap m α β U start good hu hstart hsr hoverlap hz hinv
  change star start ⬝ᵥ (fun i => ((y i).im:ℂ))=(C:ℂ) at hproj
  obtain ⟨hCp,hvbound,hrbound⟩ := grover_small_overlap_normalization_bounds m ε α β hε hε1 hα hsmall hβ
    U start good hu hU hsr hgr hsn hgn hoverlap hstart hphase hroot
  change 0<C at hCp
  have hvnz : v≠0 := by
    intro hzero
    have hzraw := congrArg WithLp.ofLp hzero
    change (fun i => ((y i).im:ℂ))=0 at hzraw
    rw [hzraw,dotProduct_zero] at hproj
    exact (Complex.ofReal_ne_zero.mpr hCp.ne') hproj.symm
  have hσp : 0<σ := norm_pos_iff.mpr hvnz
  have hSnorm : ‖S‖=1 := by
    have h := EuclideanSpace.norm_sq_eq S
    change ‖S‖^2=(∑i,‖start i‖^2) at h
    rw [hsn] at h
    nlinarith only [h,norm_nonneg S]
  have hGnorm : ‖G‖=1 := by
    have h := EuclideanSpace.norm_sq_eq G
    change ‖G‖^2=(∑i,‖good i‖^2) at h
    rw [hgn] at h
    nlinarith only [h,norm_nonneg G]
  have hσbound : σ≤6/ε := by
    have hn := EuclideanSpace.norm_sq_eq v
    change σ^2=(∑i,‖((y i).im:ℂ)‖^2) at hn
    change (∑i,‖((y i).im:ℂ)‖^2)≤36/ε^2 at hvbound
    have hsq : σ^2≤(6/ε)^2 := by
      rw [hn]
      convert! hvbound using 1
      ring
    exact (sq_le_sq₀ hσp.le (by positivity)).mp hsq
  have hclose : ‖v-C • S‖≤(2*β/ε)*C := by
    have hn := EuclideanSpace.norm_sq_eq (v-C • S)
    change ‖v-C • S‖^2=(∑i,‖((y i).im:ℂ)-(C:ℂ)*start i‖^2) at hn
    change (∑i,‖((y i).im:ℂ)-(C:ℂ)*start i‖^2)≤(2*β/ε*C)^2 at hrbound
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0≤(2*β/ε)*C)).mp
    rw [hn]
    exact hrbound
  have hnear := grover_normalize_near_unit S v C (2*β/ε) hSnorm hCp hvnz hclose
  have hnormalize : NormedSpace.normalize v=(σ⁻¹:ℂ) • v := by
    rw [NormedSpace.normalize,RCLike.real_smul_eq_coe_smul (K:=ℂ),RCLike.ofReal_inv]
    rfl
  change ‖S-NormedSpace.normalize v‖≤2*(2*β/ε) at hnear
  rw [hnormalize] at hnear
  have hnear' : ‖S-(σ⁻¹:ℂ) • v‖≤4*β/ε := by
    convert! hnear using 1
    ring
  obtain ⟨hWu,hWr⟩ := grover_search_real_unitary m Uf U good huf hu hU hgn hgr hgood hfix
  change star W*W=1 at hWu
  change ∀i j,(W i j).im=0 at hWr
  change W *ᵥ y=Complex.exp (Complex.I*β) • y at hy
  let t := Nat.floor (Real.pi/(2*β))
  obtain ⟨ht,hθ0,hθβ⟩ := grover_interpolation_iteration ε α β hε hα hβ.1
  have hrot :=
      jw_real_unitary_normalized_quarter_iteration m β hβp hβπ W y hWu hWr hy t ⟨hθ0,hθβ.le⟩ hσp
  let L := (W^t).toEuclideanLin
  have hWt : star (W^t)*(W^t)=1 := Matrix.mem_unitaryGroup_iff'.mp
    ((Matrix.unitaryGroup (Fin m) ℂ).pow_mem (Matrix.mem_unitaryGroup_iff'.mpr hWu) t)
  have hLnorm (x : EuclideanSpace ℂ (Fin m)) : ‖L x‖=‖x‖ :=
    grover_unitary_euclidean_norm m (W^t) hWt x
  have hrot' : ‖L ((σ⁻¹:ℂ) • v)-(σ⁻¹:ℂ) • u‖≤β := by
    change ‖(WithLp.toLp 2 (W^t *ᵥ ((σ⁻¹:ℂ) • (fun i => ((y i).im:ℂ))) -
      (σ⁻¹:ℂ) • (fun i => ((y i).re:ℂ))) : EuclideanSpace ℂ (Fin m))‖≤β
    exact hrot
  have hgu : inner ℂ G ((σ⁻¹:ℂ) • u)=(σ⁻¹:ℂ)*(1/2) := by
    rw [inner_smul_right]
    change (σ⁻¹:ℂ)*inner ℂ (WithLp.toLp 2 good) (WithLp.toLp 2 (fun i => ((y i).re:ℂ))) = _
    rw [EuclideanSpace.inner_toLp_toLp,dotProduct_comm,grover_real_left_real_dot m good y hgr]
    change star good ⬝ᵥ y=(1/2:ℂ) at hyg
    rw [hyg]
    norm_num
  have hgumod : ‖inner ℂ G ((σ⁻¹:ℂ) • u)‖=1/(2*σ) := by
    rw [hgu,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hσp]
    norm_num
  have hgulow : ε/12≤‖inner ℂ G ((σ⁻¹:ℂ) • u)‖ := by
    rw [hgumod]
    apply (div_le_div_iff₀ (by norm_num : 0<(12:ℝ)) (by positivity : 0<2*σ)).mpr
    have h := (le_div_iff₀ hε).mp hσbound
    nlinarith only [h]
  have hamp := grover_amplitude_of_near_rotation L hLnorm S ((σ⁻¹:ℂ) • v) ((σ⁻¹:ℂ) • u) G
    (4*β/ε) β hGnorm.le hnear' hrot'
  have hmargin := grover_small_overlap_amplitude_margin ε α β hε hε1 hsmall hβ.2
  refine ⟨t,ht,?_⟩
  have htarget : ε^3/1000≤‖inner ℂ G (L S)‖ := by linarith only [hmargin,hgulow,hamp]
  change ε^3/1000≤‖star good ⬝ᵥ ((W^t) *ᵥ start)‖
  change ε^3/1000≤‖((W^t) *ᵥ start) ⬝ᵥ star good‖ at htarget
  simpa only [dotProduct_comm] using! htarget

/-- The Grover interpolation statement follows from `groverInterpolation`
[Ambainis2007ElementDistinctness]. -/
theorem groverInterpolation_answer : GroverInterpolation := groverInterpolation

end Qatlib.Concepts.WalkFind.GroverInterp
