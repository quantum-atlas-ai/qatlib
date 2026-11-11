/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.GroverInterp.GroverIncludingMinusOneStat
import Qatlib.Concepts.WalkFind.GroverInterp.GroverInterpolationQuan

/-!
# Grover interpolation allowing eigenvalue minus one

This module proves the Grover interpolation contract while allowing the background unitary to
have eigenvalue minus one. The proof obtains a spectral weight decomposition, a zero of the
secular scalar in the phase gap, and quantitative normalization estimates for its resolvent
vector.

The results culminate in `minusOne_groverInterpolation` and its exported form
`groverIncludingMinusOne_answer`, supplying the version of the quantum-walk interpolation
statement that includes this spectral endpoint.

For background, see [Ambainis2007ElementDistinctness].

## Main statements

* `minusOne_grover_small_overlap_root`: a secular root and a nonzero eigenvector in the stated
  phase interval.
* `minusOne_grover_small_overlap_normalization_bounds`: quantitative bounds for the imaginary
  part of the resolvent vector.
* `groverIncludingMinusOne_answer`: the interpolation contract including eigenvalue minus one.

## References

* [Ambainis, 2007][Ambainis2007ElementDistinctness]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Qatlib.Concepts.WalkFind.GroverInterp
open Matrix
open scoped InnerProductSpace

/-- Under the stated positive phase gap on nonzero eigenvectors orthogonal to the normalized
fixed start vector, every fixed vector is its scalar multiple given by the start overlap. -/
theorem minusOne_jw_fixed_vector_start_line (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (U : Matrix (Fin m) (Fin m) ℂ) (start v : Fin m → ℂ)
    (hstart : U *ᵥ start = start) (hfixed : U *ᵥ v = v)
    (hsn : (∑ i, ‖start i‖ ^ 2) = 1)
    (hphase : ∀ (ν : ℂ) (w : Fin m → ℂ), U *ᵥ w = ν • w →
      (∑ i, star (w i) * start i) = 0 → w ≠ 0 →
      ∃ θ : ℝ, ε ≤ θ ∧ θ ≤ 2 * Real.pi - ε ∧ ν = Complex.exp (Complex.I * θ)) :
    v = (star start ⬝ᵥ v) • start := by
  let c := star start ⬝ᵥ v
  let w := v - c • start
  have hsn' : star start ⬝ᵥ start = 1 := by rw [jw_star_dot_self, hsn]; rfl
  have hwfix : U *ᵥ w = (1 : ℂ) • w := by
    simp only [w, Matrix.mulVec_sub, Matrix.mulVec_smul, hfixed, hstart, one_smul]
  have hworth : (∑ i, star (w i) * start i) = 0 := by
    have hc : star v ⬝ᵥ start = star c := by
      simp only [c, dotProduct, Pi.star_apply, star_sum, star_mul, star_star, mul_comm]
    change star w ⬝ᵥ start = 0
    simp only [w, star_sub, sub_dotProduct, star_smul, smul_dotProduct, hc, hsn']
    simp
  have hwzero : w = 0 := by
    by_contra hw
    obtain ⟨θ, hlo, hhi, he⟩ := hphase 1 w hwfix hworth hw
    exact jw_phase_ne_one θ (hε.trans_le hlo) (by linarith only [hhi, hε]) he.symm
  exact sub_eq_zero.mp hwzero

/-- The unitary and phase-gap hypotheses yield a unitary eigenbasis and nonnegative spectral
weights splitting the good-state mass into totals `1 - α^2` and `α^2` on the nonfixed and
fixed eigenspaces. -/
theorem minusOne_jw_unitary_gap_weights (m : ℕ) (ε α : ℝ) (hε : 0 < ε)
    (U : Matrix (Fin m) (Fin m) ℂ) (start good : Fin m → ℂ)
    (hu : star U * U = 1) (hstart : U *ᵥ start = start)
    (hsn : (∑ i, ‖start i‖ ^ 2) = 1) (hgn : (∑ i, ‖good i‖ ^ 2) = 1)
    (hoverlap : star good ⬝ᵥ start = (α : ℂ))
    (hphase : ∀ (ν : ℂ) (v : Fin m → ℂ), U *ᵥ v = ν • v →
      (∑ i, star (v i) * start i) = 0 → v ≠ 0 →
      ∃ θ : ℝ, ε ≤ θ ∧ θ ≤ 2 * Real.pi - ε ∧ ν = Complex.exp (Complex.I * θ)) :
    ∃ (B : Matrix (Fin m) (Fin m) ℂ) (μ : Fin m → ℂ) (w s : Fin m → ℝ),
      star B * B = 1 ∧ B * star B = 1 ∧
      (∀ j, ‖μ j‖ = 1) ∧
      (∀ j, U *ᵥ (fun i => B i j) = μ j • (fun i => B i j)) ∧
      (∀ j, 0 ≤ w j) ∧ (∀ j, 0 ≤ s j) ∧
      (∑ j, w j) = 1 - α ^ 2 ∧ (∑ j, s j) = 1 ∧
      (∀ j, μ j = 1 → w j = 0) ∧ (∀ j, μ j ≠ 1 → s j = 0) ∧
      ∀ j, ‖(star B *ᵥ good) j‖ ^ 2 = w j + α ^ 2 * s j := by
  classical
  obtain ⟨B, μ, hB, hB', hμ, heig⟩ := jw_unitary_orthonormal_eigenbasis m U hu
  let c := star B *ᵥ good
  let d := star B *ᵥ start
  let s := fun j => ‖d j‖ ^ 2
  let w := fun j => if μ j = 1 then 0 else ‖c j‖ ^ 2
  have hsumc : (∑ j, ‖c j‖ ^ 2) = 1 := (jw_unitary_basis_parseval m B hB' good).trans hgn
  have hsums : (∑ j, s j) = 1 := (jw_unitary_basis_parseval m B hB' start).trans hsn
  have hd0 (j : Fin m) (hj : μ j ≠ 1) : d j = 0 := by
    exact jw_eigenvector_start_coefficient_zero m U start (fun i => B i j) (μ j)
      hu hstart (heig j) hj
  have hsg : star start ⬝ᵥ good = (α : ℂ) := by
    have h := congrArg star hoverlap
    simpa [dotProduct, star_sum, star_mul, mul_comm] using! h
  have hcfix (j : Fin m) (hj : μ j = 1) : c j = (α : ℂ) * d j := by
    have hjfix : U *ᵥ (fun i => B i j) = (fun i => B i j) := by
      simpa only [hj, one_smul] using! heig j
    have hline := minusOne_jw_fixed_vector_start_line m ε hε U start (fun i => B i j)
      hstart hjfix hsn hphase
    have hconj : star (star start ⬝ᵥ (fun i => B i j)) = d j := by
      simp only [d, dotProduct, Matrix.mulVec, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_apply, star_sum, star_mul, star_star, Pi.star_apply, mul_comm]
    change star (fun i => B i j) ⬝ᵥ good = (α : ℂ) * d j
    rw [hline, star_smul, smul_dotProduct, smul_eq_mul, hconj, hsg, mul_comm]
  have hweights (j : Fin m) : ‖c j‖ ^ 2 = w j + α ^ 2 * s j := by
    by_cases hj : μ j = 1
    · simp only [w, hj, if_pos, zero_add, s, hcfix j hj, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, mul_pow, sq_abs]
    · simp only [w, if_neg hj, s, hd0 j hj, norm_zero, zero_pow (by decide : 2 ≠ 0),
        mul_zero, add_zero]
  have hsumw : (∑ j, w j) = 1 - α ^ 2 := by
    have hh := hsumc
    simp only [hweights, Finset.sum_add_distrib, ← Finset.mul_sum, hsums, mul_one] at hh
    linarith only [hh]
  refine ⟨B, μ, w, s, hB, hB', hμ, heig, ?_, ?_, hsumw, hsums, ?_, ?_, hweights⟩
  · intro j
    simp only [w]
    split_ifs <;> positivity
  · intro j
    exact sq_nonneg _
  · intro j hj
    simp only [w, hj, if_pos]
  · intro j hj
    simp only [s, hd0 j hj, norm_zero, zero_pow (by decide : 2 ≠ 0)]

/-- Under the unitary and phase-gap assumptions, every eigenvalue different from one with a
nonzero eigenvector has real part between minus one and `cos ε`. -/
theorem minusOne_jw_nonfixed_eigenvalue_real_gap (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (U : Matrix (Fin m) (Fin m) ℂ) (start v : Fin m → ℂ) (μ : ℂ)
    (hu : star U * U = 1) (hstart : U *ᵥ start = start)
    (heigen : U *ᵥ v = μ • v) (hμ : μ ≠ 1) (hv : v ≠ 0)
    (hphase : ∀ (ν : ℂ) (w : Fin m → ℂ), U *ᵥ w = ν • w →
      (∑ i, star (w i) * start i) = 0 → w ≠ 0 →
      ∃ θ : ℝ, ε ≤ θ ∧ θ ≤ 2 * Real.pi - ε ∧ ν = Complex.exp (Complex.I * θ)) :
    -1 ≤ μ.re ∧ μ.re ≤ Real.cos ε := by
  have ho := jw_eigenvector_start_coefficient_zero m U start v μ hu hstart heigen hμ
  obtain ⟨θ, hlo, hhi, he⟩ := hphase μ v heigen ho hv
  have hre : μ.re = Real.cos θ := by simp [he, Complex.exp_re]
  rw [hre]
  refine ⟨Real.neg_one_le_cos θ, ?_⟩
  by_cases hθ : θ ≤ Real.pi
  · exact Real.cos_le_cos_of_nonneg_of_le_pi hε.le hθ hlo
  · calc
      Real.cos θ = Real.cos (2 * Real.pi - θ) := (Real.cos_two_pi_sub θ).symm
      _ ≤ Real.cos ε := Real.cos_le_cos_of_nonneg_of_le_pi hε.le
        (by linarith only [hθ]) (by linarith only [hhi])

/-- In the given unitary eigenbasis, replacing fixed eigenvalues by real value minus one places
every resulting real spectral value in `[-1, cos ε]`. -/
theorem minusOne_jw_unitary_basis_real_gap (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (U B : Matrix (Fin m) (Fin m) ℂ) (start : Fin m → ℂ) (μ : Fin m → ℂ)
    (hu : star U * U = 1) (hB : star B * B = 1) (hstart : U *ᵥ start = start)
    (heigen : ∀ j, U *ᵥ (fun i => B i j) = μ j • (fun i => B i j))
    (hphase : ∀ (ν : ℂ) (v : Fin m → ℂ), U *ᵥ v = ν • v →
      (∑ i, star (v i) * start i) = 0 → v ≠ 0 →
      ∃ θ : ℝ, ε ≤ θ ∧ θ ≤ 2 * Real.pi - ε ∧ ν = Complex.exp (Complex.I * θ)) :
    ∀ j, -1 ≤ (if μ j = 1 then -1 else (μ j).re) ∧
      (if μ j = 1 then -1 else (μ j).re) ≤ Real.cos ε := by
  intro j
  by_cases hj : μ j = 1
  · simp only [if_pos hj]
    exact ⟨le_refl _, Real.neg_one_le_cos ε⟩
  · simp only [if_neg hj]
    exact minusOne_jw_nonfixed_eigenvalue_real_gap m ε hε U start (fun i => B i j) (μ j)
      hu hstart (heigen j) hj (jw_unitary_basis_column_ne_zero m B hB j) hphase

/-- Under the unitary and phase-gap hypotheses with `0 < ε ≤ 1`, the matrix `U - exp (I * β) •
1` is invertible whenever `0 < β < ε`. -/
theorem minusOne_grover_resolvent_isUnit (m : ℕ) (ε β : ℝ) (_hε : 0 < ε) (hε1 : ε ≤ 1)
    (hβ : 0 < β) (hβε : β < ε)
    (U : Matrix (Fin m) (Fin m) ℂ) (start : Fin m → ℂ)
    (hu : star U * U = 1) (hstart : U *ᵥ start = start)
    (hphase : ∀ (ν : ℂ) (v : Fin m → ℂ), U *ᵥ v = ν • v →
      (∑ i, star (v i) * start i) = 0 → v ≠ 0 →
      ∃ θ : ℝ, ε ≤ θ ∧ θ ≤ 2 * Real.pi - ε ∧ ν = Complex.exp (Complex.I * θ)) :
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
    obtain ⟨θ, hlo, hhi, heq⟩ := hphase z w he ho hnw
    exact grover_phase_ne_of_order β θ hβ.le (hβε.trans_le hlo) (by linarith) heq
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y hxy
  have hw : (U - z • (1 : Matrix (Fin m) (Fin m) ℂ)) *ᵥ (x - y) = 0 := by
    rw [Matrix.mulVec_sub, hxy, sub_self]
  exact sub_eq_zero.mp (hker (x - y) hw)

/-- Under the unitary and phase-gap hypotheses with `0 < ε ≤ 1`, the Grover secular scalar is
continuous on `(0, ε)`. -/
theorem minusOne_grover_secular_continuousOn (m : ℕ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (U : Matrix (Fin m) (Fin m) ℂ) (start good : Fin m → ℂ)
    (hu : star U * U = 1) (hstart : U *ᵥ start = start)
    (hphase : ∀ (ν : ℂ) (v : Fin m → ℂ), U *ᵥ v = ν • v →
      (∑ i, star (v i) * start i) = 0 → v ≠ 0 →
      ∃ θ : ℝ, ε ≤ θ ∧ θ ≤ 2 * Real.pi - ε ∧ ν = Complex.exp (Complex.I * θ)) :
    ContinuousOn (groverSecularScalar m U good) (Set.Ioo 0 ε) := by
  intro β hβ
  let A : ℝ → Matrix (Fin m) (Fin m) ℂ := fun b =>
    U - Complex.exp (Complex.I * b) • (1 : Matrix (Fin m) (Fin m) ℂ)
  have hA : Continuous A := by dsimp only [A]; fun_prop
  have hi := minusOne_grover_resolvent_isUnit m ε β hε hε1 hβ.1 hβ.2 U start hu hstart hphase
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

/-- Opposite weak signs at endpoints inside the phase gap yield a secular root between them and
a nonzero resolvent eigenvector of `U * Uf` with good-state overlap one half. -/
theorem minusOne_grover_secular_root_of_signs (m : ℕ) (ε a b : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (ha : 0 < a) (hab : a ≤ b) (hb : b < ε)
    (Uf U : Matrix (Fin m) (Fin m) ℂ) (start good : Fin m → ℂ)
    (hu : star U * U = 1) (hstart : U *ᵥ start = start)
    (hgn : (∑ i, ‖good i‖ ^ 2) = 1)
    (hgood : Uf *ᵥ good = -good)
    (hfix : ∀ v : Fin m → ℂ, (∑ i, star (v i) * good i) = 0 → Uf *ᵥ v = v)
    (hphase : ∀ (ν : ℂ) (v : Fin m → ℂ), U *ᵥ v = ν • v →
      (∑ i, star (v i) * start i) = 0 → v ≠ 0 →
      ∃ θ : ℝ, ε ≤ θ ∧ θ ≤ 2 * Real.pi - ε ∧ ν = Complex.exp (Complex.I * θ))
    (hlo : 0 ≤ groverSecularScalar m U good a)
    (hhi : groverSecularScalar m U good b ≤ 0) :
    ∃ β ∈ Set.Icc a b,
      let z := Complex.exp (Complex.I * β)
      let y := (U - z • (1 : Matrix (Fin m) (Fin m) ℂ))⁻¹ *ᵥ (U *ᵥ good)
      groverSecularScalar m U good β = 0 ∧
        (star good ⬝ᵥ y) = 1 / 2 ∧ (U * Uf) *ᵥ y = z • y ∧ y ≠ 0 := by
  have hc := minusOne_grover_secular_continuousOn m ε hε hε1 U start good hu hstart hphase
  have hc' := hc.mono (Set.Icc_subset_Ioo ha hb)
  obtain ⟨β, hβ, hroot⟩ := intermediate_value_Icc' hab hc' (show (0 : ℝ) ∈
      Set.Icc (groverSecularScalar m U good b) (groverSecularScalar m U good a) from ⟨hhi, hlo⟩)
  let z := Complex.exp (Complex.I * β)
  let y := (U - z • (1 : Matrix (Fin m) (Fin m) ℂ))⁻¹ *ᵥ (U *ᵥ good)
  have hi := minusOne_grover_resolvent_isUnit m ε β hε hε1 (ha.trans_le hβ.1)
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

/-- Under the stated real-unitary, reflection, and phase-gap hypotheses with `0 < α ≤ ε^2 /
200`, a secular root lies between `ε * α / sqrt (2 * pi)` and `13 * α / 5` and yields a
nonzero eigenvector with good-state overlap one half. -/
theorem minusOne_grover_small_overlap_root (m : ℕ) (ε α : ℝ)
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
      ∃ θ : ℝ, ε ≤ θ ∧ θ ≤ 2 * Real.pi - ε ∧ ν = Complex.exp (Complex.I * θ)) :
    ∃ β ∈ Set.Icc (ε * α / Real.sqrt (2 * Real.pi)) ((13/5 : ℝ)*α),
      let z := Complex.exp (Complex.I * β)
      let y := (U - z • (1 : Matrix (Fin m) (Fin m) ℂ))⁻¹ *ᵥ (U *ᵥ good)
      groverSecularScalar m U good β = 0 ∧
        (star good ⬝ᵥ y) = 1/2 ∧ (U * Uf) *ᵥ y = z • y ∧ y ≠ 0 := by
  classical
  let lo := ε * α / Real.sqrt (2 * Real.pi)
  let hi := (13/5 : ℝ)*α
  obtain ⟨B, μ, w, s, hB, hB', hμ, he, hw, _, hmass, hsums, hwfix, hsfix, hweights⟩ :=
    minusOne_jw_unitary_gap_weights m ε α hε U start good hu hstart hsn hgn hoverlap hphase
  let eig := fun j => if μ j = 1 then (-1 : ℝ) else (μ j).re
  have heig := minusOne_jw_unitary_basis_real_gap m ε hε U B start μ hu hB hstart he hphase
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
    hwfix hsfix hsums hweights (minusOne_grover_resolvent_isUnit m ε lo hε hε1 hlop hloeps U start hu hstart hphase)
  have hshi := grover_secular_gap_weights m U B μ good α hi w s hu hU hg hB' hμ he
    hwfix hsfix hsums hweights (minusOne_grover_resolvent_isUnit m ε hi hε hε1 hhip hhieps U start hu hstart hphase)
  have hscalarlo : 0 ≤ groverSecularScalar m U good lo := by
    rw [hslo]
    exact mul_nonneg (div_nonneg hsinlo (by norm_num)) hsign.2
  have hscalarhi : groverSecularScalar m U good hi ≤ 0 := by
    rw [hshi]
    exact mul_nonpos_of_nonneg_of_nonpos (div_nonneg hsinhi (by norm_num)) hsign.1
  exact minusOne_grover_secular_root_of_signs m ε lo hi hε hε1 hlop hab hhieps Uf U start good
    hu hstart hgn hgood hfix hphase hscalarlo hscalarhi

/-- For a secular root in the specified interval under the real-unitary and small-overlap
assumptions, the coefficient `C` is positive, the squared norm of the imaginary part is at
most `36 / ε^2`, and its squared distance from `C • start` is at most `(2 * β * C / ε)^2`. -/
theorem minusOne_grover_small_overlap_normalization_bounds (m : ℕ) (ε α β : ℝ)
    (hε : 0<ε) (hε1 : ε≤1) (hα : 0<α) (hsmall : α≤ε^2/200)
    (hβbounds : β ∈ Set.Icc (ε*α/Real.sqrt (2*Real.pi)) ((13/5:ℝ)*α))
    (U : Matrix (Fin m) (Fin m) ℂ) (start good : Fin m → ℂ)
    (hu : star U*U=1) (hU : ∀i j,(U i j).im=0)
    (hsr : ∀i,(start i).im=0) (hgr : ∀i,(good i).im=0)
    (hsn : (∑i,‖start i‖^2)=1) (hgn : (∑i,‖good i‖^2)=1)
    (hoverlap : (∑i,star (good i)*start i)=(α:ℂ)) (hstart : U *ᵥ start=start)
    (hphase : ∀ (ν : ℂ) (v : Fin m → ℂ), U *ᵥ v=ν • v →
      (∑i,star (v i)*start i)=0 → v≠0 →
      ∃θ : ℝ, ε≤θ ∧ θ≤2*Real.pi-ε ∧ ν=Complex.exp (Complex.I*θ))
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
  have hinv := minusOne_grover_resolvent_isUnit m ε β hε hε1 hβp hβeps U start hu hstart hphase
  obtain ⟨B,μ,w,s,hB,hB',hμ,he,hw,_,hmass,hsums,hwfix,hsfix,hweights⟩ :=
    minusOne_jw_unitary_gap_weights m ε α hε U start good hu hstart hsn hgn hoverlap hphase
  let eig := fun j => if μ j=1 then (-1:ℝ) else (μ j).re
  have heig := minusOne_jw_unitary_basis_real_gap m ε hε U B start μ hu hB hstart he hphase
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

/-- Establishes `GroverIncludingMinusOne`, the Grover interpolation contract allowing eigenvalue
minus one in the background spectrum [Ambainis2007ElementDistinctness]. -/
theorem minusOne_groverInterpolation : GroverIncludingMinusOne := by
  intro m ε α hε hε1 hα _ Uf U start good huf hu hU hsr hgr hsn hgn hoverlap hgood hfix hstart hphase
  by_cases hlarge : ε^2/200≤α
  · exact groverInterpolation_large_overlap m ε α hε hε1 hα hlarge Uf U start good hoverlap
  have hsmall : α≤ε^2/200 := le_of_lt (lt_of_not_ge hlarge)
  obtain ⟨β,hβ,hroot,hyg,hy,_⟩ := minusOne_grover_small_overlap_root m ε α hε hε1 hα hsmall Uf U start good
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
  have hinv := minusOne_grover_resolvent_isUnit m ε β hε hε1 hβp hβeps U start hu hstart hphase
  have hz : Complex.exp (Complex.I*β)≠1 := jw_phase_ne_one β hβp (by linarith [Real.pi_gt_three])
  have hproj :=
      grover_resolvent_imaginary_start_overlap m α β U start good hu hstart hsr hoverlap hz hinv
  change star start ⬝ᵥ (fun i => ((y i).im:ℂ))=(C:ℂ) at hproj
  obtain ⟨hCp,hvbound,hrbound⟩ := minusOne_grover_small_overlap_normalization_bounds m ε α β hε hε1 hα hsmall hβ
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

/-- The exported proof of `GroverIncludingMinusOne`, corresponding to the version of the Lemma 3
interpolation statement that includes eigenvalue minus one
[Ambainis2007ElementDistinctness]. -/
theorem groverIncludingMinusOne_answer : GroverIncludingMinusOne :=
  minusOne_groverInterpolation

end Qatlib.Concepts.WalkFind.GroverInterp
