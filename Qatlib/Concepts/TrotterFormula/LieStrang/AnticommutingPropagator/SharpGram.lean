/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.LieStrang.AnticommutingPropagator.SharpGramDefs
import Qatlib.Concepts.TrotterFormula.LieStrang.AnticommutingPropagator.Algebra
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity

/-!
# Gram bounds for anticommuting propagators

This module computes the Gram matrix of a rescaled step built from anticommuting Hermitian
involutions and proves operator and vector norm bounds. The component square and Hermiticity
reduce the norm estimates to real scalar inequalities, in the matrix norm setting of
[Bhatia1997].

For trigonometric coefficients with `ν² = ω² - a²` and `0 < a < ω`, the resulting upper and
inverse bounds are controlled by `(ω + a) / ν`.

## Main statements

* `sharp_gram_identity`: the explicit decomposition of the step Gram matrix.
* `sharp_gram_generic_bounds`: component identities and bounds with radius `sharpGramRadius d`.
* `sharp_gram_physical_bounds`: bounds for the trigonometric coefficients.
* `sharp_gram_bounds`: the combined Gram specification.

## References

* [Bhatia, 1997][Bhatia1997]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.TrotterFormula.LieStrang.AnticommutingPropagator
open Matrix
open scoped Matrix.Norms.L2Operator

variable {I : Type} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in

/-- The anticommutation identity for `P * Q` also holds with `P` and `Q` interchanged. -/
private theorem reverse_product (P Q : Matrix I I ℂ)
    (hPQ : P * Q = -(Q * P)) : Q * P = -(P * Q) := by
  rw [hPQ, neg_neg]

omit [DecidableEq I] in

/-- The Gram component `c Q - ih P Q` is Hermitian for anticommuting Hermitian `P` and `Q` and
real `c`, `h`. -/
theorem sharp_gram_component_hermitian (P Q : Matrix I I ℂ) (c h : ℝ)
    (hPh : P.IsHermitian) (hQh : Q.IsHermitian)
    (hPQ : P * Q = -(Q * P)) :
    (sharpGramComponent P Q c h).IsHermitian := by
  change (sharpGramComponent P Q c h)ᴴ = sharpGramComponent P Q c h
  unfold sharpGramComponent
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, hPh.eq, hQh.eq,
    reverse_product P Q hPQ]
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply,
    smul_eq_mul, star_mul, Complex.star_def, Complex.conj_I, Complex.conj_ofReal]
  ring

/-- Anticommuting involutions satisfy the five stated product identities for `P`, `Q`, and `P *
Q`, including `(P * Q)² = -1`. -/
private theorem product_relations (P Q : Matrix I I ℂ)
    (hP : P * P = 1) (hQ : Q * Q = 1) (hPQ : P * Q = -(Q * P)) :
    Q * (P * Q) = -P ∧ (P * Q) * Q = P ∧
      (P * Q) * P = -Q ∧ P * (P * Q) = Q ∧
      (P * Q) * (P * Q) = -(1 : Matrix I I ℂ) := by
  have hQP := reverse_product P Q hPQ
  have h1 : Q * (P * Q) = -P := by
    rw [← mul_assoc, hQP, neg_mul, mul_assoc, hQ, mul_one]
  have h2 : (P * Q) * Q = P := by rw [mul_assoc, hQ, mul_one]
  have h3 : (P * Q) * P = -Q := by
    rw [mul_assoc, hQP, mul_neg, ← mul_assoc, hP, one_mul]
  have h4 : P * (P * Q) = Q := by rw [← mul_assoc, hP, one_mul]
  have h5 : (P * Q) * (P * Q) = -(1 : Matrix I I ℂ) := by
    rw [← mul_assoc, h3, neg_mul, hQ]
  exact ⟨h1,h2,h3,h4,h5⟩

/-- For anticommuting involutions and `c² + h² - d² = 1`, the Gram component squares to `(1 +
d²)` times identity. -/
theorem sharp_gram_component_square (P Q : Matrix I I ℂ) (c h d : ℝ)
    (hP : P * P = 1) (hQ : Q * Q = 1) (hPQ : P * Q = -(Q * P))
    (hcs : c ^ 2 + h ^ 2 - d ^ 2 = 1) :
    sharpGramComponent P Q c h * sharpGramComponent P Q c h =
      (((1 + d ^ 2 : ℝ) : ℂ)) • (1 : Matrix I I ℂ) := by
  have hs : (c : ℂ)^2 + (h : ℂ)^2 - (d : ℂ)^2 = 1 := by exact_mod_cast hcs
  obtain ⟨h1,h2,_,_,h5⟩ := product_relations P Q hP hQ hPQ
  unfold sharpGramComponent
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm]
  rw [hQ,h1,h2,h5]
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul]
  push_cast
  ring_nf
  simp only [Complex.I_sq]
  linear_combination ((1 : Matrix I I ℂ) i j) * hs

/-- The Gram component anticommutes with `P` when `P` and `Q` are anticommuting involutions. -/
theorem sharp_gram_component_anticommute (P Q : Matrix I I ℂ) (c h : ℝ)
    (hP : P * P = 1) (hQ : Q * Q = 1) (hPQ : P * Q = -(Q * P)) :
    sharpGramComponent P Q c h * P = -(P * sharpGramComponent P Q c h) := by
  obtain ⟨_,_,h3,h4,_⟩ := product_relations P Q hP hQ hPQ
  unfold sharpGramComponent
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm]
  rw [reverse_product P Q hPQ,h3,h4]
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul]
  ring

/-- For anticommuting Hermitian involutions and `c² + h² - d² = 1`, the step Gram matrix equals
`(1 + 2d²)` times identity plus `2d` times the Gram component. -/
theorem sharp_gram_identity (P Q : Matrix I I ℂ) (c h d : ℝ)
    (hPh : P.IsHermitian) (hQh : Q.IsHermitian)
    (hP : P * P = 1) (hQ : Q * Q = 1) (hPQ : P * Q = -(Q * P))
    (hcs : c ^ 2 + h ^ 2 - d ^ 2 = 1) :
    (rescaledStep P Q d h c 1)ᴴ * rescaledStep P Q d h c 1 =
      (((1 + 2 * d ^ 2 : ℝ) : ℂ)) • (1 : Matrix I I ℂ) +
        (((2 * d : ℝ) : ℂ)) • sharpGramComponent P Q c h := by
  have hs : (c : ℂ)^2 + (h : ℂ)^2 - (d : ℂ)^2 = 1 := by exact_mod_cast hcs
  simp only [rescaledStep, shiftedGenerator, Complex.ofReal_one, one_smul]
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, hPh.eq, hQh.eq, star_mul,
    Complex.star_def, Complex.conj_I, Complex.conj_ofReal]
  unfold sharpGramComponent
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    smul_add, smul_smul, one_mul, mul_one]
  rw [hP,hQ,reverse_product P Q hPQ]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.neg_apply, smul_eq_mul]
  push_cast
  ring_nf
  simp only [Complex.I_sq]
  linear_combination ((1 : Matrix I I ℂ) i j) * hs

/-- A nonnegative real scalar times the identity matrix has norm at most that scalar. -/
private theorem norm_real_identity_le (r : ℝ) (hr : 0 ≤ r) :
    ‖(r : ℂ) • (1 : Matrix I I ℂ)‖ ≤ r := by
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hr]
  calc
    r * ‖(1 : Matrix I I ℂ)‖ ≤ r * 1 :=
      mul_le_mul_of_nonneg_left Qatlib.Foundations.OperatorErrors.OperatorError.l2_norm_one_le hr
    _ = r := mul_one r

/-- Under the Hermitian involution, anticommutation, and coefficient hypotheses, the Gram
component has norm at most `sqrt (1 + d²)`. -/
theorem sharp_gram_component_norm (P Q : Matrix I I ℂ) (c h d : ℝ)
    (hPh : P.IsHermitian) (hQh : Q.IsHermitian)
    (hP : P * P = 1) (hQ : Q * Q = 1) (hPQ : P * Q = -(Q * P))
    (hcs : c ^ 2 + h ^ 2 - d ^ 2 = 1) :
    ‖sharpGramComponent P Q c h‖ ≤ Real.sqrt (1 + d ^ 2) := by
  let T := sharpGramComponent P Q c h
  have hTh : T.IsHermitian := sharp_gram_component_hermitian P Q c h hPh hQh hPQ
  have hTT : T * T = (((1 + d ^ 2 : ℝ) : ℂ)) • (1 : Matrix I I ℂ) :=
    sharp_gram_component_square P Q c h d hP hQ hPQ hcs
  have ht : ‖T‖ * ‖T‖ ≤ 1 + d ^ 2 := by
    calc
      ‖T‖ * ‖T‖ = ‖Tᴴ * T‖ := (Matrix.l2_opNorm_conjTranspose_mul_self T).symm
      _ = ‖(((1 + d ^ 2 : ℝ) : ℂ)) • (1 : Matrix I I ℂ)‖ := by rw [hTh.eq,hTT]
      _ ≤ 1 + d ^ 2 := norm_real_identity_le _ (by positivity)
  have hs := Real.sq_sqrt (show 0 ≤ 1 + d ^ 2 by positivity)
  have hp := Real.sqrt_nonneg (1 + d ^ 2)
  change ‖T‖ ≤ Real.sqrt (1 + d ^ 2)
  nlinarith [norm_nonneg T]

/-- Under the Hermitian involution, anticommutation, and coefficient hypotheses, the rescaled
step has norm at most `sharpGramRadius d`. -/
theorem sharp_gram_operator_norm (P Q : Matrix I I ℂ) (c h d : ℝ)
    (hPh : P.IsHermitian) (hQh : Q.IsHermitian)
    (hP : P * P = 1) (hQ : Q * Q = 1) (hPQ : P * Q = -(Q * P))
    (hcs : c ^ 2 + h ^ 2 - d ^ 2 = 1) :
    ‖rescaledStep P Q d h c 1‖ ≤ sharpGramRadius d := by
  let F := rescaledStep P Q d h c 1
  let T := sharpGramComponent P Q c h
  have hg := sharp_gram_identity P Q c h d hPh hQh hP hQ hPQ hcs
  have ht := sharp_gram_component_norm P Q c h d hPh hQh hP hQ hPQ hcs
  have hG : ‖Fᴴ * F‖ ≤ 1 + 2 * d ^ 2 + |2 * d| * Real.sqrt (1 + d ^ 2) := by
    calc
      ‖Fᴴ * F‖ = ‖(((1 + 2 * d ^ 2 : ℝ) : ℂ)) • (1 : Matrix I I ℂ) +
          (((2 * d : ℝ) : ℂ)) • T‖ := congrArg norm hg
      _ ≤ ‖(((1 + 2 * d ^ 2 : ℝ) : ℂ)) • (1 : Matrix I I ℂ)‖ +
          ‖(((2 * d : ℝ) : ℂ)) • T‖ := norm_add_le _ _
      _ ≤ 1 + 2 * d ^ 2 + |2 * d| * Real.sqrt (1 + d ^ 2) := by
        apply add_le_add (norm_real_identity_le _ (by positivity))
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left ht (abs_nonneg _)
  have htwo : |(2 : ℝ) * d| = 2 * |d| := by rw [abs_mul]; norm_num
  rw [htwo,Matrix.l2_opNorm_conjTranspose_mul_self] at hG
  have hs := Real.sq_sqrt (show 0 ≤ 1 + d ^ 2 by positivity)
  have hp := Real.sqrt_nonneg (1 + d ^ 2)
  have ha := sq_abs d
  change ‖F‖ ≤ Real.sqrt (1 + d ^ 2) + |d|
  nlinarith [norm_nonneg F, abs_nonneg d]

omit [Fintype I] in

/-- Negating the two generator coefficients in a unit rescaled step is equivalent to negating
its step parameter. -/
theorem rescaledStep_neg_coefficients (P Q : Matrix I I ℂ) (c h d : ℝ) :
    rescaledStep P Q (-d) (-h) c 1 = rescaledStep P Q d h c (-1) := by
  unfold rescaledStep shiftedGenerator
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Complex.ofReal_neg, Complex.ofReal_one]
  ring

/-- The coefficient relation for anticommuting Hermitian involutions yields the Gram
decomposition, component identities, an operator upper bound, and a vector inverse bound
with radius `sharpGramRadius d`. -/
theorem sharp_gram_generic_bounds (P Q : Matrix I I ℂ) (c h d : ℝ)
    (hPh : P.IsHermitian) (hQh : Q.IsHermitian)
    (hP : P * P = 1) (hQ : Q * Q = 1) (hPQ : P * Q = -(Q * P))
    (hcs : c ^ 2 + h ^ 2 - d ^ 2 = 1) :
    let F := rescaledStep P Q d h c 1
    let T := sharpGramComponent P Q c h
    let R := sharpGramRadius d
    Fᴴ * F = (((1 + 2 * d ^ 2 : ℝ) : ℂ)) • (1 : Matrix I I ℂ) +
      (((2 * d : ℝ) : ℂ)) • T ∧
    T.IsHermitian ∧
    T * T = (((1 + d ^ 2 : ℝ) : ℂ)) • (1 : Matrix I I ℂ) ∧
    T * P = -(P * T) ∧ ‖F‖ ≤ R ∧
    (∀ v : Qatlib.Foundations.PureStateMath.QState I,
      ‖Qatlib.Foundations.PureStateMath.BornBridge.toEuclidean_fromVec v‖ ≤ R * ‖Qatlib.Foundations.PureStateMath.BornBridge.toEuclidean_fromVec (F *ᵥ v)‖) := by
  refine ⟨sharp_gram_identity P Q c h d hPh hQh hP hQ hPQ hcs,
    sharp_gram_component_hermitian P Q c h hPh hQh hPQ,
    sharp_gram_component_square P Q c h d hP hQ hPQ hcs,
    sharp_gram_component_anticommute P Q c h hP hQ hPQ,
    sharp_gram_operator_norm P Q c h d hPh hQh hP hQ hPQ hcs,?_⟩
  intro v
  have hnegative : c ^ 2 + (-h) ^ 2 - (-d) ^ 2 = 1 := by nlinarith [hcs]
  have hn := sharp_gram_operator_norm P Q c (-h) (-d) hPh hQh hP hQ hPQ hnegative
  have hbound : ‖rescaledStep P Q d h c (-1)‖ ≤ sharpGramRadius d := by
    rw [rescaledStep_neg_coefficients] at hn
    simpa only [sharpGramRadius, neg_sq, abs_neg] using hn
  have hi := (rescaledStep_inverse P Q d h c 1 hP hQ hPQ (by nlinarith [hcs])).1
  have hv := Qatlib.Concepts.ReferenceError.RefTraceError.l2_norm_mulVec_fromVec_le (rescaledStep P Q d h c (-1))
    (rescaledStep P Q d h c 1 *ᵥ v)
  rw [Matrix.mulVec_mulVec,hi,Matrix.one_mulVec] at hv
  exact hv.trans (mul_le_mul_of_nonneg_right hbound (norm_nonneg _))

/-- If `0 < a < ω`, `ν > 0`, and `ν² = ω² - a²`, the radius at `a * sin (ν * t) / ν` is at most
`(ω + a) / ν`. -/
theorem sharp_gram_physical_radius (a ω ν t : ℝ)
    (ha : 0 < a) (haω : a < ω) (hν : 0 < ν) (hsq : ν ^ 2 = ω ^ 2 - a ^ 2) :
    sharpGramRadius (a * (Real.sin (ν * t) / ν)) ≤ (ω + a) / ν := by
  have hω : 0 < ω := ha.trans haω
  have hd : |a * (Real.sin (ν * t) / ν)| ≤ a / ν := by
    rw [abs_mul,abs_of_pos ha,abs_div,abs_of_pos hν]
    calc
      a * (|Real.sin (ν * t)| / ν) ≤ a * (1 / ν) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right (Real.abs_sin_le_one _) hν.le) ha.le
      _ = a / ν := by ring
  have hd2 : (a * (Real.sin (ν * t) / ν)) ^ 2 ≤ (a / ν) ^ 2 := by
    nlinarith [sq_abs (a * (Real.sin (ν * t) / ν)), abs_nonneg (a * (Real.sin (ν * t) / ν)),
      div_nonneg ha.le hν.le]
  have hr := Real.sqrt_le_sqrt (show 1 + (a * (Real.sin (ν * t) / ν)) ^ 2 ≤
      1 + (a / ν) ^ 2 by linarith)
  have he : Real.sqrt (1 + (a / ν) ^ 2) = ω / ν := by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (div_nonneg hω.le hν.le)).2
    field_simp [hν.ne']
    nlinarith [hsq]
  unfold sharpGramRadius
  calc
    _ ≤ ω / ν + a / ν := add_le_add (hr.trans he.le) hd
    _ = (ω + a) / ν := by ring

omit [Fintype I] in

/-- Absorbing the step parameter `s` into both generator coefficients leaves the rescaled step
unchanged. -/
theorem rescaledStep_physical_coefficients (P Q : Matrix I I ℂ) (a ω c s : ℝ) :
    rescaledStep P Q (a * s) (ω * s) c 1 = rescaledStep P Q a ω c s := by
  unfold rescaledStep shiftedGenerator
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Complex.ofReal_mul, Complex.ofReal_one]
  ring

/-- For anticommuting Hermitian involutions and the stated positive parameters, the
trigonometric rescaled step has radius and operator norm at most `(ω + a) / ν`, with
matching upper and inverse vector bounds. -/
theorem sharp_gram_physical_bounds (P Q : Matrix I I ℂ) (a ω ν t : ℝ)
    (hPh : P.IsHermitian) (hQh : Q.IsHermitian)
    (hP : P * P = 1) (hQ : Q * Q = 1) (hPQ : P * Q = -(Q * P))
    (ha : 0 < a) (haω : a < ω) (hν : 0 < ν) (hsq : ν ^ 2 = ω ^ 2 - a ^ 2) :
    let F := rescaledStep P Q a ω (Real.cos (ν * t)) (Real.sin (ν * t) / ν)
    let R := sharpGramRadius (a * (Real.sin (ν * t) / ν))
    let κ := (ω + a) / ν
    R ≤ κ ∧ ‖F‖ ≤ κ ∧
    (∀ v : Qatlib.Foundations.PureStateMath.QState I,
      ‖Qatlib.Foundations.PureStateMath.BornBridge.toEuclidean_fromVec (F *ᵥ v)‖ ≤ κ * ‖Qatlib.Foundations.PureStateMath.BornBridge.toEuclidean_fromVec v‖ ∧
      ‖Qatlib.Foundations.PureStateMath.BornBridge.toEuclidean_fromVec v‖ ≤ κ * ‖Qatlib.Foundations.PureStateMath.BornBridge.toEuclidean_fromVec (F *ᵥ v)‖) := by
  let c := Real.cos (ν * t)
  let s := Real.sin (ν * t) / ν
  have hcurve : c ^ 2 + (ω * s) ^ 2 - (a * s) ^ 2 = 1 := by
    calc
      _ = Real.cos (ν * t) ^ 2 + (ω ^ 2 - a ^ 2) *
          (Real.sin (ν * t) / ν) ^ 2 := by dsimp [c,s]; ring
      _ = Real.cos (ν * t) ^ 2 + Real.sin (ν * t) ^ 2 := by
        rw [← hsq,div_pow,mul_div_cancel₀ _ (pow_ne_zero 2 hν.ne')]
      _ = 1 := by nlinarith [Real.sin_sq_add_cos_sq (ν * t)]
  have hg := sharp_gram_generic_bounds P Q c (ω * s) (a * s)
    hPh hQh hP hQ hPQ hcurve
  dsimp only at hg
  have hn := hg.2.2.2.2.1
  have hi := hg.2.2.2.2.2
  rw [rescaledStep_physical_coefficients] at hn hi
  have hr := sharp_gram_physical_radius a ω ν t ha haω hν hsq
  refine ⟨hr,hn.trans hr,?_⟩
  intro v
  constructor
  · exact (Qatlib.Concepts.ReferenceError.RefTraceError.l2_norm_mulVec_fromVec_le _ v).trans
      (mul_le_mul_of_nonneg_right (hn.trans hr) (norm_nonneg _))
  · exact (hi v).trans (mul_le_mul_of_nonneg_right hr (norm_nonneg _))

/-- The generic and trigonometric Gram bounds together satisfy `SharpGramSpecification`. -/
theorem sharp_gram_bounds : SharpGramSpecification := by
  constructor
  · intro I _ _ P Q c h d hPh hQh hP hQ hPQ hcs
    exact sharp_gram_generic_bounds P Q c h d hPh hQh hP hQ hPQ hcs
  · intro I _ _ P Q a ω ν t hPh hQh hP hQ hPQ ha haω hν hsq
    exact sharp_gram_physical_bounds P Q a ω ν t hPh hQh hP hQ hPQ ha haω hν hsq

end Qatlib.Concepts.TrotterFormula.LieStrang.AnticommutingPropagator
