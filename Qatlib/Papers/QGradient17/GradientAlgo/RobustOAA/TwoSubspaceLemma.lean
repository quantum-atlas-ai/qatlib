/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.PureStateMath.Qubit
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The two-subspace iteration identity behind Lemma 40

[GilyenArunachalamWiebe2019], Lemma 40 (arXiv:1711.00465v3, Appendix C, p.58)
analyses the product of the two reflections `W (2 P₁ - 1) Wᴴ` and `2 P₂ - 1` on the
two-dimensional space spanned by two states `ψ` and `φ`. The
hypotheses say that `W` is unitary, that `W ψ` is the rotation of `ψ` towards
`φ` by the angle `θ`, that `2 P₂ - 1` fixes `φ` and negates `ψ`, that
`2 P₁ - 1` fixes `ψ`, and that `2 P₁ - 1` negates the image of
`cos θ • φ - sin θ • ψ` under `Wᴴ`. Under these hypotheses the product acts on
`W ψ` by rotating the two-dimensional space.

The exact statement proved here carries an overall sign: the `k`-th power of
`W (2 P₁ - 1) Wᴴ (2 P₂ - 1)` sends `W ψ` to `(-1)^k` times
`sin((2k+1) θ) • φ + cos((2k+1) θ) • ψ`. The sign cannot be dropped: the
unsigned identity is refuted by
`Qatlib.Papers.QGradient17.GradientAlgo.zero_angle_counterexample`, which is the
zero-angle instance `W = 1` of exactly the hypothesis set below.
`two_subspace_iterate_neg` records the equivalent form in which the negated
product `-W (2 P₁ - 1) Wᴴ (2 P₂ - 1)` has the paper's unsigned orbit.

Normalization of `ψ` and `φ` and their orthogonality are part of the paper's
two-dimensional setting; the iteration identity is linear and holds without
them, so no statement below depends on their values.

The file does not prove Lemma 40's geometric reading of `θ` as an angle of
`W`, nor any property of the projections `P₁` and `P₂` beyond the stated
actions on `ψ`, `φ` and `Wᴴ (cos θ • φ - sin θ • ψ)`.
-/

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.QGradient17.GradientAlgo.RobustOAA

variable {H : Type*} [Fintype H] [DecidableEq H]

omit [DecidableEq H] in
/-- A square matrix acts additively on amplitude vectors. -/
private theorem applyGate_add (U : Matrix H H ℂ) (x y : QState H) :
    ApplyGate U (x + y) = ApplyGate U x + ApplyGate U y := by
  unfold ApplyGate
  rw [Matrix.mulVec_add]

omit [DecidableEq H] in
/-- A square matrix acts subadditively on amplitude vectors. -/
private theorem applyGate_sub (U : Matrix H H ℂ) (x y : QState H) :
    ApplyGate U (x - y) = ApplyGate U x - ApplyGate U y := by
  unfold ApplyGate
  rw [Matrix.mulVec_sub]

omit [DecidableEq H] in
/-- A matrix difference acts by the difference of the images. -/
private theorem applyGate_sub_mat (A B : Matrix H H ℂ) (x : QState H) :
    ApplyGate (A - B) x = ApplyGate A x - ApplyGate B x := by
  unfold ApplyGate
  rw [Matrix.sub_mulVec]

omit [DecidableEq H] in
/-- A square matrix commutes with complex scalar multiplication of amplitude vectors. -/
private theorem applyGate_smul (c : ℂ) (U : Matrix H H ℂ) (x : QState H) :
    ApplyGate U (c • x) = c • ApplyGate U x := by
  unfold ApplyGate
  rw [Matrix.mulVec_smul]

omit [DecidableEq H] in
/-- A complex scalar multiple of a matrix acts by the scalar multiple of the image. -/
private theorem applyGate_smul_mat (c : ℂ) (U : Matrix H H ℂ) (x : QState H) :
    ApplyGate (c • U) x = c • ApplyGate U x := by
  unfold ApplyGate
  rw [Matrix.smul_mulVec]

omit [DecidableEq H] in
/-- A square matrix commutes with negation of amplitude vectors. -/
private theorem applyGate_neg (U : Matrix H H ℂ) (x : QState H) :
    ApplyGate U (-x) = -ApplyGate U x := by
  unfold ApplyGate
  rw [Matrix.mulVec_neg]

/-- A unitary matrix cancels against its adjoint on the left. -/
private theorem applyGate_conj_mul (A : Matrix H H ℂ) (h : A.conjTranspose * A = 1)
    (x : QState H) : ApplyGate A.conjTranspose (ApplyGate A x) = x := by
  rw [← applyGate_mul, h, applyGate_one]

/-- A unitary matrix cancels against its adjoint on the right. -/
private theorem applyGate_mul_conj (A : Matrix H H ℂ) (h : A * A.conjTranspose = 1)
    (x : QState H) : ApplyGate A (ApplyGate A.conjTranspose x) = x := by
  rw [← applyGate_mul, h, applyGate_one]

/-- The squared sine and cosine of a real angle, read in the complex numbers, sum to one. -/
private theorem sin_mul_self_add_cos_mul_self (θ : ℝ) :
    (Real.sin θ : ℂ) * (Real.sin θ : ℂ) + (Real.cos θ : ℂ) * (Real.cos θ : ℂ) = 1 := by
  have h := Real.sin_sq_add_cos_sq θ
  have h' : (((Real.sin θ) ^ 2 + (Real.cos θ) ^ 2 : ℝ) : ℂ) = 1 := by
    rw [h]
    norm_num
  push_cast at h'
  simpa [pow_two] using h'

omit [Fintype H] [DecidableEq H] in
/-- The first vector of the plane is recovered from its coordinates in the rotated frame
`sin θ • x + cos θ • y`, `cos θ • x - sin θ • y`. -/
private theorem eq_sin_smul_add_cos_smul {s c : ℂ} (h : s * s + c * c = 1) (x y : QState H) :
    x = s • (s • x + c • y) + c • (c • x - s • y) := by
  have hxy : s • (s • x + c • y) + c • (c • x - s • y) = (s * s + c * c) • x := by
    module
  rw [hxy, h, one_smul]

omit [Fintype H] [DecidableEq H] in
/-- The second vector of the plane is recovered from its coordinates in the rotated frame
`sin θ • x + cos θ • y`, `cos θ • x - sin θ • y`. -/
private theorem eq_cos_smul_sub_sin_smul {s c : ℂ} (h : s * s + c * c = 1) (x y : QState H) :
    y = c • (s • x + c • y) - s • (c • x - s • y) := by
  have hxy : c • (s • x + c • y) - s • (c • x - s • y) = (s * s + c * c) • y := by
    module
  rw [hxy, h, one_smul]

/-- One application of `W (2 P₁ - 1) Wᴴ (2 P₂ - 1)` to `c • φ + d • ψ`: the first factor
negates the `ψ` component and the second rotates the result by the angle `2θ`, with an overall
sign. -/
private theorem two_subspace_step (W P₁ P₂ : Matrix H H ℂ) (ψ φ : QState H) (θ : ℝ)
    (hW : W ∈ Matrix.unitaryGroup H ℂ)
    (hWψ : ApplyGate W ψ = (Real.sin θ : ℂ) • φ + (Real.cos θ : ℂ) • ψ)
    (hP₂φ : ApplyGate P₂ φ = φ) (hP₂ψ : ApplyGate P₂ ψ = 0)
    (hP₁ψ : ApplyGate P₁ ψ = ψ)
    (hP₁W : ApplyGate P₁ (ApplyGate W.conjTranspose
      ((Real.cos θ : ℂ) • φ - (Real.sin θ : ℂ) • ψ)) = 0)
    (c d : ℂ) :
    ApplyGate (W * ((2 : ℂ) • P₁ - 1) * W.conjTranspose * ((2 : ℂ) • P₂ - 1))
        (c • φ + d • ψ)
      = -(c * (Real.cos (2 * θ) : ℂ) + d * (Real.sin (2 * θ) : ℂ)) • φ
        + (c * (Real.sin (2 * θ) : ℂ) - d * (Real.cos (2 * θ) : ℂ)) • ψ := by
  obtain ⟨hWW, hWcomm⟩ : W * W.conjTranspose = 1 ∧ W.conjTranspose * W = 1 := by
    constructor
    · simpa only [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff).mp hW
    · simpa only [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff').mp hW
  set R₁ : Matrix H H ℂ := W * ((2 : ℂ) • P₁ - 1) * W.conjTranspose with hR₁
  set v : QState H := (Real.cos θ : ℂ) • φ - (Real.sin θ : ℂ) • ψ with hv
  have hsin : (Real.sin θ : ℂ) * (Real.sin θ : ℂ) + (Real.cos θ : ℂ) * (Real.cos θ : ℂ) = 1 :=
    sin_mul_self_add_cos_mul_self θ
  -- the two eigenvector relations of the reflection `R₁ = W (2 P₁ - 1) Wᴴ`
  have hR₁u : ApplyGate R₁ (ApplyGate W ψ) = ApplyGate W ψ := by
    rw [hR₁, applyGate_mul, applyGate_mul, applyGate_sub_mat, applyGate_smul_mat,
      applyGate_conj_mul W hWcomm ψ, hP₁ψ, applyGate_one]
    rw [show ((2 : ℂ) • ψ - ψ) = ψ from by rw [two_smul]; abel]
  have hR₁v : ApplyGate R₁ v = -v := by
    rw [hR₁, hv, applyGate_mul, applyGate_mul, applyGate_sub_mat, applyGate_smul_mat, hP₁W]
    rw [smul_zero, zero_sub, applyGate_neg, applyGate_one, applyGate_mul_conj W hWW]
  -- the rotated frame of the plane
  have hφ : φ = (Real.sin θ : ℂ) • ApplyGate W ψ + (Real.cos θ : ℂ) • v := by
    rw [hWψ, hv]
    exact eq_sin_smul_add_cos_smul (s := (Real.sin θ : ℂ)) (c := (Real.cos θ : ℂ)) hsin φ ψ
  have hψ : ψ = (Real.cos θ : ℂ) • ApplyGate W ψ - (Real.sin θ : ℂ) • v := by
    rw [hWψ, hv]
    exact eq_cos_smul_sub_sin_smul (s := (Real.sin θ : ℂ)) (c := (Real.cos θ : ℂ)) hsin φ ψ
  have hcos2 : (Real.cos (2 * θ) : ℂ) =
      (Real.cos θ : ℂ) * (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * (Real.sin θ : ℂ) := by
    have h : Real.cos (2 * θ) = Real.cos θ * Real.cos θ - Real.sin θ * Real.sin θ := by
      rw [Real.cos_two_mul, ← Real.sin_sq_add_cos_sq θ]
      ring
    rw [h]
    push_cast
    ring
  have hsin2 : (Real.sin (2 * θ) : ℂ) = 2 * (Real.sin θ : ℂ) * (Real.cos θ : ℂ) := by
    have h : Real.sin (2 * θ) = 2 * Real.sin θ * Real.cos θ := Real.sin_two_mul θ
    rw [h]
    push_cast
    ring
  -- the reflection acts on the plane by the double-angle matrix
  have hR₁φ : ApplyGate R₁ φ = -((Real.cos (2 * θ) : ℂ)) • φ + (Real.sin (2 * θ) : ℂ) • ψ := by
    conv_lhs => rw [hφ]
    rw [applyGate_add, applyGate_smul, applyGate_smul, hR₁u, hR₁v, hWψ, hv, hcos2, hsin2]
    module
  have hR₁ψ : ApplyGate R₁ ψ = (Real.sin (2 * θ) : ℂ) • φ + (Real.cos (2 * θ) : ℂ) • ψ := by
    conv_lhs => rw [hψ]
    rw [applyGate_sub, applyGate_smul, applyGate_smul, hR₁u, hR₁v, hWψ, hv, hcos2, hsin2]
    module
  -- the second reflection only flips the sign of the `ψ` component
  have hR₂ (z : QState H) :
      ApplyGate ((2 : ℂ) • P₂ - 1) z = (2 : ℂ) • ApplyGate P₂ z - z := by
    rw [applyGate_sub_mat, applyGate_smul_mat, applyGate_one]
  have hP₂lin : ApplyGate ((2 : ℂ) • P₂ - 1) (c • φ + d • ψ) = c • φ - d • ψ := by
    rw [hR₂, applyGate_add, applyGate_smul, applyGate_smul, hP₂φ, hP₂ψ, smul_zero, add_zero]
    module
  rw [applyGate_mul, hP₂lin, applyGate_sub, applyGate_smul, applyGate_smul, hR₁φ, hR₁ψ]
  module

/-- Lemma 40 of Gilyén, Arunachalam and Wiebe (arXiv:1711.00465v3, Appendix C, p.58): the `k`-th
power of the product `W (2 P₁ - 1) Wᴴ (2 P₂ - 1)` sends `W ψ` to `(-1)^k` times the double-angle
orbit `sin((2k+1) θ) • φ + cos((2k+1) θ) • ψ`. -/
theorem two_subspace_iterate (W P₁ P₂ : Matrix H H ℂ) (ψ φ : QState H) (θ : ℝ)
    (hW : W ∈ Matrix.unitaryGroup H ℂ) (_hψ : Normalized ψ) (_hφ : Normalized φ)
    (_horth : ∑ i, star (φ i) * ψ i = 0)
    (hWψ : ApplyGate W ψ = (Real.sin θ : ℂ) • φ + (Real.cos θ : ℂ) • ψ)
    (hP₂φ : ApplyGate P₂ φ = φ) (hP₂ψ : ApplyGate P₂ ψ = 0)
    (hP₁ψ : ApplyGate P₁ ψ = ψ)
    (hP₁W : ApplyGate P₁ (ApplyGate W.conjTranspose
      ((Real.cos θ : ℂ) • φ - (Real.sin θ : ℂ) • ψ)) = 0) :
    ∀ k : ℕ,
      ApplyGate ((W * ((2 : ℂ) • P₁ - 1) * W.conjTranspose * ((2 : ℂ) • P₂ - 1)) ^ k)
          (ApplyGate W ψ)
        = ((-1 : ℂ) ^ k * (Real.sin ((2 * (k : ℝ) + 1) * θ) : ℂ)) • φ
          + ((-1 : ℂ) ^ k * (Real.cos ((2 * (k : ℝ) + 1) * θ) : ℂ)) • ψ := by
  have hsin_step : ∀ k : ℕ,
      ((-1 : ℂ) ^ (k + 1) * (Real.sin ((2 * (k : ℝ) + 1) * θ + 2 * θ) : ℂ)) =
        -(((-1 : ℂ) ^ k * (Real.sin ((2 * (k : ℝ) + 1) * θ) : ℂ)) *
              (Real.cos (2 * θ) : ℂ) +
            ((-1 : ℂ) ^ k * (Real.cos ((2 * (k : ℝ) + 1) * θ) : ℂ)) *
              (Real.sin (2 * θ) : ℂ)) := by
    intro k
    rw [pow_succ, Real.sin_add]
    push_cast
    ring
  have hcos_step : ∀ k : ℕ,
      ((-1 : ℂ) ^ (k + 1) * (Real.cos ((2 * (k : ℝ) + 1) * θ + 2 * θ) : ℂ)) =
        ((-1 : ℂ) ^ k * (Real.sin ((2 * (k : ℝ) + 1) * θ) : ℂ)) *
              (Real.sin (2 * θ) : ℂ) -
          ((-1 : ℂ) ^ k * (Real.cos ((2 * (k : ℝ) + 1) * θ) : ℂ)) *
              (Real.cos (2 * θ) : ℂ) := by
    intro k
    rw [pow_succ, Real.cos_add]
    push_cast
    ring
  intro k
  induction k with
  | zero =>
      simpa using hWψ
  | succ k ih =>
      have harg : ((2 * ((k + 1 : ℕ) : ℝ) + 1) * θ) = (2 * (k : ℝ) + 1) * θ + 2 * θ := by
        push_cast
        ring
      rw [pow_succ', applyGate_mul, ih,
        two_subspace_step W P₁ P₂ ψ φ θ hW hWψ hP₂φ hP₂ψ hP₁ψ hP₁W]
      rw [harg, ← hsin_step k, ← hcos_step k]

/-- An integer power of a negated matrix is the corresponding sign times the power. -/
private theorem neg_pow_smul (M : Matrix H H ℂ) (k : ℕ) :
    (-M) ^ k = (-1 : ℂ) ^ k • M ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, ih, show (-M : Matrix H H ℂ) = (-1 : ℂ) • M from
        (neg_one_smul ℂ M).symm, Matrix.smul_mul, Matrix.mul_smul, smul_smul, pow_succ,
        pow_succ]

/-- The paper's unsigned orbit, stated for the negated product: the `k`-th power of
`-(W (2 P₁ - 1) Wᴴ (2 P₂ - 1))` sends `W ψ` to `sin((2k+1) θ) • φ + cos((2k+1) θ) • ψ`.
Unlike the unsigned product this identity is consistent at `θ = 0`. -/
theorem two_subspace_iterate_neg (W P₁ P₂ : Matrix H H ℂ) (ψ φ : QState H) (θ : ℝ)
    (hW : W ∈ Matrix.unitaryGroup H ℂ) (_hψ : Normalized ψ) (_hφ : Normalized φ)
    (_horth : ∑ i, star (φ i) * ψ i = 0)
    (hWψ : ApplyGate W ψ = (Real.sin θ : ℂ) • φ + (Real.cos θ : ℂ) • ψ)
    (hP₂φ : ApplyGate P₂ φ = φ) (hP₂ψ : ApplyGate P₂ ψ = 0)
    (hP₁ψ : ApplyGate P₁ ψ = ψ)
    (hP₁W : ApplyGate P₁ (ApplyGate W.conjTranspose
      ((Real.cos θ : ℂ) • φ - (Real.sin θ : ℂ) • ψ)) = 0) :
    ∀ k : ℕ,
      ApplyGate ((-(W * ((2 : ℂ) • P₁ - 1) * W.conjTranspose *
            ((2 : ℂ) • P₂ - 1))) ^ k) (ApplyGate W ψ)
        = (Real.sin ((2 * (k : ℝ) + 1) * θ) : ℂ) • φ
          + (Real.cos ((2 * (k : ℝ) + 1) * θ) : ℂ) • ψ := by
  intro k
  have hsign : (-1 : ℂ) ^ k * (-1 : ℂ) ^ k = 1 := by
    rw [← mul_pow]
    norm_num
  rw [neg_pow_smul, applyGate_smul_mat,
    two_subspace_iterate W P₁ P₂ ψ φ θ hW _hψ _hφ _horth hWψ hP₂φ hP₂ψ hP₁ψ hP₁W,
    smul_add, smul_smul, smul_smul, ← mul_assoc, ← mul_assoc, hsign, one_mul, one_mul]

end Qatlib.Papers.QGradient17.GradientAlgo.RobustOAA
