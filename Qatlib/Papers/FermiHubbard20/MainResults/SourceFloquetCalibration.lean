/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FermionAlgebra.CarJordanWigner.FermionHubbard

set_option backward.isDefEq.respectTransparency false

/-!
# Floquet calibration of the entangling gate (source §III, Supplemental §C)

Claim `FermiHubbard20.c002` (metadata/papers/FermiHubbard20.json) concerns the
fast Floquet calibration protocol of arXiv:2010.07965 (Supplemental §C,
Eq. (18)–(38)).  Its mathematical content, formalised in this file, is:

* the cycle unitary `U_c = U · RZ` has a `2 × 2` "entangling block" `u2`
  (Eq. (18), (21), (24));
* the eigenvalues of `u2` read off the gate parameters: the determinant gives
  the global phase `e^{-2iγ}` and the trace gives the Rabi angle `Ω` via
  `trace = 2 e^{-iγ} cos Ω` (Eq. (37)), and
* repeating the block `n` times multiplies the angle by `n`,
  `u2ⁿ = cos(nΩ)·1 - sin(nΩ)·τ` with `τ² = -1` (Eq. (28)–(29)) — the
  `n`-fold amplification of parameter deviations.

The empirical parts of the claim (uniqueness of the gate from a finite set of
single-qubit probes, and robustness to SPAM errors) are documented in the
docstrings; the algebraic core above is fully proved.
-/

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators

namespace Qatlib.Papers.FermiHubbard20.MainResults

/-! ## Complex phases -/

/-- `e^{-i a}`, the phase used in the source's Eq. (23) for `u`. -/
def eim (a : ℝ) : ℂ := Complex.exp (-(Complex.I) * (a : ℂ))

/-- `e^{i a}`, the phase used for the read-out rotations `RZ`. -/
def epos (a : ℝ) : ℂ := Complex.exp ((Complex.I) * (a : ℂ))

/-- Euler form of `eim`. -/
lemma eim_euler (a : ℝ) :
    eim a = (Real.cos a : ℂ) - Complex.I * (Real.sin a : ℂ) := by
  unfold eim
  have harg : -(Complex.I) * (a : ℂ) = (-a : ℝ) * Complex.I := by push_cast; ring
  rw [harg, Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
  push_cast; ring

/-- Euler form of `epos`. -/
lemma epos_euler (a : ℝ) :
    epos a = (Real.cos a : ℂ) + Complex.I * (Real.sin a : ℂ) := by
  unfold epos
  have harg : (Complex.I) * (a : ℂ) = (a : ℝ) * Complex.I := by push_cast; ring
  rw [harg, Complex.exp_ofReal_mul_I]
  ring

/-- Additivity of `eim`. -/
lemma eim_add (a b : ℝ) : eim a * eim b = eim (a + b) := by
  unfold eim
  rw [← Complex.exp_add]; congr 1; push_cast; ring

/-- `eim` at `0` is `1`. -/
@[simp] lemma eim_zero : eim 0 = 1 := by unfold eim; simp

/-- `eim a + eim (-a) = 2 cos a`. -/
lemma eim_add_eim_neg (a : ℝ) : eim a + eim (-a) = 2 * (Real.cos a : ℂ) := by
  rw [eim_euler a, eim_euler (-a), Real.cos_neg, Real.sin_neg]
  push_cast
  ring

/-- `epos a · eim a = 1`. -/
lemma epos_mul_eim (a : ℝ) : epos a * eim a = 1 := by
  unfold epos eim
  rw [← Complex.exp_add]
  have h : Complex.I * (a : ℂ) + -(Complex.I) * (a : ℂ) = 0 := by ring
  rw [h, Complex.exp_zero]

/-! ## The Rabi angle `Ω` (Eq. (24)) -/

/-- Rabi angle `Ω = arccos(cos θ · cos ζ)` of the effective `2 × 2` rotation
produced by the cycle (source Eq. (24): `Ω(θ,ζ) = arccos(cos θ cos ζ) ∈ [0,π]`). -/
def Omega (θ ζ : ℝ) : ℝ := Real.arccos (Real.cos θ * Real.cos ζ)

/-- `cos Ω = cos θ · cos ζ`. -/
lemma cos_Omega (θ ζ : ℝ) : Real.cos (Omega θ ζ) = Real.cos θ * Real.cos ζ := by
  unfold Omega
  apply Real.cos_arccos
  · have h1 : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
    have h2 : |Real.cos ζ| ≤ 1 := Real.abs_cos_le_one ζ
    have habs : |Real.cos θ * Real.cos ζ| ≤ 1 := by
      rw [abs_mul]
      calc |Real.cos θ| * |Real.cos ζ| ≤ 1 * 1 :=
            mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    exact (abs_le.mp habs).1
  · have h1 : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
    have h2 : |Real.cos ζ| ≤ 1 := Real.abs_cos_le_one ζ
    have habs : |Real.cos θ * Real.cos ζ| ≤ 1 := by
      rw [abs_mul]
      calc |Real.cos θ| * |Real.cos ζ| ≤ 1 * 1 :=
            mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    exact (abs_le.mp habs).2

/-- **Rabi-angle bounds (source Eq. (38)).**  For `0 ≤ θ ≤ π/2` and any
`ζ`, the Rabi angle lies in `[θ, π − θ]`.  This is what makes the calibration
robust: `Ω` never degenerates even when `cos ζ` varies over its full range. -/
theorem rabi_bounds {θ : ℝ} (ζ : ℝ) (hθ0 : 0 ≤ θ) (hθ2 : θ ≤ Real.pi / 2) :
    θ ≤ Omega θ ζ ∧ Omega θ ζ ≤ Real.pi - θ := by
  have hcos0 : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hθ2⟩
  have hθπ : θ ≤ Real.pi := by linarith [Real.pi_pos, hθ2]
  have hlow : Real.cos θ * Real.cos ζ ≤ Real.cos θ := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.cos_le_one ζ) hcos0
  have hhigh : -Real.cos θ ≤ Real.cos θ * Real.cos ζ := by
    have h := mul_le_mul_of_nonneg_left (Real.neg_one_le_cos ζ) hcos0
    simpa only [mul_neg, mul_one] using h
  constructor
  · have h1 : Real.arccos (Real.cos θ) ≤ Real.arccos (Real.cos θ * Real.cos ζ) :=
      Real.arccos_le_arccos hlow
    rwa [Real.arccos_cos hθ0 hθπ] at h1
  · have h1 : Real.arccos (Real.cos θ * Real.cos ζ) ≤ Real.arccos (-Real.cos θ) :=
      Real.arccos_le_arccos hhigh
    rw [Real.arccos_neg, Real.arccos_cos hθ0 hθπ] at h1
    exact h1

/-! ## The entangling block `u2` and the operator `σ̃` (Eq. (23)–(25)) -/

/-- The `2 × 2` entangling block `u2` of the cycle unitary (source Eq. (23),
(24)).  It already has the global phase `e^{-iγ}` factored out. -/
def u2 (θ ζ χ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![eim ζ * (Real.cos θ : ℂ), -Complex.I * epos χ * (Real.sin θ : ℂ);
     -Complex.I * eim χ * (Real.sin θ : ℂ), eim (-ζ) * (Real.cos θ : ℂ)]

/-- The traceless operator `σ̃` such that `u2 = cos Ω·1 − i σ̃` (source
Eq. (23)), written in the ordered basis of the two computational states. -/
def sigmaTilde (θ ζ χ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cos θ : ℂ) * (Real.sin ζ : ℂ), (Real.sin θ : ℂ) * epos χ;
     (Real.sin θ : ℂ) * eim χ, -((Real.cos θ : ℂ) * (Real.sin ζ : ℂ))]

/-- `trace u2 = 2 cos Ω` (source Eq. (37): the eigenvalues of the
phase-factored block `u2` are `e^{±iΩ}`, so the trace is their sum). -/
theorem u2_trace (θ ζ χ : ℝ) :
    Matrix.trace (u2 θ ζ χ) = 2 * (Real.cos (Omega θ ζ) : ℂ) := by
  simp only [u2]
  rw [Matrix.trace_fin_two_of, ← add_mul, eim_add_eim_neg, cos_Omega]
  push_cast; ring

/-- `det u2 = 1`: the block is unimodular, so the eigenvalue product carries no
information beyond the trace (source Eq. (23)). -/
theorem u2_det (θ ζ χ : ℝ) : Matrix.det (u2 θ ζ χ) = 1 := by
  simp only [u2]
  rw [Matrix.det_fin_two_of]
  have h1 : eim ζ * eim (-ζ) = 1 := by rw [eim_add, add_neg_cancel, eim_zero]
  have h2 : epos χ * eim χ = 1 := epos_mul_eim χ
  rw [show (eim ζ * (Real.cos θ : ℂ) * (eim (-ζ) * (Real.cos θ : ℂ))
        - (-Complex.I * epos χ * (Real.sin θ : ℂ)) *
            (-Complex.I * eim χ * (Real.sin θ : ℂ)))
      = (eim ζ * eim (-ζ)) * ((Real.cos θ : ℂ) * (Real.cos θ : ℂ))
        - ((Complex.I * Complex.I) * (epos χ * eim χ)) *
            ((Real.sin θ : ℂ) * (Real.sin θ : ℂ)) by ring]
  rw [h1, h2, Complex.I_mul_I]
  have hsc : ((Real.cos θ : ℂ))^2 + ((Real.sin θ : ℂ))^2 = 1 := by
    have h : (Real.cos θ)^2 + (Real.sin θ)^2 = 1 := by
      nlinarith [Real.sin_sq_add_cos_sq θ]
    have := congrArg (fun x : ℝ => (x : ℂ)) h
    push_cast at this ⊢
    exact this
  simp only [one_mul, mul_one]
  ring_nf
  linear_combination hsc

/-- **The `σ̃` representation (source Eq. (24)):**
`u2 = cos Ω·1 − i σ̃`. -/
theorem u2_repr (θ ζ χ : ℝ) :
    u2 θ ζ χ = (Real.cos (Omega θ ζ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
      - Complex.I • sigmaTilde θ ζ χ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [u2, sigmaTilde, Matrix.smul_apply, Matrix.sub_apply, eim_euler, cos_Omega]
  all_goals ring

/-- Real identity behind `σ̃² = sin²Ω·1`:
`sin²Ω = cos²θ sin²ζ + sin²θ`. -/
lemma sin_sq_Omega (θ ζ : ℝ) :
    Real.sin (Omega θ ζ) ^ 2 = Real.cos θ ^ 2 * Real.sin ζ ^ 2 + Real.sin θ ^ 2 := by
  have hc := cos_Omega θ ζ
  have hs := Real.sin_sq_add_cos_sq (Omega θ ζ)
  have h1 := Real.sin_sq_add_cos_sq ζ
  have h2 := Real.sin_sq_add_cos_sq θ
  rw [hc] at hs
  nlinarith [hs, h1, h2]

/-- `σ̃² = sin²Ω·1` (source Eq. (24)–(25): `σ` is idempotent; the key
identity that turns
`u2` into a rotation of angle `Ω`). -/
theorem sigmaTilde_sq (θ ζ χ : ℝ) :
    sigmaTilde θ ζ χ * sigmaTilde θ ζ χ
      = ((Real.sin (Omega θ ζ)) ^ 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hrc : Complex.cos (θ : ℂ) ^ 2 * Complex.sin (ζ : ℂ) ^ 2
        + Complex.sin (θ : ℂ) ^ 2
      = Complex.sin ((Omega θ ζ : ℝ) : ℂ) ^ 2 := by
    have := congrArg (fun x : ℝ => (x : ℂ)) (sin_sq_Omega θ ζ).symm
    push_cast at this ⊢
    simpa only [Complex.ofReal_cos, Complex.ofReal_sin] using this
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigmaTilde, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]
  · -- (0,0): diagonal
    rw [show Complex.cos (θ : ℂ) * Complex.sin (ζ : ℂ)
            * (Complex.cos (θ : ℂ) * Complex.sin (ζ : ℂ))
          + Complex.sin (θ : ℂ) * epos χ * (Complex.sin (θ : ℂ) * eim χ)
        = Complex.cos (θ : ℂ) * Complex.cos (θ : ℂ)
            * Complex.sin (ζ : ℂ) * Complex.sin (ζ : ℂ)
          + Complex.sin (θ : ℂ) * Complex.sin (θ : ℂ) * (epos χ * eim χ) by ring]
    rw [epos_mul_eim, mul_one]
    linear_combination hrc
  · -- (0,1): off-diagonal = 0
    ring
  · -- (1,0): off-diagonal = 0
    ring
  · -- (1,1): diagonal
    rw [show Complex.sin (θ : ℂ) * eim χ * (Complex.sin (θ : ℂ) * epos χ)
          + Complex.cos (θ : ℂ) * Complex.sin (ζ : ℂ)
              * (Complex.cos (θ : ℂ) * Complex.sin (ζ : ℂ))
        = Complex.cos (θ : ℂ) * Complex.cos (θ : ℂ)
            * Complex.sin (ζ : ℂ) * Complex.sin (ζ : ℂ)
          + Complex.sin (θ : ℂ) * Complex.sin (θ : ℂ) * (eim χ * epos χ) by ring]
    rw [mul_comm (eim χ) (epos χ), epos_mul_eim, mul_one]
    linear_combination hrc

/-! ## The rotation operator `τ` and `n`-fold amplification (Eq. (28)–(29)) -/

/-- The unit rotation generator `τ = (sin Ω)⁻¹ · i σ̃`, so that
`u2 = cos Ω·1 − sin Ω·τ` and `τ² = −1`. -/
def tau (θ ζ χ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((Real.sin (Omega θ ζ) : ℂ))⁻¹ • (Complex.I • sigmaTilde θ ζ χ)

/-- `τ² = −1` (needs `sin Ω ≠ 0`, i.e. a non-degenerate rotation). -/
theorem tau_sq (θ ζ χ : ℝ) (hsin : Real.sin (Omega θ ζ) ≠ 0) :
    tau θ ζ χ * tau θ ζ χ = (-1 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hc : (Real.sin (Omega θ ζ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsin
  have hIS : (Complex.I • sigmaTilde θ ζ χ) * (Complex.I • sigmaTilde θ ζ χ)
      = (-((Real.sin (Omega θ ζ)) ^ 2) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, sigmaTilde_sq, smul_smul,
      Complex.I_mul_I,
      show ((-1 : ℂ) * ((Real.sin (Omega θ ζ)) ^ 2)) = (-((Real.sin (Omega θ ζ)) ^ 2) : ℂ) by
        ring]
  rw [tau, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hIS, smul_smul,
    show ((Real.sin (Omega θ ζ) : ℂ))⁻¹ * ((Real.sin (Omega θ ζ) : ℂ))⁻¹
          * (-((Real.sin (Omega θ ζ)) ^ 2)) = -1 by
      have hs : (((Real.sin (Omega θ ζ) : ℂ)))⁻¹ * ((Real.sin (Omega θ ζ) : ℂ))
          = 1 := by
        rw [mul_comm]
        exact mul_inv_cancel₀ hc
      calc ((Real.sin (Omega θ ζ) : ℂ))⁻¹ * ((Real.sin (Omega θ ζ) : ℂ))⁻¹
              * (-((Real.sin (Omega θ ζ)) ^ 2))
            = -((((Real.sin (Omega θ ζ) : ℂ))⁻¹ * ((Real.sin (Omega θ ζ) : ℂ)))
                * (((Real.sin (Omega θ ζ) : ℂ))⁻¹ * ((Real.sin (Omega θ ζ) : ℂ)))) := by ring
        _ = -(1 * 1) := by rw [hs]
        _ = -1 := by norm_num]

/-- `u2 = cos Ω·1 − sin Ω·τ` (source Eq. (28)). -/
theorem u2_eq_cos_sin (θ ζ χ : ℝ) (hsin : Real.sin (Omega θ ζ) ≠ 0) :
    u2 θ ζ χ = (Real.cos (Omega θ ζ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
      - (Real.sin (Omega θ ζ) : ℂ) • tau θ ζ χ := by
  have hc : (Real.sin (Omega θ ζ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsin
  rw [u2_repr θ ζ χ, tau]
  rw [smul_smul]
  rw [show (Real.sin (Omega θ ζ) : ℂ) * ((Real.sin (Omega θ ζ) : ℂ))⁻¹ = 1 by
    exact mul_inv_cancel₀ hc]
  rw [one_smul]

/-- **Multiplication of rotations.** `(cos a·1 − sin a·τ)(cos b·1 − sin b·τ)
= cos(a+b)·1 − sin(a+b)·τ` for `τ² = −1`. -/
theorem rot_mul {τ : Matrix (Fin 2) (Fin 2) ℂ}
    (hτ : τ * τ = (-1 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) (a b : ℝ) :
    ((Real.cos a : ℂ) • 1 - (Real.sin a : ℂ) • τ) *
        ((Real.cos b : ℂ) • 1 - (Real.sin b : ℂ) • τ)
      = (Real.cos (a + b) : ℂ) • 1 - (Real.sin (a + b) : ℂ) • τ := by
  have e1 : ((Real.cos a : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
      ((Real.cos b : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))
      = ((Real.cos a : ℂ) * (Real.cos b : ℂ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [Matrix.smul_mul, Matrix.one_mul, smul_smul]
  have e2 : ((Real.cos a : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
      ((Real.sin b : ℂ) • τ) = ((Real.cos a : ℂ) * (Real.sin b : ℂ)) • τ := by
    rw [Matrix.smul_mul, Matrix.one_mul, smul_smul]
  have e3 : ((Real.sin a : ℂ) • τ) *
      ((Real.cos b : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))
      = ((Real.sin a : ℂ) * (Real.cos b : ℂ)) • τ := by
    rw [Matrix.mul_smul, Matrix.mul_one, smul_smul,
      mul_comm (Real.cos b : ℂ) (Real.sin a : ℂ)]
  have e4 : ((Real.sin a : ℂ) • τ) * ((Real.sin b : ℂ) • τ)
      = (-((Real.sin a : ℂ) * (Real.sin b : ℂ))) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hτ, smul_smul, smul_smul, mul_neg, mul_one]
  rw [sub_mul, mul_sub, mul_sub, e1, e2, e3, e4, Real.cos_add, Real.sin_add]
  push_cast
  module

/-- **`n`-fold amplification of the rotation (source Eq. (29)).**  Repeating a
rotation of angle `Ω` exactly `n` times gives a rotation of angle `nΩ`.  This
is the algebraic statement that small parameter errors are multiplied by `n`. -/
theorem pow_rot {τ : Matrix (Fin 2) (Fin 2) ℂ}
    (hτ : τ * τ = (-1 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) (Ω : ℝ) :
    ∀ n : ℕ, ((Real.cos Ω : ℂ) • 1 - (Real.sin Ω : ℂ) • τ) ^ n
      = (Real.cos ((n : ℝ) * Ω) : ℂ) • 1 - (Real.sin ((n : ℝ) * Ω) : ℂ) • τ := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih, rot_mul hτ ((n : ℝ) * Ω) Ω,
        show (n : ℝ) * Ω + Ω = ((n + 1 : ℕ) : ℝ) * Ω by push_cast; ring]

/-- **The concrete amplification for the cycle's entangling block.**  The
`n`-fold repetition of `u2` is a rotation of angle `nΩ`,
`u2ⁿ = cos(nΩ)·1 − sin(nΩ)·τ` (source Eq. (29) for the actual gate). -/
theorem u2_pow (θ ζ χ : ℝ) (hsin : Real.sin (Omega θ ζ) ≠ 0) (n : ℕ) :
    (u2 θ ζ χ) ^ n
      = (Real.cos ((n : ℝ) * Omega θ ζ) : ℂ) • 1
        - (Real.sin ((n : ℝ) * Omega θ ζ) : ℂ) • tau θ ζ χ := by
  rw [u2_eq_cos_sin θ ζ χ hsin]
  exact pow_rot (tau_sq θ ζ χ hsin) (Omega θ ζ) n

/-! ## Main theorem: eigenvalue read-out and `n`-fold amplification -/

/-- **Floquet calibration: eigenvalue determination and `n`-fold amplification
(arXiv:2010.07965 Supplemental §C, Eq. (23), (24), (25), (28), (29), (37), (38)).**

For the cycle's entangling block `u2` at gate parameters `(θ, ζ, χ)`:

1. the Rabi angle satisfies the robust bounds `θ ≤ Ω ≤ π − θ`
   (Eq. (38));
2. the eigenvalues of `u2` are recovered from `trace u2 = 2 cos Ω` and
   `det u2 = 1` (Eq. (37)); hence the cycle eigenvalues determine the gate
   angle `Ω`;
3. repeating the block `n` times amplifies the angle `n`-fold,
   `u2ⁿ = cos(nΩ)·1 − sin(nΩ)·τ` with `τ² = −1` (Eq. (28)–(29)).

The uniqueness of the full gate from a finite set of single-qubit probe
rotations and the robustness to SPAM errors (the empirical parts of claim
`c002`) are described in the paper's Supplement and are not formalised here. -/
theorem floquet_calibration (θ ζ χ : ℝ) (hθ0 : 0 ≤ θ) (hθ2 : θ ≤ Real.pi / 2)
    (hsin : Real.sin (Omega θ ζ) ≠ 0) :
    (θ ≤ Omega θ ζ ∧ Omega θ ζ ≤ Real.pi - θ) ∧
      Matrix.trace (u2 θ ζ χ) = 2 * (Real.cos (Omega θ ζ) : ℂ) ∧
      Matrix.det (u2 θ ζ χ) = 1 ∧
      (tau θ ζ χ * tau θ ζ χ = (-1 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) ∧
      (∀ n : ℕ, (u2 θ ζ χ) ^ n
        = (Real.cos ((n : ℝ) * Omega θ ζ) : ℂ) • 1
          - (Real.sin ((n : ℝ) * Omega θ ζ) : ℂ) • tau θ ζ χ) :=
  ⟨rabi_bounds ζ hθ0 hθ2,
    u2_trace θ ζ χ,
    u2_det θ ζ χ,
    tau_sq θ ζ χ hsin,
    u2_pow θ ζ χ hsin⟩

end Qatlib.Papers.FermiHubbard20.MainResults
