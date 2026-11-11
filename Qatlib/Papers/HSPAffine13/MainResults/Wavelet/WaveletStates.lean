/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HSPAffine13.MainResults.AffineModel.AffineGroup
import Mathlib.NumberTheory.MulChar.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# The wavelet states of Lemma 2

The paper builds the `(q - 1)`-dimensional representation `π₀` on the
sum-zero functions `L₀²(F)`.  In the multiplicative-character model used here,
the wavelet family is

```
φ_{χ, v}(x) = (1 / sqrt (q - 1)) * χ (x - v),
ψ_v(x)      = (1 / sqrt q) * (φ_{1, v}(x) - sqrt (q - 1) * δ_v(x)),
```

where `χ` is a multiplicative character of `F` and `δ_v` is the delta function
at `v`.  This is the paper's `φ_{k, v}` with `χ = χ_u^{-k}` together with the
special sum-zero vector `ψ_v`.

The action of `c = (u, b)` on functions is
`(π(c) f)(x) = f ((x - b) / u)`.  We prove the two forward eigenvector
identities of Lemma 2:

* `π(c) φ_{χ, v} = χ(u⁻¹) • φ_{χ, v}` when `b + u v = v`;
* `π(c) ψ_v = ψ_v` when `v = b / (1 - u)`;

and the Born probability `‖ψ_v(v)‖² = (q - 1) / q` of the paper's final
sentence.  The classification of all eigenvectors (the converse direction of
Lemma 2) is not included in this module.
-/

set_option autoImplicit false

namespace Qatlib.Papers.HSPAffine13.MainResults

open AffineGroup

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The normalization `1 / sqrt (q - 1)` of the wavelet family. -/
noncomputable def waveletNorm (F : Type*) [Field F] [Fintype F] : ℂ :=
  (((Real.sqrt ((Fintype.card F - 1 : ℕ) : ℝ) : ℝ) : ℂ))⁻¹

/-- The normalization `1 / sqrt q` of the vector `ψ`. -/
noncomputable def psiNorm (F : Type*) [Field F] [Fintype F] : ℂ :=
  (((Real.sqrt (Fintype.card F : ℝ) : ℝ) : ℂ))⁻¹

/-- The unnormalized factor `sqrt (q - 1)` appearing in `ψ`. -/
noncomputable def waveletScale (F : Type*) [Field F] [Fintype F] : ℂ :=
  ((Real.sqrt ((Fintype.card F - 1 : ℕ) : ℝ) : ℝ) : ℂ)

/-- The delta function at `v`. -/
noncomputable def delta (v : F) : F → ℂ := fun x => if x = v then 1 else 0

/-- The paper's wavelet `φ_{χ, v}(x) = (1 / sqrt (q - 1)) * χ (x - v)`. -/
noncomputable def phi (χ : MulChar F ℂ) (v : F) : F → ℂ :=
  fun x => waveletNorm F * χ (x - v)

/-- The paper's special sum-zero wavelet `ψ_v`. -/
noncomputable def psi (v : F) : F → ℂ :=
  psiNorm F • (phi (1 : MulChar F ℂ) v - waveletScale F • delta v)

/-- The representation action `(π(u, b) f)(x) = f ((x - b) / u)`. -/
noncomputable def pi0 (u : Fˣ) (b : F) (f : F → ℂ) : F → ℂ :=
  fun x => f ((x - b) / (u : F))

omit [Fintype F] [DecidableEq F] in
/-- The action `π(u, b)` is additive. -/
@[simp]
theorem pi0_add (u : Fˣ) (b : F) (f g : F → ℂ) :
    pi0 u b (f + g) = pi0 u b f + pi0 u b g := rfl

omit [Fintype F] [DecidableEq F] in
/-- The action `π(u, b)` preserves subtraction. -/
@[simp]
theorem pi0_sub (u : Fˣ) (b : F) (f g : F → ℂ) :
    pi0 u b (f - g) = pi0 u b f - pi0 u b g := rfl

omit [Fintype F] [DecidableEq F] in
/-- The action `π(u, b)` is complex-linear. -/
@[simp]
theorem pi0_smul (u : Fˣ) (b : F) (c : ℂ) (f : F → ℂ) :
    pi0 u b (c • f) = c • pi0 u b f := rfl

omit [Fintype F] [DecidableEq F] in
/-- The shifted argument identity behind the eigenvector computation. -/
theorem pi0_phi_argument (u : Fˣ) (b : F) (v : F) (hv : b + (u : F) * v = v)
    (x : F) :
    (x - b) / (u : F) - v = ((u⁻¹ : Fˣ) : F) * (x - v) := by
  have hu0 : (u : F) ≠ 0 := u.ne_zero
  have hnum : x - b - (u : F) * v = x - v := by
    calc
      x - b - (u : F) * v = x - (b + (u : F) * v) := by ring
      _ = x - v := by rw [hv]
  calc
    (x - b) / (u : F) - v = (x - b - (u : F) * v) / (u : F) := by
      field_simp [hu0]
    _ = (x - v) / (u : F) := by rw [hnum]
    _ = ((u⁻¹ : Fˣ) : F) * (x - v) := by
      rw [div_eq_mul_inv]
      simp [mul_comm]

omit [DecidableEq F] in
/-- **Lemma 2, eigenvector identity.**  If `b + u v = v`, then `φ_{χ, v}` is
an eigenvector of `π(u, b)` with eigenvalue `χ(u⁻¹)`. -/
theorem pi0_phi_eq_smul (χ : MulChar F ℂ) (u : Fˣ) (b : F) (v : F)
    (hv : b + (u : F) * v = v) :
    pi0 u b (phi χ v) = χ ((u⁻¹ : Fˣ) : F) • phi χ v := by
  ext x
  simp only [pi0, phi, Pi.smul_apply]
  rw [pi0_phi_argument u b v hv x, map_mul]
  ring

omit [Fintype F] [DecidableEq F] in
/-- The fixed-point condition `b + u v = v` is equivalent to
`v = b / (1 - u)` when `u ≠ 1`. -/
theorem fixedPoint_eq_div (u : Fˣ) (b : F) (hu : (u : F) ≠ 1) :
    b + (u : F) * (b / (1 - (u : F))) = b / (1 - (u : F)) := by
  have hden : 1 - (u : F) ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  field_simp [hden]
  ring

omit [Fintype F] in
/-- The delta function is fixed by `π(u, b)` at the fixed point `v`. -/
theorem pi0_delta_fixed (u : Fˣ) (b : F) (v : F) (hv : b + (u : F) * v = v) :
    pi0 u b (delta v) = delta v := by
  ext x
  simp only [pi0, delta]
  have hu0 : (u : F) ≠ 0 := u.ne_zero
  have hiff : (x - b) / (u : F) = v ↔ x = v := by
    rw [div_eq_iff hu0]
    constructor
    · intro h
      rw [mul_comm] at h
      linear_combination h + hv
    · intro h
      subst h
      have hx : (u : F) * x = x - b := by
        calc
          (u : F) * x = (b + (u : F) * x) - b := by ring
          _ = x - b := by rw [hv]
      rw [← hx, mul_comm]
  simp [hiff]

/-- **Lemma 2, fixed-point identity.**  For `c = (u, b)` and
`v = b / (1 - u)`, the vector `ψ_v` is fixed by `π(c)`. -/
theorem pi0_psi_fixed (u : Fˣ) (b : F) (hu : (u : F) ≠ 1) :
    pi0 u b (psi (b / (1 - (u : F)))) = psi (b / (1 - (u : F))) := by
  set v : F := b / (1 - (u : F)) with hvdef
  have hv : b + (u : F) * v = v := fixedPoint_eq_div u b hu
  have hphi : pi0 u b (phi (1 : MulChar F ℂ) v) = phi (1 : MulChar F ℂ) v := by
    have h := pi0_phi_eq_smul (1 : MulChar F ℂ) u b v hv
    rw [show (1 : MulChar F ℂ) ((u⁻¹ : Fˣ) : F) = 1 by
      exact MulChar.one_apply_coe (u⁻¹)] at h
    simpa using h
  have hdelta : pi0 u b (delta v) = delta v := pi0_delta_fixed u b v hv
  simp only [psi, pi0_smul, pi0_sub, hphi, hdelta]

/-- The value of `ψ_v` at `v` is `-sqrt (q - 1) / sqrt q`. -/
theorem psi_apply_self (v : F) :
    psi v v = -(psiNorm F * waveletScale F) := by
  simp [psi, phi, delta, MulChar.map_zero, mul_comm]

/-- **Lemma 2, Born probability.**  Measuring `ψ_v` in the computational basis
collapses to `|v>` with probability `(q - 1) / q`. -/
theorem psi_born_at_self (v : F) :
    Complex.normSq (psi v v) = ((Fintype.card F - 1 : ℕ) : ℝ) / (Fintype.card F : ℝ) := by
  rw [psi_apply_self, Complex.normSq_neg, Complex.normSq_mul]
  have hqpos : (0 : ℝ) < (Fintype.card F : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hq1 : (0 : ℝ) ≤ ((Fintype.card F - 1 : ℕ) : ℝ) := by positivity
  simp only [psiNorm, waveletScale, Complex.normSq_inv, Complex.normSq_ofReal]
  rw [Real.mul_self_sqrt hqpos.le, Real.mul_self_sqrt hq1]
  field_simp [hqpos.ne']

end Qatlib.Papers.HSPAffine13.MainResults
