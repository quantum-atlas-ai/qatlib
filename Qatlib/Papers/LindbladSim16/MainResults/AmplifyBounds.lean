/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.PureStateMath.Qubit
public import Mathlib.Tactic

@[expose] public section


/-! A conditional implication from an operator error bound to a reduced-state bound. -/

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.LindbladSim16.MainResults

open scoped ComplexOrder

/-- The Euclidean 2-norm of a state vector, `‖v‖ = √(Σ_i ‖v i‖²)`. -/
noncomputable def vecNorm {I : Type*} [Fintype I] (v : QState I) : ℝ :=
  Real.sqrt (∑ i, ‖v i‖ ^ 2)

/-- The reflection `2P - I`. -/
def reflection {I : Type*} [DecidableEq I] (P : Matrix I I ℂ) : Matrix I I ℂ :=
  2 • P - 1

/-- Eq. (85): the oblivious amplitude amplification operator
`F = -Ŵ (2P₁ - I) Ŵ† (2P₀ - I) Ŵ` (reflection signs immaterial to the norm). -/
def obliviousAmpOp {I : Type*} [Fintype I] [DecidableEq I] (P₀ P₁ : Matrix I I ℂ)
    (Ŵ : Matrix I I ℂ) : Matrix I I ℂ :=
  -(Ŵ * reflection P₁ * Ŵᴴ * reflection P₀ * Ŵ)

/-- The system-register reduction `(⟨κ| ⊗ I)|v⟩`. -/
noncomputable def redSys {J : Type*} [Fintype J] {d : ℕ} (κ : QState J)
    (v : QState (J × Fin d)) : QState (Fin d) :=
  fun i => ∑ j, starRingEnd ℂ (κ j) * v (j, i)

/-- Scaling a vector scales its Euclidean norm by the modulus of the scalar. -/
theorem vecNorm_smul {I : Type*} [Fintype I] (c : ℂ) (v : QState I) :
    vecNorm (c • v) = ‖c‖ * vecNorm v := by
  unfold vecNorm
  have hsum : ∑ i, ‖(c • v) i‖ ^ 2 = ‖c‖ ^ 2 * ∑ i, ‖v i‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
  rw [hsum, Real.sqrt_mul (sq_nonneg ‖c‖), Real.sqrt_sq (norm_nonneg c)]

/-! ## Lemma 3 -/

/-- **Lemma 3 of Cleve–Wang (arXiv:1612.09512v3, §5 pp. 15–16, Eq. (95)).**

With `Ŵ|Ψ⊥⟩ = (√3/2)|Φ⟩ - (1/2)|Φ⊥⟩` (Eq. (86)) and the amplification operator
`Q = (1/4)·I + O(1/r)` in operator norm (Eq. (89), obtained in the paper from
Eq. (88) and the normalisation bound Eq. (81)), together with the paper's identity
Eq. (93) `Q|ψ⟩ = (1/4)|ψ⟩ + (√3/4)(⟨κ|⊗I)|Ψ⊥(ψ)⟩`, the system-register reduction
`(⟨κ|⊗I)|Ψ⊥⟩` — i.e. `P₁|Ψ⊥⟩` — is `O(1/r)`.

This is the paper's final derivation (93)+(94)⇒(95), mechanised below.  The remaining
open obligation is exactly the paper's Eqs. (88)–(93): deriving the operator bound
(89) from (88)/(81) and the identity (93) from (90)–(92). -/
theorem source_lemma3
    (r : ℕ) (hr : 2 ≤ r) {J : Type*} [Fintype J] {d : ℕ}
    (κ : QState J) (Qm : Matrix (Fin d) (Fin d) ℂ)
    (Ψperp : QState (Fin d) → QState (J × Fin d))
    -- Eq. (89): `Q = (1/4)·I + O(1/r)` in operator norm.
    (hQ : ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ v : QState (Fin d),
        vecNorm ((Qm - (1 / 4 : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) *ᵥ v)
          ≤ C₀ * vecNorm v / (r : ℝ))
    -- Eq. (93): `Q|ψ⟩ = (1/4)|ψ⟩ + (√3/4)(⟨κ|⊗I)|Ψ⊥(ψ)⟩`.
    (h93 : ∀ ψ : QState (Fin d),
        Qm *ᵥ ψ
          = (1 / 4 : ℂ) • ψ + (((Real.sqrt 3 / 4 : ℝ)) : ℂ) • redSys κ (Ψperp ψ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ ψ : QState (Fin d), vecNorm ψ = 1 →
      vecNorm (redSys κ (Ψperp ψ)) ≤ C / (r : ℝ) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := hQ
  have hrpos : (0 : ℝ) < (r : ℝ) := by
    have : 0 < r := by omega
    exact_mod_cast this
  have hcoef : ‖(((Real.sqrt 3 / 4 : ℝ)) : ℂ)‖ = Real.sqrt 3 / 4 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hcoefpos : (0 : ℝ) < Real.sqrt 3 / 4 := by positivity
  refine ⟨C₀ * (Real.sqrt 3 / 4)⁻¹ + 1, by positivity, ?_⟩
  intro ψ hψ
  -- Substitute Eq. (93) into the operator bound of Eq. (89).
  have hsub : (Qm - (1 / 4 : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) *ᵥ ψ
      = (((Real.sqrt 3 / 4 : ℝ)) : ℂ) • redSys κ (Ψperp ψ) := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, h93 ψ,
      add_sub_cancel_left]
  have hb := hC₀ ψ
  rw [hsub, vecNorm_smul, hcoef, hψ, mul_one] at hb
  -- `hb : (√3/4) * ‖redSys‖ ≤ C₀ / r`.
  have step : vecNorm (redSys κ (Ψperp ψ)) ≤ (Real.sqrt 3 / 4)⁻¹ * (C₀ / (r : ℝ)) := by
    calc vecNorm (redSys κ (Ψperp ψ))
        = (Real.sqrt 3 / 4)⁻¹ * ((Real.sqrt 3 / 4) * vecNorm (redSys κ (Ψperp ψ))) := by
          rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hcoefpos), one_mul]
      _ ≤ (Real.sqrt 3 / 4)⁻¹ * (C₀ / (r : ℝ)) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
  have step2 : (Real.sqrt 3 / 4)⁻¹ * (C₀ / (r : ℝ)) = C₀ * (Real.sqrt 3 / 4)⁻¹ / (r : ℝ) := by
    ring
  have step3 : C₀ * (Real.sqrt 3 / 4)⁻¹ / (r : ℝ)
      ≤ (C₀ * (Real.sqrt 3 / 4)⁻¹ + 1) / (r : ℝ) := by
    gcongr
    linarith
  have step' : vecNorm (redSys κ (Ψperp ψ)) ≤ C₀ * (Real.sqrt 3 / 4)⁻¹ / (r : ℝ) := by
    rw [← step2]; exact step
  linarith [step', step3]

end Qatlib.Papers.LindbladSim16.MainResults
