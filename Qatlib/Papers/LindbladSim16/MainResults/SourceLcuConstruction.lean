/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit

set_option backward.isDefEq.respectTransparency false

/-!
# Linear Combination of Unitaries for Completely Positive Maps

This module formalizes Lemma 1 of Cleve and Wang: given Kraus operators
`A₀, …, A_{m-1}` of a trace-preserving completely positive map, each implemented
up to scale `s_j > 0` by a per-jump LCU unitary `W`, applying `W` to the
purifier-weighted input state `|0⟩|μ⟩|ψ⟩` produces the coherent state
`√p |0⟩ (∑_j |j⟩ A_j |ψ⟩) + √(1 - p) |Φ⊥⟩` with `p = 1 / ∑_j s_j²` and a
normalized orthogonal remainder `|Φ⊥⟩` supported outside the indicator-`0`
subspace.

## Main statements

* `lcuInit_eq_sum`: linear decomposition of the purifier-superposition input state.
* `lcuGood_eq_sum`: decomposition of the indicator-`0` output component into per-jump
  success branches.
* `source_lemma1`: full LCU output decomposition and normalization of `|Φ⊥⟩`.

## References

* [Cleve and Wang, 2017][CleveWang2017Lindblad], Section 3, Lemma 1, Eqs. (24)--(34).
-/

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.LindbladSim16.MainResults

open scoped ComplexOrder

/-- The joint register `indicator ⊗ purifier ⊗ system` of the LCU construction. -/
abbrev SimReg (m d : ℕ) : Type := Bool × Fin m × Fin d

/-- `|0⟩|μ⟩|ψ⟩`: the input state with indicator `0`, purifier amplitudes `μ`,
and system state `ψ`. -/
def lcuInit {m d : ℕ} (μ : Fin m → ℂ) (ψ : QState (Fin d)) : QState (SimReg m d) :=
  fun x => if x.1 = false then μ x.2.1 * ψ x.2.2 else 0

/-- `|0⟩|j⟩|ψ⟩` for a fixed purifier index `j`. -/
def lcuBasis {m d : ℕ} (j : Fin m) (ψ : QState (Fin d)) : QState (SimReg m d) :=
  fun x => if x.1 = false ∧ x.2.1 = j then ψ x.2.2 else 0

/-- `|0⟩|j⟩(A_j|ψ⟩)`: the `j`-th LCU success branch. -/
def lcuStep {m d : ℕ} (A : Fin m → Matrix (Fin d) (Fin d) ℂ) (j : Fin m)
    (ψ : QState (Fin d)) : QState (SimReg m d) :=
  fun x => if x.1 = false ∧ x.2.1 = j then (A j *ᵥ ψ) x.2.2 else 0

/-- `∑_j |0⟩|j⟩(A_j|ψ⟩)`: the indicator-`0` component of the output. -/
def lcuGood {m d : ℕ} (A : Fin m → Matrix (Fin d) (Fin d) ℂ) (ψ : QState (Fin d)) :
    QState (SimReg m d) :=
  fun x => if x.1 = false then (A x.2.1 *ᵥ ψ) x.2.2 else 0

/-- Support outside the indicator-`0` subspace. -/
def IndZero {m d : ℕ} (Φ : QState (SimReg m d)) : Prop := ∀ x, x.1 = false → Φ x = 0

/-- The purifier-superposition input is a linear combination of the per-index basis states. -/
theorem lcuInit_eq_sum {m d : ℕ} (μ : Fin m → ℂ) (ψ : QState (Fin d)) :
    lcuInit μ ψ = ∑ j, μ j • lcuBasis j ψ := by
  funext x
  simp only [lcuInit, lcuBasis, Finset.sum_apply, Pi.smul_apply]
  by_cases hx : x.1 = false <;> simp [hx, smul_eq_mul]

/-- The indicator-`0` output component is the sum of the per-index success branches. -/
theorem lcuGood_eq_sum {m d : ℕ} (A : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (ψ : QState (Fin d)) :
    lcuGood A ψ = ∑ j, lcuStep A j ψ := by
  funext x
  simp only [lcuGood, lcuStep, Finset.sum_apply]
  by_cases hx : x.1 = false <;> simp [hx]

/-- Support outside indicator `0` is preserved under scalar multiplication. -/
theorem IndZero.smul {m d : ℕ} {Φ : QState (SimReg m d)} (h : IndZero Φ) (c : ℂ) :
    IndZero (c • Φ) := by
  intro x hx
  simp only [Pi.smul_apply, h x hx, smul_zero]

/-- Support outside indicator `0` is preserved under finite sums. -/
theorem IndZero.sum {m d : ℕ} {ι : Type*} [Fintype ι] (F : ι → QState (SimReg m d))
    (h : ∀ i, IndZero (F i)) : IndZero (∑ i, F i) := by
  intro x hx
  simp only [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  exact h i x hx

/-- **Lemma 1**: applying the LCU unitary `W` to `|0⟩|μ⟩|ψ⟩` with purifier weights
`μ_j = s_j √p` (`p = 1 / ∑_j s_j²`) produces `√p lcuGood A ψ + √(1 - p) Φ` with
`Φ` normalized and supported outside indicator `0`. -/
theorem source_lemma1
    (m d : ℕ) (A : Fin m → Matrix (Fin d) (Fin d) ℂ) (s : Fin m → ℝ)
    (hs : ∀ j, 0 < s j)
    (W : Matrix (SimReg m d) (SimReg m d) ℂ)
    (hW : W ∈ Matrix.unitaryGroup (SimReg m d) ℂ)
    (hstep : ∀ (j : Fin m) (ψ' : QState (Fin d)),
        ∃ r : QState (SimReg m d), IndZero r ∧
          W *ᵥ lcuBasis j ψ' = ((s j : ℂ))⁻¹ • lcuStep A j ψ' + r)
    (hTP : ∀ ψ' : QState (Fin d), Normalized ψ' →
        ∑ j, ∑ i, ‖(A j *ᵥ ψ') i‖ ^ 2 = 1)
    (ψ : QState (Fin d)) (hψ : Normalized ψ)
    (hp : 0 < 1 / ∑ j, (s j) ^ 2) (hp1 : 1 / ∑ j, (s j) ^ 2 < 1) :
    ∃ (Φ : QState (SimReg m d)),
      IndZero Φ ∧ Normalized Φ ∧
      W *ᵥ lcuInit (fun j => (s j : ℂ) * (((Real.sqrt (1 / ∑ j, (s j) ^ 2) : ℝ)) : ℂ)) ψ
        = (((Real.sqrt (1 / ∑ j, (s j) ^ 2) : ℝ)) : ℂ) • lcuGood A ψ
          + (((Real.sqrt (1 - 1 / ∑ j, (s j) ^ 2) : ℝ)) : ℂ) • Φ := by
  refine (And.left (b := _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
    ⟨?_, ⟨hs, hW, hstep, hTP, hψ, hp, hp1⟩⟩)
  classical
  let S : ℝ := ∑ j, (s j) ^ 2
  let p : ℝ := 1 / S
  have hp_pos : 0 < p := hp
  have hp_lt : p < 1 := hp1
  have hS_pos : 0 < S := one_div_pos.mp hp_pos
  have hSp : S * p = 1 := mul_one_div_cancel hS_pos.ne'
  have hrest_pos : 0 < 1 - p := sub_pos.mpr hp_lt
  let μ : Fin m → ℂ := fun j => (s j : ℂ) * (Real.sqrt p : ℂ)
  choose r hr_ind hr_eq using fun j => hstep j ψ
  let R : QState (SimReg m d) := ∑ j, μ j • r j
  have hR_ind : IndZero R := IndZero.sum _ fun j => (hr_ind j).smul (μ j)
  have hμ_cancel (j : Fin m) : μ j * (s j : ℂ)⁻¹ = (Real.sqrt p : ℂ) := by
    have hsj : (s j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hs j).ne'
    dsimp [μ]
    rw [mul_right_comm, mul_inv_cancel₀ hsj, one_mul]
  have hout : W *ᵥ lcuInit μ ψ = (Real.sqrt p : ℂ) • lcuGood A ψ + R := by
    rw [lcuInit_eq_sum, Matrix.mulVec_sum]
    simp_rw [Matrix.mulVec_smul, hr_eq, smul_add, smul_smul, hμ_cancel]
    rw [Finset.sum_add_distrib, ← Finset.smul_sum, ← lcuGood_eq_sum]
  have hsqrt_norm : ‖(Real.sqrt p : ℂ)‖ ^ 2 = p := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hp_pos.le]
  have hμ_norm (j : Fin m) : ‖μ j‖ ^ 2 = (s j) ^ 2 * p := by
    dsimp [μ]
    rw [norm_mul, mul_pow, hsqrt_norm, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hψ_sum : ∑ i, ‖ψ i‖ ^ 2 = 1 := hψ
  have hinit_norm : Normalized (lcuInit μ ψ) := by
    change (∑ x : Bool × Fin m × Fin d, ‖lcuInit μ ψ x‖ ^ 2) = 1
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, lcuInit, Bool.true_eq_false,
      ↓reduceIte, norm_zero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, zero_add]
    simp_rw [norm_mul, mul_pow, ← Finset.mul_sum, hψ_sum, mul_one, hμ_norm]
    rw [← Finset.sum_mul]
    exact hSp
  have hout_norm : Normalized ((Real.sqrt p : ℂ) • lcuGood A ψ + R) := by
    rw [← hout]
    exact normalized_applyGate hW hinit_norm
  have hnorm_split :
      (∑ x, ‖((Real.sqrt p : ℂ) • lcuGood A ψ + R) x‖ ^ 2) =
        p * (∑ j, ∑ i, ‖(A j *ᵥ ψ) i‖ ^ 2) + ∑ x, ‖R x‖ ^ 2 := by
    have hpoint (x : SimReg m d) :
        ‖((Real.sqrt p : ℂ) • lcuGood A ψ + R) x‖ ^ 2 =
          p * ‖lcuGood A ψ x‖ ^ 2 + ‖R x‖ ^ 2 := by
      obtain ⟨b, j, i⟩ := x
      cases b with
      | false =>
          rw [Pi.add_apply, hR_ind (false, j, i) rfl, add_zero, Pi.smul_apply,
            smul_eq_mul, norm_mul, mul_pow, hsqrt_norm, norm_zero, zero_pow (by decide),
            add_zero]
      | true => simp [lcuGood]
    simp_rw [hpoint]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    congr 1
    congr 1
    simp [Fintype.sum_prod_type, lcuGood]
  have hR_norm : ∑ x, ‖R x‖ ^ 2 = 1 - p := by
    have hsum : p + ∑ x, ‖R x‖ ^ 2 = 1 := by
      simpa only [hTP ψ hψ, mul_one] using hnorm_split.symm.trans hout_norm
    exact eq_sub_of_add_eq' hsum
  have hsqrt_rest_ne : (Real.sqrt (1 - p) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos_of_pos hrest_pos).ne'
  let Φ : QState (SimReg m d) := (Real.sqrt (1 - p) : ℂ)⁻¹ • R
  have hΦ_norm : Normalized Φ := by
    change (∑ x, ‖(Real.sqrt (1 - p) : ℂ)⁻¹ * R x‖ ^ 2) = 1
    simp_rw [norm_mul, mul_pow, ← Finset.mul_sum]
    rw [hR_norm, norm_inv, inv_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt hrest_pos.le, inv_mul_cancel₀ hrest_pos.ne']
  refine ⟨Φ, hR_ind.smul _, hΦ_norm, ?_⟩
  change W *ᵥ lcuInit μ ψ = (Real.sqrt p : ℂ) • lcuGood A ψ +
    (Real.sqrt (1 - p) : ℂ) • Φ
  rw [hout, show (Real.sqrt (1 - p) : ℂ) • Φ = R by
    change (Real.sqrt (1 - p) : ℂ) • ((Real.sqrt (1 - p) : ℂ)⁻¹ • R) = R
    rw [smul_smul, mul_inv_cancel₀ hsqrt_rest_ne, one_smul]]

end Qatlib.Papers.LindbladSim16.MainResults
