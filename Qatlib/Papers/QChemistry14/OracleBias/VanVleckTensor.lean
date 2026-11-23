/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QChemistry14.OracleBias.TwoLevelSystem

@[expose] public section

/-!
# Tensor-product Van Vleck model on `EuclideanSpace`

This module lifts the single-subsystem two-level model to the tensor tower of `N`
identical, non-interacting subsystems, giving normalized tensor product states,
per-subsystem Hamiltonians, and factorized overlaps behind Eqs. (47)-(54) of
[McCleanEtAl2014]. It proves the corrected amplitude/probability distinction of Eq. (54)
(the `N`-fold amplitude is `|Δ| ^ N`, the Born probability `|Δ| ^ (2N)`), the bias
identity of Eq. (53), and the exponential decay of the Born probability (equivalently the
exponential growth of its reciprocal) in the subsystem count. The reciprocal models the
mean number of independent repetitions until an ideal ground-state projection succeeds.

## Main statements

* `inner_prodTrial_prodGround`: the `N`-fold overlap amplitude equals `Δ ^ N`.
* `qpe_ground_amplitude` and `qpe_ground_born`: the absolute amplitude is `|Δ| ^ N` and
  the Born probability is `|Δ| ^ (2N)`.
* `tower_energy`: the trial energy equals `N * (Δ^2 * Eg + (1 - Δ^2) * Ee)`.
* `sumHam_apply_prodGround`: the product of ground states has eigenvalue `N * Eg`.
* `tower_bias`: the bias equals `N * (1 - Δ^2) * (Ee - Eg)`.
* `bornProb_exponential_decay` and `repetition_growth`: uniform positive constants
  governing the exponential decay of the Born probability and the exponential growth of
  the repetition cost.

## References

* [McClean et al., 2014][McCleanEtAl2014]
-/

namespace Qatlib.Papers.QChemistry14.OracleBias

open scoped TensorProduct InnerProductSpace

noncomputable section

/-- A type bundled with its normed additive group and complex inner product space
structure, used to carry the canonical inner product through the tensor tower. -/
structure IpsType where
  carrier : Type
  nacg : NormedAddCommGroup carrier
  ips : InnerProductSpace ℂ carrier

/-- The bundled normed additive group structure is available on the carrier. -/
instance (w : IpsType) : NormedAddCommGroup w.carrier := w.nacg
/-- The bundled complex inner product space structure is available on the carrier. -/
instance (w : IpsType) : InnerProductSpace ℂ w.carrier := w.ips

/-- The tensor tower of `n` copies of the two-dimensional subsystem space, with its inner
product structure bundled. -/
@[reducible] noncomputable def towerW : ℕ → IpsType
  | 0 => ⟨ℂ, inferInstance, inferInstance⟩
  | n + 1 =>
      ⟨(towerW n).carrier ⊗[ℂ] EuclideanSpace ℂ (Fin 2),
        TensorProduct.instNormedAddCommGroup, TensorProduct.instInnerProductSpace⟩

/-- The `n`-subsystem tensor tower `ℂ^(2^n)` with its canonical inner product structure. -/
@[reducible] noncomputable def tower (n : ℕ) : Type := (towerW n).carrier

/-- The trial product state `|Ψᵗ⟩ = ⨂ᵢ |ψᵗᵢ⟩` of Eqs. (49)-(50),
normalized for `Δ² ≤ 1`. -/
noncomputable def prodTrial (Δ θ : ℝ) : (n : ℕ) → tower n
  | 0 => 1
  | n + 1 => prodTrial Δ θ n ⊗ₜ[ℂ] trialState Δ θ

/-- The normalized ground product state `|Ψᵍ⟩ = ⨂ᵢ |ψᵍᵢ⟩` of Eq. (48). -/
noncomputable def prodGround : (n : ℕ) → tower n
  | 0 => 1
  | n + 1 => prodGround n ⊗ₜ[ℂ] ground

/-- The total Hamiltonian `H = Σᵢ Hᵢ` with each summand acting on one subsystem,
Eq. (47). -/
noncomputable def sumHam (Eg Ee : ℝ) : (n : ℕ) → tower n →L[ℂ] tower n
  | 0 => 0
  | n + 1 =>
      TensorProduct.mapL (ContinuousLinearMap.id ℂ (tower n)) (subHamiltonian Eg Ee)
        + TensorProduct.mapL (sumHam Eg Ee n) (ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 2)))

/-- The trial product state is normalized at every subsystem count. -/
theorem norm_prodTrial (Δ θ : ℝ) (hΔ : Δ ^ 2 ≤ 1) (n : ℕ) : ‖prodTrial Δ θ n‖ = 1 := by
  induction n with
  | zero => simp [prodTrial]
  | succ n ih =>
      rw [prodTrial, TensorProduct.norm_tmul, ih, norm_trialState Δ θ hΔ, one_mul]

/-- The ground product state is normalized at every subsystem count. -/
theorem norm_prodGround (n : ℕ) : ‖prodGround n‖ = 1 := by
  induction n with
  | zero => simp [prodGround]
  | succ n ih =>
      rw [prodGround, TensorProduct.norm_tmul, ih, norm_ground, one_mul]

/-- The trial product state is a unit vector: `⟨Ψᵗ|Ψᵗ⟩ = 1`. -/
theorem inner_self_prodTrial (Δ θ : ℝ) (hΔ : Δ ^ 2 ≤ 1) (n : ℕ) :
    ⟪prodTrial Δ θ n, prodTrial Δ θ n⟫_ℂ = 1 := by
  rw [inner_self_eq_norm_sq_to_K, norm_prodTrial Δ θ hΔ n]
  simp

/-- The genuine factorized overlap: the `N`-fold trial/ground amplitude equals `Δ ^ N`,
with the corrected exponent of Eq. (54). -/
theorem inner_prodTrial_prodGround (Δ θ : ℝ) (n : ℕ) :
    ⟪prodTrial Δ θ n, prodGround n⟫_ℂ = (↑Δ : ℂ) ^ n := by
  induction n with
  | zero => simp [prodTrial, prodGround]
  | succ n ih =>
      rw [prodTrial, prodGround, TensorProduct.inner_tmul, ih, inner_trial_ground, pow_succ]

/-- The absolute `N`-fold overlap amplitude is `|Δ| ^ N`, not `|Δ| ^ (2N)`; the printed
exponent `2N` in Eq. (54) belongs to the Born probability only. -/
theorem qpe_ground_amplitude (Δ θ : ℝ) (n : ℕ) :
    ‖⟪prodTrial Δ θ n, prodGround n⟫_ℂ‖ = |Δ| ^ n := by
  rw [inner_prodTrial_prodGround, norm_pow, Complex.norm_real, Real.norm_eq_abs]

/-- The squared overlap is `|Δ| ^ (2N)`. For `Δ² ≤ 1` this is the Born probability of
projecting the normalized trial state onto the ground product state. -/
theorem qpe_ground_born (Δ θ : ℝ) (n : ℕ) :
    ‖⟪prodTrial Δ θ n, prodGround n⟫_ℂ‖ ^ 2 = (Δ ^ 2) ^ n := by
  rw [qpe_ground_amplitude, ← pow_mul, mul_comm, pow_mul, ← abs_pow,
    abs_of_nonneg (sq_nonneg Δ)]

/-- The trial-state energy of the total Hamiltonian equals
`N * (Δ^2 * Eg + (1 - Δ^2) * Ee)`, Eq. (52). -/
theorem tower_energy (Δ θ : ℝ) (hΔ : Δ ^ 2 ≤ 1) (Eg Ee : ℝ) (n : ℕ) :
    ⟪prodTrial Δ θ n, sumHam Eg Ee n (prodTrial Δ θ n)⟫_ℂ
      = (((n * (Δ ^ 2 * Eg + (1 - Δ ^ 2) * Ee) : ℝ) : ℂ)) := by
  induction n with
  | zero => simp [prodTrial, sumHam, zero_mul, Complex.ofReal_zero]
  | succ n ih =>
      have hmap1 : (TensorProduct.mapL (ContinuousLinearMap.id ℂ (tower n)) (subHamiltonian Eg Ee))
          (prodTrial Δ θ n ⊗ₜ[ℂ] trialState Δ θ)
          = prodTrial Δ θ n ⊗ₜ[ℂ] subHamiltonian Eg Ee (trialState Δ θ) := by
        rw [TensorProduct.mapL_tmul, ContinuousLinearMap.id_apply]
      have hmap2 : (TensorProduct.mapL (sumHam Eg Ee n)
            (ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 2))))
          (prodTrial Δ θ n ⊗ₜ[ℂ] trialState Δ θ)
          = sumHam Eg Ee n (prodTrial Δ θ n) ⊗ₜ[ℂ] trialState Δ θ := by
        rw [TensorProduct.mapL_tmul, ContinuousLinearMap.id_apply]
      rw [prodTrial, sumHam, add_apply, hmap1, hmap2, inner_add_right,
        TensorProduct.inner_tmul, TensorProduct.inner_tmul, inner_self_prodTrial Δ θ hΔ n,
        trialState_energy Δ θ hΔ Eg Ee, ih, inner_self_trialState Δ θ hΔ]
      simp only [mul_one, one_mul]
      rw [← Complex.ofReal_add, Nat.cast_add, Nat.cast_one]
      congr 1
      ring
/-- The product of subsystem ground states is an eigenvector of the total Hamiltonian
with eigenvalue `N * Eg`. -/
theorem sumHam_apply_prodGround (Eg Ee : ℝ) (n : ℕ) :
    sumHam Eg Ee n (prodGround n) = ((n * Eg : ℝ) : ℂ) • prodGround n := by
  induction n with
  | zero => simp [prodGround, sumHam]
  | succ n ih =>
      rw [prodGround, sumHam, add_apply, TensorProduct.mapL_tmul, TensorProduct.mapL_tmul,
        ContinuousLinearMap.id_apply, ContinuousLinearMap.id_apply, subHamiltonian_apply_ground,
        ih, TensorProduct.tmul_smul, ← TensorProduct.smul_tmul', ← add_smul,
        ← Complex.ofReal_add, Nat.cast_succ]
      congr 2
      ring

/-- The energy expectation of the normalized ground product state is `N * Eg`. -/
theorem tower_ground_energy (Eg Ee : ℝ) (n : ℕ) :
    ⟪prodGround n, sumHam Eg Ee n (prodGround n)⟫_ℂ = ((n * Eg : ℝ) : ℂ) := by
  rw [sumHam_apply_prodGround, inner_smul_right, inner_self_eq_norm_sq_to_K, norm_prodGround]
  simp

/-- The energy bias relative to the ground product state equals
`N * (1 - Δ^2) * (Ee - Eg)`, Eq. (53) in the regime `Eg < Ee`. -/
theorem tower_bias (Δ θ : ℝ) (hΔ : Δ ^ 2 ≤ 1) (Eg Ee : ℝ) (n : ℕ) :
    ⟪prodTrial Δ θ n, sumHam Eg Ee n (prodTrial Δ θ n)⟫_ℂ
      - ⟪prodGround n, sumHam Eg Ee n (prodGround n)⟫_ℂ
      = ((n * (1 - Δ ^ 2) * (Ee - Eg) : ℝ) : ℂ) := by
  rw [tower_energy Δ θ hΔ Eg Ee n, tower_ground_energy, ← Complex.ofReal_sub]
  congr 1
  ring

/-- The Born probability decays exponentially in the subsystem count: there is a uniform
positive constant `C` (namely `2 * (1 - |Δ|)`) such that the probability is at most
`exp (-C * n)` for every `n`. -/
theorem bornProb_exponential_decay (Δ θ : ℝ) (hΔ : |Δ| < 1) :
    ∃ C > 0, ∀ n : ℕ, ‖⟪prodTrial Δ θ n, prodGround n⟫_ℂ‖ ^ 2 ≤ Real.exp (-(C * n)) := by
  refine ⟨2 * (1 - |Δ|), by nlinarith, ?_⟩
  intro n
  rw [qpe_ground_born]
  rcases eq_or_ne Δ 0 with h0 | h0
  · subst Δ
    cases n with
    | zero => simp
    | succ k =>
        have h0' : ((0:ℝ) ^ 2) ^ (k + 1) = 0 := by
          rw [show (0:ℝ) ^ 2 = 0 by norm_num, zero_pow (Nat.succ_ne_zero k)]
        rw [h0']
        exact (Real.exp_pos _).le
  · have hΔ2 : Δ ^ 2 = |Δ| ^ 2 := by rw [← abs_pow, abs_of_nonneg (sq_nonneg Δ)]
    rw [hΔ2]
    have hpos : 0 < |Δ| := abs_pos.2 h0
    have key : (|Δ| ^ 2) ^ n = Real.exp ((2 * (n : ℝ)) * Real.log |Δ|) := by
      rw [← pow_mul, ← Real.exp_log (pow_pos hpos _), Real.log_pow]
      push_cast
      ring
    rw [key, Real.exp_le_exp]
    have hlog := Real.log_le_sub_one_of_pos hpos
    nlinarith [(Nat.cast_nonneg (α := ℝ) n)]

/-- For nonzero overlap, the reciprocal Born probability for projection onto the ground
product state is at least `exp (C * n)` for every `n), for a uniform positive rate `C`. -/
theorem repetition_growth (Δ θ : ℝ) (hΔ : |Δ| < 1) (h0 : Δ ≠ 0) :
    ∃ C > 0, ∀ n : ℕ,
      Real.exp (C * n) ≤ (‖⟪prodTrial Δ θ n, prodGround n⟫_ℂ‖ ^ 2)⁻¹ := by
  obtain ⟨C, hC, hbound⟩ := bornProb_exponential_decay Δ θ hΔ
  refine ⟨C, hC, ?_⟩
  intro n
  have hp : 0 < ‖⟪prodTrial Δ θ n, prodGround n⟫_ℂ‖ ^ 2 := by
    rw [qpe_ground_amplitude]
    exact pow_pos (pow_pos (abs_pos.2 h0) n) 2
  calc
    Real.exp (C * n) = (Real.exp (-(C * n)))⁻¹ := by rw [← Real.exp_neg, neg_neg]
    _ ≤ (‖⟪prodTrial Δ θ n, prodGround n⟫_ℂ‖ ^ 2)⁻¹ := inv_anti₀ hp (hbound n)

end

end Qatlib.Papers.QChemistry14.OracleBias
