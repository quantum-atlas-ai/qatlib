/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.QlsHhl
import Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.HamiltonianInputModels
import Qatlib.Concepts.LocalMachine.LocalTransport.LeastSquaresOutputSpec

/-!
# Auxiliary HHL input-model bounds

The declarations in this module supply elementary dilation, signed-filter, storage, and
preparation facts for the input model of [HarrowHassidimLloyd2009]. They define explicit error
and cost scales and establish the identities and monotonicity bounds assembled by the
input-model interface theorems.

## Main statements

* `qlsScaledDilation_block_content`: Lists the four blocks of the quarter-scaled dilation.
* `signed_hVector_normalized`: Proves normalization for a consistent signed filter.
* `totalAngleBits_poly`: Bounds the preparation angle-bit count.

## References

* [Harrow et al., 2009][HarrowHassidimLloyd2009]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.HhlAlgorithms.Postselection
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter
open Qatlib.Concepts.QlsReadoutSpec.RectDilation
open Qatlib.Concepts.HhlAlgorithms.SinEnvProgram

set_option autoImplicit false

namespace Qatlib.Papers.LinearSystems09.InputModel

open Matrix
open Qatlib
open Qatlib.Concepts.HhlErrorBridge.FilterStability
open scoped Classical Matrix.Norms.L2Operator BigOperators

/-- The scaled rectangular dilation is Hermitian. -/
theorem qlsScaledDilation_isHermitian {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    (qlsScaledDilation A).IsHermitian := by
  show (qlsScaledDilation A)ᴴ = qlsScaledDilation A
  rw [qlsScaledDilation, Matrix.fromBlocks_conjTranspose]
  ext p q
  rcases p with i | j <;> rcases q with i' | j'
  · simp [Matrix.fromBlocks_apply₁₁]
  · simp [Matrix.fromBlocks_apply₁₂]
  · simp [Matrix.fromBlocks_apply₂₁]
  · simp [Matrix.fromBlocks_apply₂₂]

/-- The scaled dilation equals one quarter of the Hermitian dilation. -/
theorem qlsScaledDilation_eq_quarter_hermitianDilation {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) :
    qlsScaledDilation A = (1 / 4 : ℂ) • hermitianDilation A := by
  ext p q
  rcases p with i | j <;> rcases q with i' | j'
  · simp [qlsScaledDilation, hermitianDilation, Matrix.fromBlocks_apply₁₁,
      Matrix.smul_apply]
  · simp [qlsScaledDilation, hermitianDilation, Matrix.fromBlocks_apply₁₂,
      Matrix.smul_apply]
  · simp [qlsScaledDilation, hermitianDilation, Matrix.fromBlocks_apply₂₁,
      Matrix.smul_apply]
  · simp [qlsScaledDilation, hermitianDilation, Matrix.fromBlocks_apply₂₂,
      Matrix.smul_apply]

/-- The scaled dilation has zero diagonal blocks and off-diagonal entries `A i j / 4` and their
complex conjugates. -/
theorem qlsScaledDilation_block_content {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    (∀ (i i' : Fin m), qlsScaledDilation A (Sum.inl i) (Sum.inl i') = 0) ∧
      (∀ (i : Fin m) (j : Fin n),
        qlsScaledDilation A (Sum.inl i) (Sum.inr j) = (1 / 4 : ℂ) * A i j) ∧
      (∀ (j : Fin n) (i : Fin m),
        qlsScaledDilation A (Sum.inr j) (Sum.inl i) = (1 / 4 : ℂ) * star (A i j)) ∧
      (∀ (j j' : Fin n), qlsScaledDilation A (Sum.inr j) (Sum.inr j') = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i i'
    simp [qlsScaledDilation, Matrix.fromBlocks_apply₁₁]
  · intro i j
    simp [qlsScaledDilation, Matrix.fromBlocks_apply₁₂, Matrix.smul_apply,
      smul_eq_mul]
  · intro j i
    simp [qlsScaledDilation, Matrix.fromBlocks_apply₂₁, Matrix.smul_apply,
      Matrix.conjTranspose_apply, smul_eq_mul]
  · intro j j'
    simp [qlsScaledDilation, Matrix.fromBlocks_apply₂₂]

/-- Every rectangular system with right-hand side `b` possesses dilation-reduction data whose
matrix and right-hand side are `A` and `b` and which satisfies `ReducesAt`. -/
theorem qlsDilation_reduces {O I : Type} [Fintype O] [DecidableEq O]
    [Fintype I] [DecidableEq I] (A : Matrix O I ℂ) (b : QState O) :
    ∃ R : Qatlib.Concepts.QlsReadoutSpec.RectDilation.DilationReduction O I,
      R.A = A ∧ R.b = b ∧ R.ReducesAt :=
  Qatlib.Concepts.QlsReadoutSpec.RectDilation.rectangular_dilation_reduction O I A b

/-- The optional least-squares direction is `none` when the least-squares vector is zero. -/
theorem leastSquaresDirection_none_of_zero_vector {O I : Type} [Fintype O]
    [DecidableEq O] [Fintype I] [DecidableEq I] (A : Matrix O I ℂ) (b : QState O)
    (h : leastSquaresVector A b = 0) : leastSquaresDirection A b = none := by
  unfold leastSquaresDirection
  rw [if_pos h]

/-- The sum of the squared real filter amplitudes `filterF` and `filterG`. -/
def signedKernelMass (F : SignedSinEnvelopeFilter) (d θ : ℝ) : ℝ :=
  F.filterF d θ ^ 2 + F.filterG d θ ^ 2

/-- For a consistent signed filter and positive `d`, the kernel mass is even in the spectral
parameter. -/
theorem signedKernelMass_even (F : SignedSinEnvelopeFilter)
    (hF : F.Consistent) (d θ : ℝ) (hd : 0 < d) :
    signedKernelMass F d θ = signedKernelMass F d (-θ) := by
  unfold signedKernelMass
  have hFodd := hF.1 d θ hd
  have hFeven := hF.2.1 d θ hd
  rw [hFodd, hFeven]
  ring

/-- For nonnegative spectral parameter and positive `d`, a consistent signed filter has the same
kernel mass as the unsigned sine-envelope filter. -/
theorem signedKernelMass_eq_unsigned (F : SignedSinEnvelopeFilter)
    (hF : F.Consistent) (d θ : ℝ) (hd : 0 < d) (hθ : 0 ≤ θ) :
    signedKernelMass F d θ =
      sinEnvelopeFilterF d θ ^ 2 + sinEnvelopeFilterG d θ ^ 2 := by
  have h := hF.2.2.2.1 d θ hd hθ
  unfold signedKernelMass
  rw [h.1, h.2]

/-- For a consistent signed filter and positive `d`, the kernel mass is at most one. -/
theorem signedKernelMass_le_one (F : SignedSinEnvelopeFilter)
    (hF : F.Consistent) (d θ : ℝ) (hd : 0 < d) :
    signedKernelMass F d θ ≤ 1 := by
  have h := hF.2.2.2.2 d θ hd
  unfold signedKernelMass at h
  exact h

/-- At zero spectral parameter, a consistent signed filter with positive `d` has flags zero and
one half. -/
theorem signedFilter_zeroMode_flag (F : SignedSinEnvelopeFilter)
    (hF : F.Consistent) (d : ℝ) (hd : 0 < d) :
    F.filterF d 0 = 0 ∧ F.filterG d 0 = 1 / 2 := by
  exact hF.2.2.1 d hd

/-- For a consistent signed filter with positive `d`, the sum of squared norms of the three
`hVector` components is one. -/
theorem signed_hVector_normalized (F : SignedSinEnvelopeFilter)
    (hF : F.Consistent) (d θ : ℝ) (hd : 0 < d) :
    ∑ s : Fin 3, ‖F.hVector d θ s‖ ^ 2 = 1 := by
  have hm := signedKernelMass_le_one F hF d θ hd
  have hnonneg : 0 ≤ 1 - F.filterF d θ ^ 2 - F.filterG d θ ^ 2 := by
    unfold signedKernelMass at hm
    linarith
  have hsum : ∑ s : Fin 3, ‖F.hVector d θ s‖ ^ 2 =
      (Real.sqrt (1 - F.filterF d θ ^ 2 - F.filterG d θ ^ 2)) ^ 2
        + F.filterF d θ ^ 2 + F.filterG d θ ^ 2 := by
    simp [SignedSinEnvelopeFilter.hVector, Fin.sum_univ_succ, Complex.norm_real,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    ring
  rw [hsum, Real.sq_sqrt hnonneg]
  ring

/-- The binary length bound `q.log2 + 1` for the denominator parameter. -/
def denominatorBits (q : ℕ) : ℕ := q.log2 + 1

/-- The denominator parameter is strictly less than two raised to `denominatorBits q`. -/
theorem denominatorBits_spec (q : ℕ) : q < 2 ^ denominatorBits q := by
  exact Nat.lt_log2_self

/-- The table storage count `M * q`. -/
def tableStorageBits (M q : ℕ) : ℕ := M * q

/-- The table storage count is monotone when both `M` and `q` increase. -/
theorem tableStorageBits_mono (M M' q q' : ℕ) (hM : M ≤ M') (hq : q ≤ q') :
    tableStorageBits M q ≤ tableStorageBits M' q' := by
  simp only [tableStorageBits]
  calc M * q ≤ M' * q := Nat.mul_le_mul hM (Nat.le_refl q)
    _ ≤ M' * q' := Nat.mul_le_mul_left M' hq

/-- The sum of the phase, rotation, table, and access error contributions. -/
def qlsErrorBudget (phase rotation table access : ℝ) : ℝ :=
  phase + rotation + table + access

/-- The total error budget equals the sum of its four arguments. -/
theorem qlsErrorBudget_sum (a b c d : ℝ) :
    qlsErrorBudget a b c d = a + b + c + d := by
  simp [qlsErrorBudget]

/-- The total error budget is monotone in its first argument. -/
theorem qlsErrorBudget_mono (a a' b c d : ℝ) (h : a ≤ a') :
    qlsErrorBudget a b c d ≤ qlsErrorBudget a' b c d := by
  simp only [qlsErrorBudget]
  linarith

/-- The sine-envelope amplitude `sin (π * (τ + 1 / 2) / M)`. -/
noncomputable def envelopeAmplitude (M : ℕ) (τ : Fin M) : ℝ :=
  Real.sin (Real.pi * ((τ.val : ℝ) + 1 / 2) / (M : ℝ))

/-- For positive `M`, the envelope amplitude is invariant under reflection of its index about
the grid midpoint. -/
theorem envelopeAmplitude_symmetry (M : ℕ) (hM : 0 < M) (τ : Fin M) :
    envelopeAmplitude M τ =
      envelopeAmplitude M ⟨M - 1 - τ.val, by omega⟩ := by
  have hMne : (M : ℝ) ≠ 0 := by
    exact_mod_cast (show M ≠ 0 by omega)
  have hsplit : ((M - 1 - τ.val : ℕ) : ℝ) = (M : ℝ) - (τ.val : ℝ) - 1 := by
    have h1 : (M - 1 - τ.val : ℕ) = (M - τ.val : ℕ) - 1 := by omega
    have h2 : ((M - τ.val : ℕ) : ℝ) = (M : ℝ) - (τ.val : ℝ) :=
      Nat.cast_sub (by exact_mod_cast (show τ.val ≤ M by omega))
    rw [h1, Nat.cast_sub (by omega), h2]
    ring
  have harg : Real.pi * ((τ.val : ℝ) + 1 / 2) / (M : ℝ)
      + Real.pi * (((M - 1 - τ.val : ℕ) : ℝ) + 1 / 2) / (M : ℝ) = Real.pi := by
    have hnum : Real.pi * ((τ.val : ℝ) + 1 / 2)
        + Real.pi * (((M - 1 - τ.val : ℕ) : ℝ) + 1 / 2) = Real.pi * (M : ℝ) := by
      rw [hsplit]
      ring
    have hcombine : Real.pi * ((τ.val : ℝ) + 1 / 2) / (M : ℝ)
        + Real.pi * (((M - 1 - τ.val : ℕ) : ℝ) + 1 / 2) / (M : ℝ)
        = (Real.pi * ((τ.val : ℝ) + 1 / 2)
          + Real.pi * (((M - 1 - τ.val : ℕ) : ℝ) + 1 / 2)) / (M : ℝ) := by ring
    rw [hcombine, hnum, div_eq_iff hMne]
  have hsin : Real.sin (Real.pi * ((τ.val : ℝ) + 1 / 2) / (M : ℝ))
      = Real.sin (Real.pi - Real.pi * ((τ.val : ℝ) + 1 / 2) / (M : ℝ)) :=
    (Real.sin_pi_sub _).symm
  unfold envelopeAmplitude
  rw [hsin]
  congr 1
  linarith [harg]

/-- A pointwise amplitude error at most nonnegative `δ` implies a Euclidean error at most `sqrt
M * δ`. -/
theorem amplitude_perturbation_l2 (M : ℕ) (ψ χ : QState (Fin M)) {δ : ℝ}
    (hδ : 0 ≤ δ) (h : ∀ τ, ‖χ τ - ψ τ‖ ≤ δ) :
    Real.sqrt (∑ τ : Fin M, ‖χ τ - ψ τ‖ ^ 2) ≤ Real.sqrt (M : ℝ) * δ := by
  have hsummax : (∑ τ : Fin M, ‖χ τ - ψ τ‖ ^ 2) ≤ M * δ ^ 2 := by
    calc (∑ τ : Fin M, ‖χ τ - ψ τ‖ ^ 2) ≤ ∑ _τ : Fin M, δ ^ 2 := by
          refine Finset.sum_le_sum fun τ _ => ?_
          have hx : 0 ≤ ‖χ τ - ψ τ‖ := norm_nonneg _
          nlinarith [h τ, hx, mul_self_nonneg (‖χ τ - ψ τ‖), mul_self_nonneg δ]
      _ = M * δ ^ 2 := by simp [Finset.sum_const]
  have hsq : (Real.sqrt (M : ℝ) * δ) ^ 2 = M * δ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ (M : ℝ))]
  have hT : Real.sqrt (M : ℝ) * δ = Real.sqrt ((Real.sqrt (M : ℝ) * δ) ^ 2) := by
    have hpos : 0 ≤ Real.sqrt (M : ℝ) * δ := by positivity
    rw [Real.sqrt_sq hpos]
  have hkey : (∑ τ : Fin M, ‖χ τ - ψ τ‖ ^ 2) ≤ (Real.sqrt (M : ℝ) * δ) ^ 2 := by
    rw [hsq]
    exact hsummax
  rw [hT]
  exact Real.sqrt_le_sqrt hkey

/-- The number `M.log2 + 1` of bisection stages. -/
def bisectionStages (M : ℕ) : ℕ := M.log2 + 1

/-- The per-stage angle precision `k + bisectionStages M + 1`. -/
def stageAngleBits (M k : ℕ) : ℕ := k + bisectionStages M + 1

/-- The total angle-bit count, given by the number of stages times the bits per stage. -/
def totalAngleBits (M k : ℕ) : ℕ := bisectionStages M * stageAngleBits M k

/-- The total angle-bit count is at most `(M.log2 + 1) * (k + M.log2 + 2)`. -/
theorem totalAngleBits_poly (M k : ℕ) :
    totalAngleBits M k ≤ (M.log2 + 1) * (k + M.log2 + 2) := by
  simp only [totalAngleBits, stageAngleBits, bisectionStages]
  have h1 : k + (M.log2 + 1) + 1 ≤ k + M.log2 + 2 := by omega
  exact Nat.mul_le_mul_left _ h1

/-- The emitter uses `M.log2 + 1` bisection stages. -/
theorem emitter_stage_count (M : ℕ) : bisectionStages M = M.log2 + 1 := rfl

/-- The natural-number source runtime scale `κ * T_B + κ^2 * s^2 * logN * epsInv`. -/
def qlsSourceScale (κ T_B s logN epsInv : ℕ) : ℕ :=
  κ * T_B + κ ^ 2 * s ^ 2 * logN * epsInv

/-- The source runtime scale is monotone in the state-preparation cost `T_B`. -/
theorem qlsSourceScale_mono_prep (κ T_B T_B' s logN epsInv : ℕ) (h : T_B ≤ T_B') :
    qlsSourceScale κ T_B s logN epsInv ≤ qlsSourceScale κ T_B' s logN epsInv := by
  simp only [qlsSourceScale]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left κ h) _

/-- The source runtime scale is monotone in the inverse-precision parameter `epsInv`. -/
theorem qlsSourceScale_mono_eps (κ T_B s logN epsInv epsInv' : ℕ)
    (h : epsInv ≤ epsInv') :
    qlsSourceScale κ T_B s logN epsInv ≤ qlsSourceScale κ T_B s logN epsInv' := by
  simp only [qlsSourceScale]
  have hmul : κ ^ 2 * s ^ 2 * logN * epsInv ≤ κ ^ 2 * s ^ 2 * logN * epsInv' :=
    Nat.mul_le_mul_left _ h
  exact Nat.add_le_add_left hmul _

/-- The synthesis access correction factor is at least one. -/
theorem qlsSynthAccessCorrection_bound (M k : ℕ) :
    qlsSynthAccessFactor M k ≥ 1 := by
  unfold qlsSynthAccessFactor
  have : (1 + (1 / 2 : ℝ) ^ k) ≥ 1 := by
    have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ k := by positivity
    linarith
  exact one_le_pow₀ this

/-- The natural-number birthday scale `2^(n / 2 + 1)`, with natural-number division in the
exponent. -/
def simonBirthdayBound (n : ℕ) : ℕ := 2 ^ (n / 2 + 1)

/-- The birthday scale is at least `2^(n / 2)`. -/
theorem simonBirthdayBound_ge (n : ℕ) : 2 ^ (n / 2) ≤ simonBirthdayBound n := by
  simp only [simonBirthdayBound]
  exact Nat.pow_le_pow_right (by omega : 0 < 2) (by omega : n / 2 ≤ n / 2 + 1)

/-- The reduced exponent `3 * α * n + 4 * β * n` in the Simon comparison. -/
def simonReducedExponent (α β n : ℝ) : ℝ := 3 * α * n + 4 * β * n

/-- The reduced Simon exponent factors as `(3 * α + 4 * β) * n`. -/
theorem simonReducedExponent_eq (α β n : ℝ) :
    simonReducedExponent α β n = (3 * α + 4 * β) * n := by
  simp [simonReducedExponent]
  ring

/-- When `3 * α + 4 * β < 1 / 2` and `n > 0`, the reduced exponential rate is strictly below
`exp ((n / 2) * log 2)` [HarrowHassidimLloyd2009]. -/
theorem simon_reduction_below_birthday (α β n : ℝ) (h : 3 * α + 4 * β < 1 / 2)
    (hn : 0 < n) :
    Real.exp ((simonReducedExponent α β n) * Real.log 2)
      < Real.exp (((1 / 2 : ℝ) * n) * Real.log 2) := by
  rw [simonReducedExponent_eq]
  have hmul : (3 * α + 4 * β) * n < (1 / 2 : ℝ) * n :=
    mul_lt_mul_of_pos_right h hn
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply Real.exp_lt_exp.mpr
  exact mul_lt_mul_of_pos_right hmul hlog

end Qatlib.Papers.LinearSystems09.InputModel
