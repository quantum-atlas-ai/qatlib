/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.UnitaryLearn09.MainResults.ParallelStorage
import Qatlib.Foundations.PureStateMath.Qubit

set_option backward.isDefEq.respectTransparency false

/-!
# UnitaryLearn09 — the measure-and-rotate retrieving strategy

Fixed source: Bisio–Chiribella–D'Ariano–Facchini–Perinotti,
*Optimal quantum learning of a unitary transformation*, arXiv:0903.0543v2
(PDF SHA-256 7740f8bf94c88b19a046c4c627cda8edf148bf92fe178c381fd20bceede57048),
Theorem 1 and Eqs. (19)–(25) (Sec. III A), Sec. III B and Sec. IV.

Theorem 1 says that the optimal retrieval of `U` from the memory state `|φ_U⟩`
is achieved by measuring the optimal POVM `P_Û = |η_Û⟩⟨η_Û|` and, conditionally
on the outcome `Û`, applying `Û` to the new input.  By Eq. (8) the fidelity of
such a measure-and-rotate retrieve channel with the target `U` is the POVM
average of the single-copy channel fidelities (the computation of Eqs. (19)–(25)
that reduces learning to estimation); for `M` output copies the same computation
gives the POVM average of the `M`-th powers.

This file formalizes that computation: POVM probabilities of a normalized
memory state are nonnegative and sum to one, and the retrieve channel written in
Kraus form `ξ ↦ √(p_ξ) • V_ξ` (or `ξ ↦ √(p_ξ) • V_ξ^{⊗M}` for `M` copies) has
exactly the stated fidelity.  It does *not* formalize the optimality bound of
Theorem 1 (`Tr[R_KK] ≤ d_j m_K^{(j)}/d_K` and the Schur decomposition of
`U^{⊗N}`), nor the non-decrease of the optimal single-copy fidelity with `M`.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Kronecker BigOperators ComplexOrder

namespace Qatlib.Papers.UnitaryLearn09.MainResults

open Qatlib.Foundations.PureStateMath

variable {Ξ : Type*} {d : ℕ}

/-- The probability of the estimate `ξ` when the memory state is `ψ`, i.e. the
Born probability `⟨ψ| P_ξ |ψ⟩` of the POVM element `P_ξ`. -/
def bornProb (P : Ξ → Matrix (Fin d) (Fin d) ℂ) (ψ : Fin d → ℂ) (ξ : Ξ) : ℝ :=
  ((star ψ) ⬝ᵥ ((P ξ) *ᵥ ψ)).re

/-- POVM probabilities are nonnegative. -/
theorem bornProb_nonneg {P : Ξ → Matrix (Fin d) (Fin d) ℂ}
    (hP : ∀ ξ, (P ξ).PosSemidef) (ψ : Fin d → ℂ) (ξ : Ξ) :
    0 ≤ bornProb P ψ ξ := by
  unfold bornProb
  exact (Complex.le_def.mp ((hP ξ).dotProduct_mulVec_nonneg ψ)).1

/-- A single term of the Kraus average: weighting the unitary channel fidelity
by the POVM probability is the Eq. (8) overlap of `√p • V_ξ` with the target.
This holds for arbitrary target and estimate matrices on a finite register. -/
theorem bornProb_mul_channelFidelity {I : Type*} [Fintype I] [DecidableEq I]
    {P : Ξ → Matrix (Fin d) (Fin d) ℂ} (hP : ∀ ξ, (P ξ).PosSemidef)
    (U Vξ : Matrix I I ℂ) (ψ : Fin d → ℂ) (ξ : Ξ) :
    bornProb P ψ ξ * unitaryChannelFidelity U Vξ =
      ‖(Uᴴ * ((Real.sqrt (bornProb P ψ ξ) : ℝ) : ℂ) • Vξ).trace‖ ^ 2 /
        (Fintype.card I : ℝ) ^ 2 := by
  unfold unitaryChannelFidelity
  rw [Matrix.mul_smul, Matrix.trace_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (bornProb_nonneg hP ψ ξ)]
  ring

variable [Fintype Ξ]

/-- A finite POVM on a `d`-dimensional register: positive operators summing to
the identity (the POVM `P_Û` of Theorem 1). -/
def IsPovm (P : Ξ → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  (∀ ξ, (P ξ).PosSemidef) ∧ ∑ ξ, P ξ = 1

/-- POVM probabilities of a normalized memory state sum to one; this is the
normalization used when the memory state is the stored state `|φ_U⟩`. -/
theorem bornProb_sum_one {P : Ξ → Matrix (Fin d) (Fin d) ℂ} (hP : IsPovm P)
    {ψ : Fin d → ℂ} (hψ : Normalized ψ) : ∑ ξ, bornProb P ψ ξ = 1 := by
  have hsum : ∑ ξ, bornProb P ψ ξ = ((star ψ) ⬝ᵥ ((∑ ξ, P ξ) *ᵥ ψ)).re := by
    simp only [bornProb]
    rw [← Complex.re_sum, ← dotProduct_sum, ← Matrix.sum_mulVec]
  rw [hsum]
  have hone : (∑ ξ, P ξ) *ᵥ ψ = ψ := by rw [hP.2, Matrix.one_mulVec]
  rw [hone]
  have h : (star ψ ⬝ᵥ ψ).re = 1 := by
    have := (normalized_iff_inner_self ψ).mp hψ
    rw [Qatlib.Foundations.PureStateMath.Inner] at this
    rw [this]
    simp
  exact h

/-- The fidelity of the measure-and-rotate retrieve channel with the target
`U`: the POVM average of the single-copy channel fidelities `F(U, V_ξ)`.  This
is the reduction of learning to estimation performed in Eqs. (19)–(25). -/
def estimateFidelity (P : Ξ → Matrix (Fin d) (Fin d) ℂ)
    (V : Ξ → Matrix (Fin d) (Fin d) ℂ) (U : Matrix (Fin d) (Fin d) ℂ)
    (ψ : Fin d → ℂ) : ℝ :=
  ∑ ξ, bornProb P ψ ξ * unitaryChannelFidelity (I := Fin d) U (V ξ)

/-- The retrieve channel of Theorem 1 in Kraus form, `K_ξ = √(p_ξ) • V_ξ`;
its fidelity is the paper's Eq. (8) sum of squared overlaps with the target. -/
def krausFidelity (P : Ξ → Matrix (Fin d) (Fin d) ℂ)
    (V : Ξ → Matrix (Fin d) (Fin d) ℂ) (U : Matrix (Fin d) (Fin d) ℂ)
    (ψ : Fin d → ℂ) : ℝ :=
  ∑ ξ, ‖(Uᴴ * ((Real.sqrt (bornProb P ψ ξ) : ℝ) : ℂ) • V ξ).trace‖ ^ 2 /
    (d : ℝ) ^ 2

/-- The POVM average of single-copy fidelities is exactly the Eq. (8) fidelity
of the Kraus-form measure-and-rotate channel. -/
theorem estimateFidelity_eq_krausFidelity {P : Ξ → Matrix (Fin d) (Fin d) ℂ}
    (hP : ∀ ξ, (P ξ).PosSemidef) (V : Ξ → Matrix (Fin d) (Fin d) ℂ)
    (U : Matrix (Fin d) (Fin d) ℂ) (ψ : Fin d → ℂ) :
    estimateFidelity P V U ψ = krausFidelity P V U ψ := by
  unfold estimateFidelity krausFidelity
  refine Finset.sum_congr rfl fun ξ _ => ?_
  simpa only [Fintype.card_fin] using
    (bornProb_mul_channelFidelity (I := Fin d) hP U (V ξ) ψ ξ)

/-- The `M`-copy global fidelity of the measure-and-rotate strategy: the POVM
average of the `M`-th powers of the single-copy fidelities.  This is the
computation behind Sec. III B.2's goal function. -/
def globalEstimateFidelity (P : Ξ → Matrix (Fin d) (Fin d) ℂ)
    (V : Ξ → Matrix (Fin d) (Fin d) ℂ) (U : Matrix (Fin d) (Fin d) ℂ)
    (ψ : Fin d → ℂ) (M : ℕ) : ℝ :=
  ∑ ξ, bornProb P ψ ξ * (unitaryChannelFidelity (I := Fin d) U (V ξ)) ^ M

/-- The `M`-copy retrieve channel `ξ ↦ √(p_ξ) • V_ξ^{⊗M}` in Kraus form,
whose Eq. (8) fidelity with `U^{⊗M}` is the global learning fidelity. -/
def krausFidelityCopies (P : Ξ → Matrix (Fin d) (Fin d) ℂ)
    (V : Ξ → Matrix (Fin d) (Fin d) ℂ) (U : Matrix (Fin d) (Fin d) ℂ)
    (ψ : Fin d → ℂ) (M : ℕ) : ℝ :=
  ∑ ξ, ‖((kronPow d M U)ᴴ *
      ((Real.sqrt (bornProb P ψ ξ) : ℝ) : ℂ) • kronPow d M (V ξ)).trace‖ ^ 2 /
    (d : ℝ) ^ (2 * M)

/-- `M`-copy measure-and-rotate fidelity: the POVM average of `M`-th powers is
the Eq. (8) fidelity of the `M`-copy Kraus retrieve channel. -/
theorem globalEstimateFidelity_eq_krausFidelityCopies
    {P : Ξ → Matrix (Fin d) (Fin d) ℂ} (hP : ∀ ξ, (P ξ).PosSemidef) (hd : 0 < d)
    (V : Ξ → Matrix (Fin d) (Fin d) ℂ) (U : Matrix (Fin d) (Fin d) ℂ)
    (ψ : Fin d → ℂ) (M : ℕ) :
    globalEstimateFidelity P V U ψ M = krausFidelityCopies P V U ψ M := by
  unfold globalEstimateFidelity krausFidelityCopies
  refine Finset.sum_congr rfl fun ξ _ => ?_
  have hterm := bornProb_mul_channelFidelity (I := kronIdx d M) hP
    (kronPow d M U) (kronPow d M (V ξ)) ψ ξ
  rw [unitaryChannelFidelity_kronPow hd U (V ξ), card_kronIdx] at hterm
  push_cast at hterm
  rw [← pow_mul, mul_comm M 2] at hterm
  exact hterm


/-- The single-copy figure of merit of the measure-and-rotate strategy is its
`M = 1` value; comparing the two displays the `M`-dependence of Sec. III B. -/
theorem globalEstimateFidelity_one {P : Ξ → Matrix (Fin d) (Fin d) ℂ}
    (V : Ξ → Matrix (Fin d) (Fin d) ℂ) (U : Matrix (Fin d) (Fin d) ℂ)
    (ψ : Fin d → ℂ) :
    globalEstimateFidelity P V U ψ 1 = estimateFidelity P V U ψ := by
  simp [globalEstimateFidelity, estimateFidelity, pow_one]

/-- When every single-copy fidelity is at most one, the global `M`-copy
fidelity of the measure-and-rotate strategy is bounded by its single-copy
(`M = 1`) fidelity.  This is the quantitative form of the contrast drawn in
Sec. III B between the single-copy and the global figures of merit. -/
theorem globalEstimateFidelity_le_single {P : Ξ → Matrix (Fin d) (Fin d) ℂ}
    (hP : ∀ ξ, (P ξ).PosSemidef) (V : Ξ → Matrix (Fin d) (Fin d) ℂ)
    (U : Matrix (Fin d) (Fin d) ℂ) (ψ : Fin d → ℂ) {M : ℕ} (hM : 1 ≤ M)
    (hF : ∀ ξ, unitaryChannelFidelity (I := Fin d) U (V ξ) ≤ 1) :
    globalEstimateFidelity P V U ψ M ≤ estimateFidelity P V U ψ := by
  unfold globalEstimateFidelity estimateFidelity
  refine Finset.sum_le_sum fun ξ _ => ?_
  refine mul_le_mul_of_nonneg_left ?_ (bornProb_nonneg hP ψ ξ)
  have h0 : 0 ≤ unitaryChannelFidelity (I := Fin d) U (V ξ) := by
    unfold unitaryChannelFidelity
    positivity
  calc (unitaryChannelFidelity (I := Fin d) U (V ξ)) ^ M
      ≤ (unitaryChannelFidelity (I := Fin d) U (V ξ)) ^ 1 :=
        pow_le_pow_of_le_one h0 (hF ξ) hM
    _ = unitaryChannelFidelity (I := Fin d) U (V ξ) := pow_one _

end Qatlib.Papers.UnitaryLearn09.MainResults
