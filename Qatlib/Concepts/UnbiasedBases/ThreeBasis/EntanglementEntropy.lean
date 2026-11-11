/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.UnbiasedBases.ThreeBasis.EntanglementEntropyDefs

/-!
# Entropy of Bipartite Pure States

This module proves the basic properties of `entropy` for normalized pure states on a finite
bipartite system, following the reduced-state description of entanglement entropy [Watrous2018].
Entropy uses the natural logarithm. The spectral formula `entropy_eq_spectral` connects the
density-based definition to the existing LOCC entanglement entropy, while
`entropy_eq_complement` identifies it with the von Neumann entropy of the other marginal.

The dimension bounds, local unitary invariance, and explicit product-state and Bell-state values
describe how this entropy behaves under standard changes of state. In particular, the bounds
apply to either subsystem dimension, product states have entropy zero, and all four Bell states
have entropy log 2.

## Main statements

* `entropy_nonneg`, `entropy_le_log_left`, and `entropy_le_log_right` give the lower and
  dimension-dependent upper bounds.
* `reduced_local_unitary` describes covariance of the reduced state, and `entropy_local_unitary`
  gives entropy invariance.
- `entropy_product` computes zero entropy for normalized product states.
* `bell_reduced` computes the Bell marginal as one half of the identity, and `entropy_bell`
  computes its entropy.

## References

- [Watrous, 2018][Watrous2018] John Watrous, The Theory of Quantum Information.
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.QuantumEntropy.EntropyCalculus
open Qatlib.Concepts.FiniteLocc.LOCCProgram
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

set_option autoImplicit false

noncomputable section
namespace Qatlib.Concepts.UnbiasedBases.ThreeBasis

open Qatlib
open scoped BigOperators

variable {D E : ℕ}

/-- The existence of a normalized state on `Fin D × Fin E` implies that both subsystem
dimensions D and E are positive. -/
theorem dimensions_pos (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ) :
    0 < D ∧ 0 < E := by
  constructor
  · by_contra h
    have hD : D = 0 := Nat.eq_zero_of_not_pos h
    subst D
    simp [Normalized] at hψ
  · by_contra h
    have hE : E = 0 := Nat.eq_zero_of_not_pos h
    subst E
    simp [Normalized] at hψ

/-- For a normalized bipartite state and a Hermiticity witness for its reduced matrix, `entropy`
equals the spectral `LOCCProgram.entanglementEntropy` computed from that matrix's
eigenvalues. -/
theorem entropy_eq_spectral (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ)
    (h : (PartialTrace (outerProduct ψ)).IsHermitian) :
    entropy ψ hψ = Qatlib.Concepts.FiniteLocc.LOCCProgram.entanglementEntropy ψ h := by
  change (∑ i, Real.negMulLog (h.eigenvalues i)) = -∑ i, h.eigenvalues i * Real.log _
  simp only [Real.negMulLog, neg_mul, Finset.sum_neg_distrib]

/-- The entanglement entropy of every normalized finite bipartite pure state is nonnegative. -/
theorem entropy_nonneg (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ) :
    0 ≤ entropy ψ hψ := by
  unfold entropy Qatlib.Concepts.QuantumEntropy.EntropyCalculus.entropy
  exact Sᵥₙ_nonneg _

/-- The entanglement entropy of a normalized state on `Fin D × Fin E` is at most the natural
logarithm of the left subsystem dimension D. -/
theorem entropy_le_log_left (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ) :
    entropy ψ hψ ≤ Real.log D := by
  simpa [entropy, Qatlib.Concepts.QuantumEntropy.EntropyCalculus.entropy] using
    Sᵥₙ_le_log_d (Qatlib.Concepts.QuantumEntropy.EntropyCalculus.state (reducedDensity ψ hψ))

/-- The entanglement entropy of a normalized bipartite pure state also equals the von Neumann
entropy of the complementary marginal obtained by tracing out the left subsystem. -/
theorem entropy_eq_complement (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ) :
    entropy ψ hψ =
      Sᵥₙ (MState.pure (Qatlib.Foundations.PureStateMath.BornBridge.normalizedStateEquivKet _ ⟨ψ, hψ⟩)).traceLeft := by
  rw [entropy_eq_partial, Sᵥₙ_of_partial_eq]

/-- The entanglement entropy of a normalized state on `Fin D × Fin E` is at most the natural
logarithm of the right subsystem dimension E. -/
theorem entropy_le_log_right (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ) :
    entropy ψ hψ ≤ Real.log E := by
  rw [entropy_eq_complement]
  simpa using Sᵥₙ_le_log_d
    (MState.pure (Qatlib.Foundations.PureStateMath.BornBridge.normalizedStateEquivKet _ ⟨ψ, hψ⟩)).traceLeft

/-- Applying local unitaries U and V to a normalized bipartite pure state conjugates its left
reduced mixed state by U. -/
theorem reduced_local_unitary (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ)
    (U : Matrix.unitaryGroup (Fin D) ℂ) (V : Matrix.unitaryGroup (Fin E) ℂ) :
    Qatlib.Concepts.QuantumEntropy.EntropyCalculus.state (reducedDensity (ApplyGate (TensorGate U.val V.val) ψ)
      (normalized_applyGate (tensorGate_unitary U.property V.property) hψ)) =
      (Qatlib.Concepts.QuantumEntropy.EntropyCalculus.state (reducedDensity ψ hψ)).uConj U := by
  apply MState.ext_m
  change PartialTrace (outerProduct (ApplyGate (TensorGate U.val V.val) ψ)) =
    U.val * PartialTrace (outerProduct ψ) * U.val.conjTranspose
  have hfactor : TensorGate U.val V.val =
      TensorGate U.val (1 : Operator E) * TensorGate (1 : Operator D) V.val := by
    rw [tensorGate_mul, Matrix.mul_one, Matrix.one_mul]
  rw [hfactor, applyGate_mul, partialTrace_outerProduct_apply_tensorLeft,
    partialTrace_outerProduct_apply_tensorRight ψ V.val V.property]

/-- Applying a tensor product of local unitary gates preserves the entanglement entropy of a
normalized bipartite pure state. -/
theorem entropy_local_unitary (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ)
    (U : Matrix.unitaryGroup (Fin D) ℂ) (V : Matrix.unitaryGroup (Fin E) ℂ) :
    entropy (ApplyGate (TensorGate U.val V.val) ψ)
      (normalized_applyGate (tensorGate_unitary U.property V.property) hψ) =
      entropy ψ hψ := by
  unfold entropy Qatlib.Concepts.QuantumEntropy.EntropyCalculus.entropy
  rw [reduced_local_unitary ψ hψ U V]
  exact congrArg Hₛ (MState.uConj_spectrum_eq _ U)

/-- The tensor product of two normalized pure states has entanglement entropy zero. -/
theorem entropy_product (a : QState (Fin D)) (b : QState (Fin E))
    (ha : Normalized a) (hb : Normalized b) :
    entropy (TensorState a b) (normalized_tensorState ha hb) = 0 := by
  have hred : Qatlib.Concepts.QuantumEntropy.EntropyCalculus.state
      (reducedDensity (TensorState a b) (normalized_tensorState ha hb)) =
      MState.pure (Qatlib.Foundations.PureStateMath.BornBridge.normalizedStateEquivKet _ ⟨a, ha⟩) := by
    apply MState.ext_m
    simp only [Qatlib.Concepts.QuantumEntropy.EntropyCalculus.state_m, reducedDensity_val,
      Qatlib.Foundations.PureStateMath.BornBridge.pure_normalizedStateEquivKet_m]
    exact partialTrace_outerProduct_tensorState a hb
  unfold entropy Qatlib.Concepts.QuantumEntropy.EntropyCalculus.entropy
  rw [hred, Sᵥₙ_of_pure_zero]

/-- Each of the four Bell states indexed by a pair of Boolean values is normalized. -/
theorem bell_normalized (s : Bool × Bool) : Normalized (Qatlib.Concepts.FiniteLocc.LOCCProgram.bell s) := by
  fin_cases s
  all_goals
    unfold Normalized
    simp only [Qatlib.Concepts.FiniteLocc.LOCCProgram.bell, Pi.smul_apply, smul_eq_mul,
      Fintype.sum_prod_type, Fin.sum_univ_two]
    simp only [ite_true, ite_false, Bool.not_true, Bool.not_false, Bool.false_eq_true,
      one_smul, neg_smul]
    simp only [Pi.add_apply, Pi.neg_apply, ket_apply]
  all_goals simp
  all_goals norm_num

/-- The left reduced matrix of each Bell state is one half of the identity matrix of size two. -/
theorem bell_reduced (s : Bool × Bool) :
    PartialTrace (outerProduct (Qatlib.Concepts.FiniteLocc.LOCCProgram.bell s)) =
      (1 / 2 : ℂ) • (1 : Operator 2) := by
  ext i j
  fin_cases s <;> fin_cases i <;> fin_cases j
  all_goals
    simp only [PartialTrace, outerProduct_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.one_apply, Fin.sum_univ_two, Qatlib.Concepts.FiniteLocc.LOCCProgram.bell, Pi.smul_apply,
      ite_true, ite_false, Bool.not_true, Bool.not_false, Bool.false_eq_true,
      one_smul, neg_smul, Pi.add_apply, Pi.neg_apply, ket_apply]
  all_goals simp
  all_goals norm_num
  all_goals
    have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← mul_inv, h2]
    norm_num

/-- Each normalized Bell state has entanglement entropy equal to the natural logarithm of two. -/
theorem entropy_bell (s : Bool × Bool) :
    entropy (Qatlib.Concepts.FiniteLocc.LOCCProgram.bell s) (bell_normalized s) = Real.log 2 := by
  have hM : (Qatlib.Concepts.QuantumEntropy.EntropyCalculus.state
      (reducedDensity (Qatlib.Concepts.FiniteLocc.LOCCProgram.bell s) (bell_normalized s))).M =
      HermitianMat.diagonal ℂ (fun _ : Fin 2 => (1 / 2 : ℝ)) := by
    apply Subtype.ext
    change PartialTrace (outerProduct (Qatlib.Concepts.FiniteLocc.LOCCProgram.bell s)) =
      Matrix.diagonal (fun _ : Fin 2 => ((1 / 2 : ℝ) : ℂ))
    rw [bell_reduced]
    ext i j
    by_cases h : i = j <;> simp [Matrix.diagonal, h]
  unfold entropy Qatlib.Concepts.QuantumEntropy.EntropyCalculus.entropy
  rw [Sᵥₙ_eq_trace_cfc_negMulLog, hM, HermitianMat.cfc_diagonal,
    HermitianMat.trace_diagonal]
  norm_num [Function.comp_def, Real.negMulLog, Real.log_div]
  ring

end Qatlib.Concepts.UnbiasedBases.ThreeBasis
