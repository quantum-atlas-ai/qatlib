/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RandCompile.ReferenceModel.QDriftReferenceSimulation
import Qatlib.Concepts.ChannelTheory.Stinespring.ShadowEstimator

/-!
# qDRIFT observable and reference-register estimates

This module applies the qDRIFT precision budget to signed Hamiltonian coefficients and to the
noncommuting Pauli pair `X` and `Z`. The randomized simulation setting follows [Campbell2019].

The theorem `qdrift_signed_observable_consumer` bounds the real observable trace error for
arbitrary input matrices, including a finite reference register. The Pauli specialization
identifies the target Hamiltonian and supplies a trace-norm approximation bound.

## Main statements

* `qdrift_signed_observable_consumer`: observable error for signed coefficients and Hermitian
  contractions.
* `qdrift_noncommuting_xz_consumer`: trace-norm guarantee for the Pauli `X+Z` example.

## References

* [Campbell, 2019][Campbell2019]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.RandCompile.ReferenceModel

namespace Qatlib.Concepts.TrotterFormula.GeneralOrder

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder Classical

/-- For signed coefficients and Hermitian contractions, the selected qDRIFT mixture approximates
ideal evolution with real observable trace error at most `‖O‖ * ε * Matrix.traceNorm ρ`,
including a reference register [Campbell2019]. -/
theorem qdrift_signed_observable_consumer (L D r : ℕ) (a : Fin L → ℝ)
    (K : Fin L → Operator D) (hlam : 0 < ∑ j, |a j|) (t ε : ℝ)
    (hε : 0 < ε) (hK : ∀ j, (K j).IsHermitian ∧ ‖K j‖ ≤ 1)
    (ρ O : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) :
    |(Matrix.trace (O * (referenceMixturePower (qdriftCoefficientLaw a hlam)
      (fun j => HamiltonianEvolution (qdriftSignedTerms a K j)
        (t * (∑ j, |a j|) / (qdriftSteps (∑ j, |a j|) t ε : ℝ))) r
          (qdriftSteps (∑ j, |a j|) t ε) ρ -
      TensorGate (HamiltonianEvolution (∑ j, (a j : ℂ) • K j) t) (1 : Operator r) * ρ *
        (TensorGate (HamiltonianEvolution (∑ j, (a j : ℂ) • K j) t) (1 : Operator r))ᴴ))).re| ≤
      ‖O‖ * ε * Matrix.traceNorm ρ := by
  have hb := qdrift_signed_coefficient_bridge L D a K hlam
  have he := (qdrift_derived_precision_budget L D r (qdriftCoefficientLaw a hlam)
    (qdriftSignedTerms a K) (∑ j, |a j|) t ε hlam.le hε (hb.2.2 hK)).2.2 ρ
  rw [hb.2.1] at he
  exact ((Complex.abs_re_le_norm _).trans (Matrix.abs_trace_le_traceNorm _)).trans
    ((Matrix.traceNorm_mul_le_opNorm_traceNorm _ _).trans
      ((mul_le_mul_of_nonneg_left he (norm_nonneg O)).trans_eq (by ring)))

/-- The Pauli `X` matrix is Hermitian and has operator norm at most one. -/
private theorem qdrift_pauliX_contract : pauliX.IsHermitian ∧ ‖pauliX‖ ≤ 1 := by
  have hh : pauliXᴴ = pauliX := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pauliX, Matrix.conjTranspose_apply]
  refine ⟨hh, l2_norm_unitary_le_one ?_⟩
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, hh]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX, Matrix.mul_apply, Fin.sum_univ_two]

/-- The Pauli `Z` matrix is Hermitian and has operator norm at most one. -/
private theorem qdrift_pauliZ_contract : pauliZ.IsHermitian ∧ ‖pauliZ‖ ≤ 1 := by
  have hh : pauliZᴴ = pauliZ := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pauliZ, Matrix.conjTranspose_apply]
  refine ⟨hh, l2_norm_unitary_le_one ?_⟩
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, hh]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

/-- The equal-weight qDRIFT model for Pauli `X` and `Z` has Hamiltonian `pauliX + pauliZ`. Its
selected mixture approximates ideal evolution in trace norm within `ε * Matrix.traceNorm ρ`,
including an arbitrary finite reference register [Campbell2019]. -/
theorem qdrift_noncommuting_xz_consumer (r : ℕ) (t ε : ℝ) (hε : 0 < ε) :
    let K := fun j : Fin 2 => if j = 0 then pauliX else pauliZ
    qdriftHamiltonian qdriftTwoLaw K 2 = pauliX + pauliZ ∧
    (∀ ρ : Matrix (Fin 2 × Fin r) (Fin 2 × Fin r) ℂ,
      Matrix.traceNorm (referenceMixturePower qdriftTwoLaw (fun j => HamiltonianEvolution (K j)
        (2 * t / (qdriftSteps 2 t ε : ℝ))) r (qdriftSteps 2 t ε) ρ -
        TensorGate (HamiltonianEvolution (pauliX + pauliZ) t) (1 : Operator r) * ρ *
          (TensorGate (HamiltonianEvolution (pauliX + pauliZ) t) (1 : Operator r))ᴴ) ≤
        ε * Matrix.traceNorm ρ) := by
  let K := fun j : Fin 2 => if j = 0 then pauliX else pauliZ
  have hK : ∀ j, (K j).IsHermitian ∧ ‖K j‖ ≤ 1 := by
    intro j
    dsimp [K]
    split_ifs
    · exact qdrift_pauliX_contract
    · exact qdrift_pauliZ_contract
  have hH : qdriftHamiltonian qdriftTwoLaw K 2 = pauliX + pauliZ := by
    simp [qdriftHamiltonian, qdriftTwoLaw, Fin.sum_univ_two, K]
  refine ⟨hH, fun ρ => ?_⟩
  have he := (qdrift_derived_precision_budget 2 2 r qdriftTwoLaw K 2 t ε
    (by norm_num) hε hK).2.2 ρ
  simpa only [hH, mul_comm t 2] using he

end Qatlib.Concepts.TrotterFormula.GeneralOrder
