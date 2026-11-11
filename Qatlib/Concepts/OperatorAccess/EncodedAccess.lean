/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.EncodingCore.AncillaErrorLaws
import Qatlib.Concepts.QueryWordCore.AdjointCircuits
import Qatlib.Concepts.BlockEncoding.Postselection
import Qatlib.Foundations.PureStateMath.BornBridge.PhyslibStates
import Qatlib.Concepts.BlockEncoding.LinearCombination

/-!
# Positive operator encodings from purified access

Explicit adjoint circuits encode reduced density matrices prepared by a unitary and measurement
effects associated with selected outcomes of a unitary dilation. Compression identities,
positivity, normalization, and exact query and gate counts certify these constructions in the
block encoding framework of [GilyenSuLowWiebe2019].

Born rule identities connect the measurement effects to outcome probabilities. A uniform
absolute expectation error for a Hermitian target then gives an approximate block encoding; the
underlying quantum state and measurement formalism is described in [Watrous2018]

## Main statements

* `purification_actual_positive_block_and_cost`: encodes a normalized density matrix with two
  queries and one gate.
* `povm_actual_effect_block_and_cost`: encodes a measurement effect with two queries and two
  gates.
* `povm_expectation_absolute_error_encoding`: converts expectation error into block encoding
  error.

## References

* [Watrous, 2018][Watrous2018]
* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option warningAsError false
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.BlockEncoding.LinearCombination

namespace Qatlib.Concepts.OperatorAccess.EncodedAccess
open Qatlib.Concepts.QueryWordCore.AdjointCircuits Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder
variable {A J I : Type*} [Fintype A] [DecidableEq A] [Fintype J] [DecidableEq J]
  [Fintype I] [DecidableEq I]

/-- The reduced matrix on `I` obtained by summing `psi (a, i) * star (psi (a, j))` over the
auxiliary index. -/
noncomputable def purifiedDensity (psi : QState (A × I)) : Matrix I I ℂ :=
  Matrix.of (fun i j => ∑ a, psi (a,i) * star (psi (a,j)))

/-- The permutation matrix exchanging the two `I` registers and leaving the auxiliary `A`
register fixed. -/
noncomputable def purificationSwap : Matrix ((A × I) × I) ((A × I) × I) ℂ :=
  permMatrix (fun x => ((x.1.1,x.2),x.1.2))

/-- The adjoint circuit word consisting of a backward query, the purification swap, and a
forward query. -/
noncomputable def purificationWord : List (AdjointStep ((A × I) × I)) :=
  [.backward, .gate purificationSwap, .forward]

/-- The matrix obtained by evaluating the purification word with oracle `U` tensored with the
identity on the extra `I` register. -/
noncomputable def purificationBody (U : Matrix (A × I) (A × I) ℂ) :
    Matrix ((A × I) × I) ((A × I) × I) ℂ :=
  evaluate (TensorGate U (1 : Matrix I I ℂ)) purificationWord

/-- The reduced matrix is the sum over auxiliary indices of the outer products of the
corresponding state slices. -/
theorem purifiedDensity_sum (psi : QState (A × I)) :
    purifiedDensity psi = ∑ a : A, outerProduct (fun i : I => psi (a,i)) := by
  ext i j
  simp [purifiedDensity, outerProduct_apply, Matrix.sum_apply]

/-- The reduced matrix of any state vector is positive semidefinite. -/
theorem purifiedDensity_posSemidef (psi : QState (A × I)) : (purifiedDensity psi).PosSemidef := by
  rw [purifiedDensity_sum]
  exact Matrix.posSemidef_sum _ (fun a ha => outerProduct_posSemidef _)

/-- The trace of the reduced matrix is the complex cast of the sum of squared norms of the state
amplitudes. -/
theorem purifiedDensity_trace (psi : QState (A × I)) :
    Matrix.trace (purifiedDensity psi) = ((∑ x : A × I, ‖psi x‖^2 : ℝ):ℂ) := by
  rw [purifiedDensity_sum, Matrix.trace_sum]
  simp_rw [trace_outerProduct]
  rw [← Complex.ofReal_sum, Fintype.sum_prod_type]

/-- Right multiplication by the permutation matrix associated with `f` selects column `f y` at
column `y`. -/
private theorem positiveAccess_mul_perm {X : Type*} [Fintype X] [DecidableEq X]
    (M : Matrix X X ℂ) (f : X → X) (x y : X) :
    (M * permMatrix f) x y = M x (f y) := by
  rw [Matrix.mul_apply]
  simp only [permMatrix, Matrix.of_apply]
  exact sum_fiber_mul_right (f y) (fun z => M x z)

/-- Compressing the purification body to the seed fiber gives the reduced matrix of the state
prepared from that basis seed. -/
theorem purification_corner (U : Matrix (A × I) (A × I) ℂ) (seed : A × I) :
    compress (encodingFiber seed) (purificationBody U) (encodingFiber seed) =
      purifiedDensity (U *ᵥ Qatlib.Foundations.PureStateMath.Ket seed) := by
  ext i j
  rw [compress_encodingFiber_eq]
  simp only [purificationBody, purificationWord, evaluate, instructionMatrix,
    Matrix.mul_one, tensorGate_conjTranspose, Matrix.conjTranspose_one]
  rw [← Matrix.mul_assoc, Matrix.mul_apply]
  simp only [purificationSwap, positiveAccess_mul_perm]
  simp only [tensorGate_apply, Matrix.one_apply, Matrix.conjTranspose_apply]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  change (∑ a : A, ∑ b : I, ∑ d : I,
      star (U (a,d) seed) * (if i=b then (1:ℂ) else 0) *
        (U (a,b) seed * (if d=j then (1:ℂ) else 0))) = _
  have hd (a : A) (b : I) : (∑ d : I,
      star (U (a,d) seed) * (if i=b then (1:ℂ) else 0) *
        (U (a,b) seed * (if d=j then (1:ℂ) else 0))) =
      star (U (a,j) seed) * (if i=b then (1:ℂ) else 0) * U (a,b) seed := by
    simpa only [mul_assoc] using sum_fiber_mul_right j
      (fun d => star (U (a,d) seed) * (if i=b then (1:ℂ) else 0) * U (a,b) seed)
  simp_rw [hd]
  have hb (a : A) : (∑ b : I, star (U (a,j) seed) *
      (if i=b then (1:ℂ) else 0) * U (a,b) seed) = star (U (a,j) seed)*U (a,i) seed := by
    have he (b : I) : star (U (a,j) seed) * (if i=b then (1:ℂ) else 0) * U (a,b) seed =
        (if b=i then (1:ℂ) else 0)*(star (U (a,j) seed)*U (a,b) seed) := by
      by_cases h : b=i
      · subst b; simp
      · simp [h, Ne.symm h]
    simp_rw [he]
    exact sum_fiber_mul_left i _
  simp_rw [hb]
  simp only [purifiedDensity, Matrix.of_apply, mulVec_ket_apply]
  apply Finset.sum_congr rfl
  intro a ha
  ring

/-- The purification circuit word is a well formed adjoint circuit. -/
theorem purification_word_wellformed :
    WellFormedAdjointCircuit (purificationWord (A := A) (I := I)) := by
  have hs : Function.Involutive (fun x : (A × I) × I => ((x.1.1,x.2),x.1.2)) := fun _ => rfl
  simp only [purificationWord, WellFormedAdjointCircuit.backward_cons_iff,
    WellFormedAdjointCircuit.gate_cons_iff, WellFormedAdjointCircuit.forward_cons_iff,
    WellFormedAdjointCircuit.nil, and_true]
  exact permMatrix_unitary hs

/-- A unitary state preparation yields a positive semidefinite trace one reduced matrix with an
exact projected unitary encoding by the purification body. The well formed purification word
uses two adjoint queries and one gate; see [GilyenSuLowWiebe2019]. -/
theorem purification_actual_positive_block_and_cost : ∀ (U : Matrix (A × I) (A × I) ℂ) (seed : A × I),
    U ∈ Matrix.unitaryGroup (A × I) ℂ →
    let rho := purifiedDensity (U *ᵥ Qatlib.Foundations.PureStateMath.Ket seed)
    rho.PosSemidef ∧ Matrix.trace rho = 1 ∧
    ProjectedUnitaryEncoding rho (purificationBody U) (encodingFiber seed) (encodingFiber seed) ∧
    WellFormedAdjointCircuit (purificationWord (A := A) (I := I)) ∧
    adjointQueryCount (purificationWord (A := A) (I := I)) = 2 ∧
    adjointGateCount (purificationWord (A := A) (I := I)) = 1
 := by
  intro U seed hU
  have hn := normalized_applyGate hU (normalized_ket seed)
  refine ⟨purifiedDensity_posSemidef _, ?_, ?_, purification_word_wellformed, rfl, rfl⟩
  · rw [purifiedDensity_trace]
    change (∑ x : A × I, ‖(U *ᵥ Qatlib.Foundations.PureStateMath.Ket seed) x‖^2) = 1 at hn
    exact_mod_cast hn
  · exact ⟨purification_word_wellformed.evaluate_unitary
      (tensorGate_unitary hU (Submonoid.one_mem _)),
      encodingFiber_isIsometry seed, encodingFiber_isIsometry seed, purification_corner U seed⟩

/-- The matrix block of `M` taking the input outcome fiber `j0` to the output outcome fiber `j`. -/
noncomputable def outcomeKraus (M : Matrix (J × I) (J × I) ℂ) (j0 j : J) : Matrix I I ℂ :=
  Matrix.of (fun i k => M (j,i) (j0,k))

/-- The sum of `Kᴴ * K` over selected outcome blocks of `M` from the input fiber `j0`. -/
noncomputable def outcomeEffect (M : Matrix (J × I) (J × I) ℂ) (j0 : J) (S : Finset J) : Matrix I I ℂ :=
  ∑ j ∈ S, (outcomeKraus M j0 j)ᴴ * outcomeKraus M j0 j

/-- The permutation that toggles a Boolean flag exactly when the outcome register belongs to
`S`. -/
noncomputable def outcomeXor (S : Finset J) : Matrix (Bool × (J × I)) (Bool × (J × I)) ℂ :=
  permMatrix (fun x => (Bool.xor x.1 (decide (x.2.1 ∈ S)),x.2))

/-- The input frame fixing the Boolean flag to false and the outcome register to `j0`. -/
noncomputable def outcomeFrame (j0 : J) : Matrix (Bool × (J × I)) I ℂ :=
  encodingFiber (I := J × I) false * encodingFiber j0

/-- The adjoint circuit word consisting of a flag flip, a backward query, outcome controlled
flag toggling, and a forward query. -/
noncomputable def outcomeWord (S : Finset J) : List (AdjointStep (Bool × (J × I))) :=
  [.gate (TensorGate PauliX (1 : Matrix (J × I) (J × I) ℂ)), .backward,
    .gate (outcomeXor S), .forward]

/-- The matrix obtained by evaluating the outcome word with `M` acting on the outcome and data
registers. -/
noncomputable def outcomeBody (M : Matrix (J × I) (J × I) ℂ) (S : Finset J) :
    Matrix (Bool × (J × I)) (Bool × (J × I)) ℂ :=
  evaluate (TensorGate (1 : Matrix Bool Bool ℂ) M) (outcomeWord S)

/-- The diagonal projector onto basis states whose outcome register belongs to `S`. -/
noncomputable def outcomeProjector (S : Finset J) : Matrix (J × I) (J × I) ℂ :=
  Matrix.diagonal (fun x => if x.1 ∈ S then 1 else 0)

/-- The outcome toggling matrix acts as the identity outside the outcome projector and as a flag
flip on its range. -/
theorem outcomeXor_decompose (S : Finset J) :
    outcomeXor (I := I) S =
      TensorGate (1 : Matrix Bool Bool ℂ) (1-outcomeProjector (I := I) S) +
      TensorGate PauliX (outcomeProjector (I := I) S) := by
  ext ⟨b,x⟩ ⟨d,y⟩
  by_cases hxy : x=y
  · subst y
    by_cases hx : x.1 ∈ S <;> cases b <;> cases d <;>
      simp [outcomeXor, outcomeProjector, tensorGate_apply, permMatrix, PauliX,
        hx]
  · cases b <;> cases d <;>
      simp [outcomeXor, outcomeProjector, tensorGate_apply, permMatrix, PauliX,
        hxy]

/-- The outcome body decomposes into a flag flip tensored with `Mᴴ * (1 - P) * M` and the flag
identity tensored with `Mᴴ * P * M`. -/
theorem outcomeBody_decompose (M : Matrix (J × I) (J × I) ℂ) (S : Finset J) :
    outcomeBody M S =
      TensorGate PauliX (Mᴴ*(1-outcomeProjector (I := I) S)*M) +
      TensorGate (1 : Matrix Bool Bool ℂ) (Mᴴ*outcomeProjector (I := I) S*M) := by
  have hx : PauliX * PauliX = (1 : Matrix Bool Bool ℂ) :=
    permMatrix_mul_self (by intro b; cases b <;> rfl)
  simp only [outcomeBody, outcomeWord, evaluate, instructionMatrix,
    Matrix.mul_one, tensorGate_conjTranspose, Matrix.conjTranspose_one]
  rw [outcomeXor_decompose]
  simp only [TensorGate, Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_kronecker_mul,
    Matrix.mul_one, Matrix.one_mul, hx]
  congr 1 <;> rw [Matrix.mul_assoc]

/-- Compressing `Mᴴ * outcomeProjector S * M` to the input outcome fiber gives the outcome
effect. -/
theorem outcomeEffect_corner (M : Matrix (J × I) (J × I) ℂ) (j0 : J) (S : Finset J) :
    compress (encodingFiber j0) (Mᴴ*outcomeProjector (I := I) S*M) (encodingFiber j0) =
      outcomeEffect M j0 S := by
  ext i k
  rw [compress_encodingFiber_eq]
  simp [outcomeProjector, outcomeEffect, outcomeKraus, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.diagonal_apply, Fintype.sum_prod_type,
    Matrix.sum_apply]
  calc
    _ = ∑ a : J, if a ∈ S then ∑ x : I, (starRingEnd ℂ) (M (a,x) (j0,i))*M (a,x) (j0,k) else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      by_cases h : a ∈ S
      · simp only [if_pos h]
      · simp only [if_neg h, Finset.sum_const_zero]
    _ = _ := Finset.sum_ite_mem_eq S _

/-- Compressing the outcome body to the input frame gives the selected outcome effect. -/
theorem outcomeBody_corner (M : Matrix (J × I) (J × I) ℂ) (j0 : J) (S : Finset J) :
    compress (outcomeFrame j0) (outcomeBody M S) (outcomeFrame j0) = outcomeEffect M j0 S := by
  have he : compress (outcomeFrame j0) (outcomeBody M S) (outcomeFrame j0) =
      compress (encodingFiber j0)
        (compress (encodingFiber (I := J × I) false) (outcomeBody M S)
          (encodingFiber (I := J × I) false)) (encodingFiber j0) := by
    dsimp only [outcomeFrame, compress]
    rw [Matrix.conjTranspose_mul (encodingFiber (J := Bool) (I := J × I) false)
      (encodingFiber (J := J) (I := I) j0)]
    simp only [Matrix.mul_assoc]
  rw [he]
  have hc : compress (encodingFiber (I := J × I) false) (outcomeBody M S)
      (encodingFiber (I := J × I) false) = Mᴴ*outcomeProjector (I := I) S*M := by
    ext x y
    rw [compress_encodingFiber_eq, outcomeBody_decompose]
    simp [tensorGate_apply, PauliX, permMatrix]
  rw [hc, outcomeEffect_corner]

/-- Every selected outcome effect is positive semidefinite. -/
theorem outcomeEffect_posSemidef (M : Matrix (J × I) (J × I) ℂ) (j0 : J) (S : Finset J) :
    (outcomeEffect M j0 S).PosSemidef :=
  Matrix.posSemidef_sum S (fun _ _ => Matrix.posSemidef_conjTranspose_mul_self _)

/-- For a unitary `M`, the effect of all outcomes is the identity matrix. -/
theorem outcomeEffect_univ (M : Matrix (J × I) (J × I) ℂ) (j0 : J)
    (hM : M ∈ Matrix.unitaryGroup (J × I) ℂ) : outcomeEffect M j0 Finset.univ = 1 := by
  have hm : Mᴴ*M = 1 := by
    simpa only [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] using hM
  ext i k
  have he := congrArg (fun V : Matrix (J × I) (J × I) ℂ => V (j0,i) (j0,k)) hm
  simpa [outcomeEffect, outcomeKraus, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Matrix.sum_apply, Matrix.one_apply] using he

/-- The selected outcome circuit word is a well formed adjoint circuit. -/
theorem outcomeWord_wellformed (S : Finset J) : WellFormedAdjointCircuit (outcomeWord (I := I) S) := by
  have hx : Function.Involutive (fun x : Bool × (J × I) =>
      (Bool.xor x.1 (decide (x.2.1 ∈ S)),x.2)) := by
    intro x
    rcases x with ⟨b,x⟩
    cases b <;> cases h : decide (x.1 ∈ S) <;> simp [h]
  simp only [outcomeWord, WellFormedAdjointCircuit.gate_cons_iff,
    WellFormedAdjointCircuit.backward_cons_iff, WellFormedAdjointCircuit.forward_cons_iff,
    WellFormedAdjointCircuit.nil, and_true]
  exact ⟨tensorGate_unitary pauliX_unitary (Submonoid.one_mem _), permMatrix_unitary hx⟩

/-- For unitary `M`, the selected outcome effect and its complement are positive semidefinite,
and the outcome body gives an exact projected unitary encoding. The well formed outcome word
uses two adjoint queries and two gates; see [GilyenSuLowWiebe2019]. -/
theorem povm_actual_effect_block_and_cost : ∀ (M : Matrix (J × I) (J × I) ℂ) (j0 : J) (S : Finset J),
    M ∈ Matrix.unitaryGroup (J × I) ℂ →
    (outcomeEffect M j0 S).PosSemidef ∧
    ((1 : Matrix I I ℂ)-outcomeEffect M j0 S).PosSemidef ∧
    ProjectedUnitaryEncoding (outcomeEffect M j0 S) (outcomeBody M S)
      (outcomeFrame j0) (outcomeFrame j0) ∧
    WellFormedAdjointCircuit (outcomeWord (I := I) S) ∧
    adjointQueryCount (outcomeWord (I := I) S) = 2 ∧
    adjointGateCount (outcomeWord (I := I) S) = 2
 := by
  intro M j0 S hM
  have hsum : outcomeEffect M j0 S + outcomeEffect M j0 Sᶜ = 1 := by
    unfold outcomeEffect
    rw [Finset.sum_add_sum_compl]
    exact outcomeEffect_univ M j0 hM
  have hcomp : (1 : Matrix I I ℂ)-outcomeEffect M j0 S = outcomeEffect M j0 Sᶜ := by
    rw [← hsum]
    abel
  refine ⟨outcomeEffect_posSemidef M j0 S, hcomp ▸ outcomeEffect_posSemidef M j0 Sᶜ,
    ?_, outcomeWord_wellformed S, rfl, rfl⟩
  exact ⟨(outcomeWord_wellformed S).evaluate_unitary
    (tensorGate_unitary (Submonoid.one_mem _) hM),
    Qatlib.Concepts.BlockEncoding.EncodingCore.IsIsometry.mul (encodingFiber_isIsometry false) (encodingFiber_isIsometry j0),
    Qatlib.Concepts.BlockEncoding.EncodingCore.IsIsometry.mul (encodingFiber_isIsometry false) (encodingFiber_isIsometry j0), outcomeBody_corner M j0 S⟩

/-- The probability mass of the selected outcome basis states equals the real part of the
outcome projector's quadratic form. -/
theorem outcomeProjector_born (S : Finset J) (v : QState (J × I)) :
    MeasureProb v {x | x.1 ∈ S} = (Qatlib.Foundations.PureStateMath.Inner v (outcomeProjector (I := I) S *ᵥ v)).re := by
  have hv (z : ℂ) : (star z*z).re = ‖z‖^2 := by
    change ((starRingEnd ℂ) z*z).re = ‖z‖^2
    rw [mul_comm, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  simp only [MeasureProb, BornProb, Finset.sum_filter, Qatlib.Foundations.PureStateMath.Inner, dotProduct,
    outcomeProjector, Matrix.mulVec_diagonal, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases h : x.1 ∈ S
  · simp only [if_pos h, one_mul]
    exact (hv (v x)).symm
  · simp only [if_neg h, zero_mul, mul_zero, Complex.zero_re]

/-- The selected outcome probability after applying `M` to the initialized outcome register
equals the real part of the outcome effect's quadratic form on the input state. -/
theorem outcomeEffect_born (M : Matrix (J × I) (J × I) ℂ) (j0 : J)
    (S : Finset J) (psi : QState I) :
    MeasureProb (M *ᵥ (encodingFiber j0 *ᵥ psi)) {x | x.1 ∈ S} =
      (Qatlib.Foundations.PureStateMath.Inner psi (outcomeEffect M j0 S *ᵥ psi)).re := by
  rw [outcomeProjector_born, ← outcomeEffect_corner]
  simp only [Qatlib.Foundations.PureStateMath.Inner, compress, Matrix.star_mulVec, Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, Matrix.conjTranspose_mul, Matrix.vecMul_vecMul, Matrix.mul_assoc]

/-- A Hermitian matrix whose real quadratic form is bounded in absolute value by nonnegative
`eps` on every normalized vector has operator norm at most `eps`. -/
theorem positiveAccess_hermitian_norm (D : Matrix I I ℂ) (hD : D.IsHermitian)
    (eps : ℝ) (heps : 0 ≤ eps)
    (h : ∀ psi : QState I, Normalized psi → |(Qatlib.Foundations.PureStateMath.Inner psi (D *ᵥ psi)).re| ≤ eps) :
    ‖D‖ ≤ eps := by
  let V := (hD.eigenvectorUnitary : Matrix I I ℂ)
  let lam : I → ℂ := fun i => (hD.eigenvalues i : ℂ)
  have hV : V ∈ Matrix.unitaryGroup I ℂ := hD.eigenvectorUnitary.2
  have hnV : ‖V‖ ≤ 1 := l2_norm_unitary_le_one hV
  have hnVH : ‖Vᴴ‖ ≤ 1 := by rw [Matrix.l2_opNorm_conjTranspose]; exact hnV
  have hdiag : ‖Matrix.diagonal lam‖ ≤ eps := by
    rw [Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg heps).mpr
    intro i
    have hp : Normalized (fun j : I => (hD.eigenvectorBasis i) j) := by
      apply (normalized_iff_norm_toEuclidean_fromVec _).mpr
      exact hD.eigenvectorBasis.orthonormal.1 i
    have hi := h _ hp
    change |(dotProduct (star ⇑(hD.eigenvectorBasis i))
      (D *ᵥ ⇑(hD.eigenvectorBasis i))).re| ≤ eps at hi
    have he : hD.eigenvalues i = (Qatlib.Foundations.PureStateMath.Inner (fun j : I => (hD.eigenvectorBasis i) j)
        (D *ᵥ (fun j : I => (hD.eigenvectorBasis i) j))).re := hD.eigenvalues_eq i
    dsimp only [lam]
    rw [Complex.norm_real, Real.norm_eq_abs, he]
    exact hi
  have hs : D = V * Matrix.diagonal lam * Vᴴ := hD.spectral_theorem
  rw [hs]
  calc
    _ ≤ (‖V‖*‖Matrix.diagonal lam‖)*‖Vᴴ‖ :=
      (Matrix.l2_opNorm_mul _ _).trans
        (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ (1*eps)*1 := by gcongr
    _ = eps := by ring

/-- If a Hermitian target's expectations approximate the selected outcome probabilities
uniformly within nonnegative `eps`, the outcome body block encodes that target with scale
one and error `eps`; see [GilyenSuLowWiebe2019]. -/
theorem povm_expectation_absolute_error_encoding : ∀ (M : Matrix (J × I) (J × I) ℂ) (j0 : J) (S : Finset J)
    (B : Matrix I I ℂ) (eps : ℝ), M ∈ Matrix.unitaryGroup (J × I) ℂ →
    B.IsHermitian → 0 ≤ eps →
    (∀ psi : QState I, Normalized psi →
      |(Qatlib.Foundations.PureStateMath.Inner psi (B *ᵥ psi)).re - MeasureProb (M *ᵥ (encodingFiber j0 *ᵥ psi))
        {x | x.1 ∈ S}| ≤ eps) →
    BlockEncoding B (outcomeBody M S) (outcomeFrame j0) (outcomeFrame j0) 1 eps
 := by
  intro M j0 S B eps hM hB heps herror
  have hp := povm_actual_effect_block_and_cost M j0 S hM
  have hD : (B-outcomeEffect M j0 S).IsHermitian := hB.sub hp.1.isHermitian
  have hn : ‖B-outcomeEffect M j0 S‖ ≤ eps :=
    positiveAccess_hermitian_norm _ hD eps heps (by
      intro psi hpsi
      have h := herror psi hpsi
      rw [outcomeEffect_born] at h
      simpa only [Qatlib.Foundations.PureStateMath.Inner, Matrix.sub_mulVec, dotProduct_sub,
          Complex.sub_re] using h)
  exact ⟨hp.2.2.1.unitary, hp.2.2.1.left_isometry, hp.2.2.1.right_isometry,
    by norm_num, heps, by simpa only [one_smul, hp.2.2.1.encoded] using hn⟩

end Qatlib.Concepts.OperatorAccess.EncodedAccess
