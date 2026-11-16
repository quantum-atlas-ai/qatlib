/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.AdaptiveCP.BranchTrace.QuantumChannel
public import Qatlib.Concepts.ChannelTheory.Stinespring.ChannelStructureDefs
public import Qatlib.Concepts.ChannelTheory.Stinespring.ChannelStructureKraus
public import Qatlib.Concepts.FiniteLocc.LOCCProgram.EntanglementDefs
public import Qatlib.Concepts.FiniteLocc.LOCCProgram.Entanglement
public import Qatlib.Papers.PPTCompose26.Composition.Solution
public import Qatlib.Papers.PPTCompose26.Composition.SpecialFamilies

@[expose] public section


/-!
# Bridge between `Qatlib` (v4.35.0) and `Qatlib.Foundations.PPTMatrix.OperatorCones`

This module provides the bidirectional mathematical bridge and downstream consumer
theorems connecting the independent reconstruction of the PPT composition bound
(`Qatlib.Foundations.PPTMatrix.OperatorCones`) to the locked `Qatlib` library:

1. `refMap_eq_channelAmplification`:
   `refMap (Fin r) T X = ChannelAmplification T r X`
2. `isCompletelyPositive_iff_completelyPositive`:
   `Qatlib.Foundations.PPTMatrix.OperatorCones.IsCompletelyPositive T ↔ CompletelyPositive T`
3. `choiMatrix_eq_refMap_omegaVec`:
   `ChoiMatrix T = refMap (Fin d) T (pureState (omegaVec d))`
4. `partialTransposeRef_eq_partialTranspose_transpose`:
   `partialTransposeRef X = (PartialTranspose X).transpose`
5. `isSeparable_iff_isSeparableSub`:
   `Qatlib.Foundations.PPTMatrix.OperatorCones.IsSeparable X ↔ IsSeparableSub X`
6. Downstream consumer theorems expressing the `2(d-1)` PPT composition bound,
   `N ≥ 2(d-1)` bound, interleaved CP compositions, and bundled `QuantumChannel`
   entanglement-breaking guarantees directly in terms of `CompletelyPositive`,
   `ChannelAmplification`, `ChoiMatrix`, `PartialTranspose`, `IsSeparableSub`,
   and `QuantumChannel`.
7. Bridge 9 native library consumers:
   - `isSeparableSub_partialTranspose_posSemidef_lib`: Peres–Horodecki criterion for `IsSeparableSub`.
   - `isPPT_of_isEntanglementBreaking_lib`: Universal cone inclusion `IsEntanglementBreaking → IsPPT`.
   - `isEntanglementBreaking_ofFn_of_exists_lib`: Multi-step ideal absorption in CP chains.
   - `isEntanglementBreaking_pow_of_le_lib` and `choi_pow_isSeparableSub_of_le_lib`:
     Universal all-power threshold $M \ge 2(d-1)$ for channel amplification and Choi matrix separability.
-/

namespace Qatlib.Papers.PPTCompose26.Composition

open Qatlib.Foundations.PPTMatrix.OperatorCones

open Matrix
open scoped ComplexOrder Kronecker BigOperators

open Qatlib
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.FiniteLocc.LOCCProgram

variable {d e : ℕ}

/-! ## Bridge 1: `refMap` and `ChannelAmplification` -/

/-- The action of `refMap (Fin r)` on an input matrix is definitionally equal to
`ChannelAmplification T r`. -/
theorem refMap_eq_channelAmplification_apply (r : ℕ)
    (T : Operator d →ₗ[ℂ] Operator e)
    (X : Matrix (Fin r × Fin d) (Fin r × Fin d) ℂ) :
    refMap (Fin r) T X = ChannelAmplification T r X :=
  rfl

/-- As a function on matrices, `refMap (Fin r) T` equals `ChannelAmplification T r`. -/
theorem refMap_eq_channelAmplification (r : ℕ)
    (T : Operator d →ₗ[ℂ] Operator e) :
    (refMap (Fin r) T :
        Matrix (Fin r × Fin d) (Fin r × Fin d) ℂ →
          Matrix (Fin r × Fin e) (Fin r × Fin e) ℂ) =
      ChannelAmplification T r :=
  rfl

/-- Block extraction identity matching `ChannelAmplification`. -/
theorem block_eq_channelAmplification_block (r : ℕ)
    (X : Matrix (Fin r × Fin d) (Fin r × Fin d) ℂ) (i j : Fin r) :
    block X i j = (fun a b => X (i, a) (j, b)) :=
  rfl

/-! ## Bridge 2: `IsCompletelyPositive` and `CompletelyPositive` -/

/-- Definitional equivalence between `Qatlib.Foundations.PPTMatrix.OperatorCones.IsCompletelyPositive` and
`Qatlib.Concepts.AdaptiveCP.BranchTrace.CompletelyPositive`. -/
theorem isCompletelyPositive_iff_completelyPositive
    (T : Operator d →ₗ[ℂ] Operator e) :
    Qatlib.Foundations.PPTMatrix.OperatorCones.IsCompletelyPositive T ↔
      Qatlib.Concepts.AdaptiveCP.BranchTrace.CompletelyPositive T :=
  Iff.rfl

/-! ## Bridge 3: `ChoiMatrix` and `refMap (Fin d) T (pureState (omegaVec d))` -/

/-- The unnormalized maximally entangled state `pureState (omegaVec d)` equals `omegaMatrix d`. -/
theorem pureState_omegaVec_eq_omegaMatrix (d : ℕ) :
    pureState (omegaVec d) = omegaMatrix d := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [pureState, Matrix.vecMulVec_apply, omegaVec, Pi.star_apply,
    RCLike.star_def, omegaMatrix]
  by_cases hia : i = a <;> by_cases hjb : j = b <;> simp [hia, hjb]

/-- The `(i, j)` block of `pureState (omegaVec d)` is the matrix unit `matrixUnit i j`. -/
theorem block_pureState_omegaVec (d : ℕ) (i j : Fin d) :
    block (pureState (omegaVec d)) i j = matrixUnit i j := by
  ext a b
  simp only [block_apply, pureState, Matrix.vecMulVec_apply, omegaVec,
    Pi.star_apply, RCLike.star_def, matrixUnit, Matrix.single]
  by_cases ha : i = a <;> by_cases hb : j = b
  · subst ha hb
    simp
  · simp [ha, hb]
  · simp [ha, hb]
  · simp [ha, hb]

/-- The Choi matrix in `Qatlib` equals `refMap (Fin d) T (pureState (omegaVec d))`. -/
theorem choiMatrix_eq_refMap_omegaVec (T : Operator d →ₗ[ℂ] Operator e) :
    ChoiMatrix T = refMap (Fin d) T (pureState (omegaVec d)) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [ChoiMatrix, refMap_apply, block_pureState_omegaVec]

/-- Alignment with `choiMatrix_eq_amplification` from `ChannelStructureKraus`. -/
theorem choiMatrix_eq_amplification_omegaVec (T : Operator d →ₗ[ℂ] Operator e) :
    ChoiMatrix T = ChannelAmplification T d (pureState (omegaVec d)) := by
  exact choiMatrix_eq_refMap_omegaVec T

/-- Complete positivity of `T` is equivalent to positive semidefiniteness of `ChoiMatrix T`. -/
theorem completelyPositive_iff_choiMatrix_posSemidef
    (T : Operator d →ₗ[ℂ] Operator e) :
    CompletelyPositive T ↔ (ChoiMatrix T).PosSemidef := by
  rw [← isCompletelyPositive_iff_completelyPositive]
  rw [isCompletelyPositive_iff_choi]
  rw [← choiMatrix_eq_refMap_omegaVec]

/-! ## Bridge 4: `partialTransposeRef` and `PartialTranspose` -/

/-- The reference partial transpose `partialTransposeRef` is the matrix transpose of the
system partial transpose `PartialTranspose`. -/
theorem partialTransposeRef_eq_partialTranspose_transpose
    (X : Matrix (Fin d × Fin e) (Fin d × Fin e) ℂ) :
    partialTransposeRef X = (PartialTranspose X).transpose := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [partialTransposeRef_apply, Matrix.transpose_apply, PartialTranspose]
  rfl

/-- Inversely, the system partial transpose is the transpose of the reference partial transpose. -/
theorem partialTranspose_eq_partialTransposeRef_transpose
    (X : Matrix (Fin d × Fin e) (Fin d × Fin e) ℂ) :
    PartialTranspose X = (partialTransposeRef X).transpose := by
  rw [partialTransposeRef_eq_partialTranspose_transpose, Matrix.transpose_transpose]

/-- Positive semidefiniteness of `partialTransposeRef X` is equivalent to positive
semidefiniteness of `PartialTranspose X`. -/
theorem posSemidef_partialTransposeRef_iff_posSemidef_partialTranspose
    (X : Matrix (Fin d × Fin e) (Fin d × Fin e) ℂ) :
    (partialTransposeRef X).PosSemidef ↔ (PartialTranspose X).PosSemidef := by
  rw [partialTransposeRef_eq_partialTranspose_transpose]
  exact Matrix.posSemidef_transpose_iff

/-- Characterization of `IsPPTMap` in terms of `ChoiMatrix` and `PartialTranspose`. -/
theorem isPPTMap_iff_choi_partialTranspose
    (T : Operator d →ₗ[ℂ] Operator e) :
    IsPPTMap T ↔ (ChoiMatrix T).PosSemidef ∧ (PartialTranspose (ChoiMatrix T)).PosSemidef := by
  rw [isPPTMap_iff_choi]
  rw [← choiMatrix_eq_refMap_omegaVec]
  rw [posSemidef_partialTransposeRef_iff_posSemidef_partialTranspose]

/-! ## Bridge 5: `IsSeparable` and `IsSeparableSub` -/

/-- `IsSeparableSub` implies `Qatlib.Foundations.PPTMatrix.OperatorCones.IsSeparable`. -/
theorem isSeparable_of_isSeparableSub
    (X : Matrix (Fin d × Fin e) (Fin d × Fin e) ℂ)
    (h : IsSeparableSub X) : Qatlib.Foundations.PPTMatrix.OperatorCones.IsSeparable X := by
  obtain ⟨n, p, σ, τ, hp, hσ, hτ, rfl⟩ := h
  refine ⟨n, fun i => (p i : ℂ) • σ i, fun i => τ i, ?_, ?_, ?_⟩
  · intro i
    have hpos : 0 ≤ (p i : ℂ) := by
      rw [Complex.nonneg_iff]
      exact ⟨hp i, rfl⟩
    exact (hσ i).1.smul hpos
  · intro i
    exact (hτ i).1
  · ext ⟨i, a⟩ ⟨j, b⟩
    simp only [TensorGate, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.kroneckerMap_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring

/-- Every nonzero positive semidefinite matrix is a positive real scalar multiple
of a trace-one density operator. -/
theorem exists_density_smul_of_posSemidef_ne_zero {S : Operator d}
    (hS : S.PosSemidef) (hz : S ≠ 0) :
    ∃ (c : ℝ) (σ : Operator d),
      0 ≤ c ∧ IsDensityOperator σ ∧ S = (c : ℂ) • σ := by
  have hne : Matrix.trace S ≠ 0 := fun h => hz (hS.trace_eq_zero_iff.mp h)
  have hsum : Matrix.trace S = ∑ i, ((hS.isHermitian.eigenvalues i : ℝ) : ℂ) :=
    hS.isHermitian.trace_eq_sum_eigenvalues
  have hre : 0 ≤ (Matrix.trace S).re := by
    rw [hsum, Complex.re_sum]
    exact Finset.sum_nonneg fun i _ => hS.eigenvalues_nonneg i
  have hreal : Matrix.trace S = ((Matrix.trace S).re : ℂ) := by
    rw [hsum, Complex.re_sum, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.ofReal_re]
  have hc : 0 < (Matrix.trace S).re := by
    rcases lt_or_eq_of_le hre with h | h
    · exact h
    · refine absurd ?_ hne
      rw [hreal]
      exact_mod_cast h.symm
  have hre0 : ((Matrix.trace S).re : ℂ) ≠ 0 := by
    exact_mod_cast hc.ne'
  refine ⟨(Matrix.trace S).re, ((Matrix.trace S).re : ℂ)⁻¹ • S, hre, ?_, ?_⟩
  · refine ⟨hS.smul (by exact_mod_cast inv_nonneg.mpr hc.le), ?_⟩
    rw [Matrix.trace_smul, hreal, smul_eq_mul]
    exact inv_mul_cancel₀ hre0
  · rw [smul_smul, mul_inv_cancel₀ hre0, one_smul]

/-- A Kronecker product of two positive semidefinite matrices is subnormalized separable. -/
theorem isSeparableSub_kronecker_of_posSemidef
    {A : Operator d} {B : Operator e}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    IsSeparableSub (A ⊗ₖ B) := by
  by_cases hAz : A = 0
  · rw [hAz, Matrix.zero_kronecker]
    exact isSeparableSub_zero
  · by_cases hBz : B = 0
    · rw [hBz, Matrix.kronecker_zero]
      exact isSeparableSub_zero
    · obtain ⟨cA, σ, hcA, hσ, hA_eq⟩ := exists_density_smul_of_posSemidef_ne_zero hA hAz
      obtain ⟨cB, τ, hcB, hτ, hB_eq⟩ := exists_density_smul_of_posSemidef_ne_zero hB hBz
      refine ⟨1, fun _ => cA * cB, fun _ => σ, fun _ => τ, ?_, ?_, ?_, ?_⟩
      · intro _
        exact mul_nonneg hcA hcB
      · intro _
        exact hσ
      · intro _
        exact hτ
      · simp only [Fin.sum_univ_one, TensorGate, hA_eq, hB_eq]
        ext ⟨i, a⟩ ⟨j, b⟩
        simp only [Matrix.smul_apply, Matrix.kroneckerMap_apply, smul_eq_mul, Complex.ofReal_mul]
        ring

/-- `Qatlib.Foundations.PPTMatrix.OperatorCones.IsSeparable` implies `IsSeparableSub`. -/
theorem isSeparableSub_of_isSeparable
    (X : Matrix (Fin d × Fin e) (Fin d × Fin e) ℂ)
    (h : Qatlib.Foundations.PPTMatrix.OperatorCones.IsSeparable X) : IsSeparableSub X := by
  obtain ⟨N, A, B, hA, hB, rfl⟩ := h
  apply isSeparableSub_sum N
  intro i
  exact isSeparableSub_kronecker_of_posSemidef (hA i) (hB i)

/-- **Equivalence of Separability Cones:** `Qatlib.Foundations.PPTMatrix.OperatorCones.IsSeparable X ↔ IsSeparableSub X`. -/
theorem isSeparable_iff_isSeparableSub
    (X : Matrix (Fin d × Fin e) (Fin d × Fin e) ℂ) :
    Qatlib.Foundations.PPTMatrix.OperatorCones.IsSeparable X ↔ IsSeparableSub X :=
  ⟨isSeparableSub_of_isSeparable X, isSeparable_of_isSeparableSub X⟩

/-- Entanglement breaking in terms of `CompletelyPositive`, `ChannelAmplification`, and `IsSeparableSub`. -/
theorem isEntanglementBreaking_iff_lib
    (T : Operator d →ₗ[ℂ] Operator e) :
    IsEntanglementBreaking T ↔
      CompletelyPositive T ∧
        ∀ (r : ℕ) (X : Matrix (Fin r × Fin d) (Fin r × Fin d) ℂ),
          X.PosSemidef → IsSeparableSub (ChannelAmplification T r X) := by
  unfold IsEntanglementBreaking
  rw [isCompletelyPositive_iff_completelyPositive]
  refine and_congr Iff.rfl ?_
  constructor
  · intro h r X hX
    rw [← isSeparable_iff_isSeparableSub]
    exact h r X hX
  · intro h r X hX
    rw [isSeparable_iff_isSeparableSub]
    exact h r X hX

/-- **Choi Characterization of Entanglement Breaking in Library Vocabulary:**
A linear map `T` is entanglement breaking iff `ChoiMatrix T` is `IsSeparableSub`. -/
theorem isEntanglementBreaking_iff_choi_isSeparableSub
    (T : Operator d →ₗ[ℂ] Operator e) :
    IsEntanglementBreaking T ↔ IsSeparableSub (ChoiMatrix T) := by
  rw [isEntanglementBreaking_iff_choi]
  rw [← choiMatrix_eq_refMap_omegaVec]
  exact isSeparable_iff_isSeparableSub (ChoiMatrix T)

/-! ## Downstream Consumer Theorems in Native `Qatlib` Vocabulary -/

/-- Predicate for a linear map on `Operator d` being PPT in `Qatlib` vocabulary. -/
def IsPPT (T : Operator d →ₗ[ℂ] Operator d) : Prop :=
  CompletelyPositive T ∧ CompletelyPositive (Qatlib.Foundations.PPTMatrix.OperatorCones.transposeMap (Fin d) ∘ₗ T)

/-- Establishes `isPPT_iff_isPPTMap`: `IsPPT T ↔ IsPPTMap T`, for the stated parameters. -/
theorem isPPT_iff_isPPTMap (T : Operator d →ₗ[ℂ] Operator d) :
    IsPPT T ↔ IsPPTMap T :=
  Iff.rfl

/-- **Main Theorem (Native Library Consumer):**
For every `d ≥ 2`, the composition of any `2 * (d - 1)` PPT maps on `Operator d`
maps every bipartite positive semidefinite operator under `ChannelAmplification`
into `IsSeparableSub`. -/
theorem compose_ppt_maps_entanglementBreaking_lib (d : ℕ) (hd : 2 ≤ d)
    (Φ : Fin (2 * (d - 1)) → Module.End ℂ (Operator d))
    (hΦ : ∀ i, IsPPT (Φ i)) :
    ∀ (r : ℕ) (X : Matrix (Fin r × Fin d) (Fin r × Fin d) ℂ),
      X.PosSemidef →
      IsSeparableSub (ChannelAmplification (compList (List.ofFn Φ)) r X) := by
  intro r X hX
  have h_eb := compose_ppt_maps_entanglementBreaking d hd Φ
    (fun i => (isPPT_iff_isPPTMap _).mp (hΦ i))
  rw [isEntanglementBreaking_iff_lib] at h_eb
  exact h_eb.2 r X hX

/-- **Choi-State Consumer:**
For every `d ≥ 2`, the Choi matrix of the composition of any `2 * (d - 1)` PPT maps
on `Operator d` is `IsSeparableSub`. -/
theorem compose_ppt_maps_choi_isSeparableSub (d : ℕ) (hd : 2 ≤ d)
    (Φ : Fin (2 * (d - 1)) → Module.End ℂ (Operator d))
    (hΦ : ∀ i, IsPPT (Φ i)) :
    IsSeparableSub (ChoiMatrix (compList (List.ofFn Φ))) := by
  have h_eb := compose_ppt_maps_entanglementBreaking d hd Φ
    (fun i => (isPPT_iff_isPPTMap _).mp (hΦ i))
  rw [isEntanglementBreaking_iff_choi_isSeparableSub] at h_eb
  exact h_eb

/-- **Generalization to `N ≥ 2 * (d - 1)` PPT maps (Native Library Consumer):** -/
theorem compose_at_least_ppt_maps_entanglementBreaking_lib (d : ℕ) (hd : 2 ≤ d) (N : ℕ)
    (hN : 2 * (d - 1) ≤ N) (Φ : Fin N → Module.End ℂ (Operator d))
    (hΦ : ∀ i, IsPPT (Φ i)) :
    ∀ (r : ℕ) (X : Matrix (Fin r × Fin d) (Fin r × Fin d) ℂ),
      X.PosSemidef →
      IsSeparableSub (ChannelAmplification (compList (List.ofFn Φ)) r X) := by
  intro r X hX
  have h_eb := compose_at_least_ppt_maps_entanglementBreaking d hd N hN Φ
    (fun i => (isPPT_iff_isPPTMap _).mp (hΦ i))
  rw [isEntanglementBreaking_iff_lib] at h_eb
  exact h_eb.2 r X hX

/-- **Interleaved Composition with Arbitrary `CompletelyPositive` Maps (Native Library Consumer):** -/
theorem compose_ppt_map_interleaved_entanglementBreaking_lib (d : ℕ) (hd : 2 ≤ d)
    (T : Module.End ℂ (Operator d)) (hT : IsPPT T)
    (S : Fin (2 * (d - 1) - 1) → Module.End ℂ (Operator d))
    (hS : ∀ i, CompletelyPositive (S i)) :
    ∀ (r : ℕ) (X : Matrix (Fin r × Fin d) (Fin r × Fin d) ℂ),
      X.PosSemidef →
      IsSeparableSub (ChannelAmplification (compList (T :: List.ofFn fun i => T ∘ₗ S i)) r X) := by
  intro r X hX
  have h_eb := compose_ppt_map_interleaved_entanglementBreaking d hd T
    ((isPPT_iff_isPPTMap _).mp hT) S
    (fun i => (isCompletelyPositive_iff_completelyPositive _).mpr (hS i))
  rw [isEntanglementBreaking_iff_lib] at h_eb
  exact h_eb.2 r X hX

/-- **Bundled `QuantumChannel` Consumer:**
Any `2 * (d - 1)` quantum channels on `Operator d` that are completely copositive
have an entanglement-breaking composition. -/
theorem compose_quantumChannels_entanglementBreaking_lib (d : ℕ) (hd : 2 ≤ d)
    (Q : Fin (2 * (d - 1)) → QuantumChannel d d)
    (hQ_copos : ∀ i, CompletelyPositive (Qatlib.Foundations.PPTMatrix.OperatorCones.transposeMap (Fin d) ∘ₗ (Q i).map)) :
    ∀ (r : ℕ) (X : Matrix (Fin r × Fin d) (Fin r × Fin d) ℂ),
      X.PosSemidef →
      IsSeparableSub (ChannelAmplification (compList (List.ofFn fun i => (Q i).map)) r X) := by
  apply compose_ppt_maps_entanglementBreaking_lib d hd
  intro i
  exact ⟨(Q i).completelyPositive, hQ_copos i⟩

/-- **Entanglement-Breaking Index Upper Bound in Library Terms:** -/
theorem ebIndex_le_of_isPPT_lib (d : ℕ) (hd : 2 ≤ d)
    (T : Module.End ℂ (Operator d)) (hT : IsPPT T) :
    ebIndex T ≤ ((2 * (d - 1) : ℕ) : ℕ∞) :=
  ebIndex_le_of_isPPTMap d hd T ((isPPT_iff_isPPTMap _).mp hT)

/-- **Sanity Check Alignment:**
The qubit transpose map is not `CompletelyPositive`, matching
`Qatlib.Concepts.ChannelTheory.Stinespring.transposeMap_two_not_completelyPositive`. -/
theorem transposeMap_two_sanity_lib :
    ¬ CompletelyPositive (Qatlib.Foundations.PPTMatrix.OperatorCones.transposeMap (Fin 2)) := by
  rw [← isCompletelyPositive_iff_completelyPositive]
  exact transposeMap_isCompletelyCopositive_not_isCompletelyPositive.2

/-! ## Bridge 7: Special PPT Families & Library Consumers -/

/-- **Diagonal Pinching Map Entanglement Breaking (Native Library Consumer):**
For any nonnegative weights `w : Fin d → ℝ`, `diagPinchMap w` maps every positive semidefinite
operator under `ChannelAmplification` into `IsSeparableSub`. -/
theorem diagPinchMap_entanglementBreaking_lib {d : ℕ} (w : Fin d → ℝ) (hw : ∀ k, 0 ≤ w k) :
    ∀ (r : ℕ) (X : Matrix (Fin r × Fin d) (Fin r × Fin d) ℂ),
      X.PosSemidef →
      IsSeparableSub (ChannelAmplification (diagPinchMap w) r X) := by
  intro r X hX
  have h_eb := isEntanglementBreaking_diagPinchMap w hw
  rw [isEntanglementBreaking_iff_lib] at h_eb
  exact h_eb.2 r X hX

/-- **Diagonal Pinching Map Choi State (Native Library Consumer):**
For any nonnegative weights `w : Fin d → ℝ`, the Choi matrix of `diagPinchMap w` is `IsSeparableSub`. -/
theorem diagPinchMap_choi_isSeparableSub_lib {d : ℕ} (w : Fin d → ℝ) (hw : ∀ k, 0 ≤ w k) :
    IsSeparableSub (ChoiMatrix (diagPinchMap w)) := by
  have h_eb := isEntanglementBreaking_diagPinchMap w hw
  rw [isEntanglementBreaking_iff_choi_isSeparableSub] at h_eb
  exact h_eb

/-- **Trace-Replacement Map Entanglement Breaking (Native Library Consumer):**
For any positive semidefinite target state `σ`, `traceReplaceMap σ` maps every positive semidefinite
operator under `ChannelAmplification` into `IsSeparableSub`. -/
theorem traceReplaceMap_entanglementBreaking_lib {d : ℕ} (σ : Operator d) (hσ : σ.PosSemidef) :
    ∀ (r : ℕ) (X : Matrix (Fin r × Fin d) (Fin r × Fin d) ℂ),
      X.PosSemidef →
      IsSeparableSub (ChannelAmplification (traceReplaceMap σ) r X) := by
  intro r X hX
  have h_eb := isEntanglementBreaking_traceReplaceMap σ hσ
  rw [isEntanglementBreaking_iff_lib] at h_eb
  exact h_eb.2 r X hX

/-- **Trace-Replacement Map Choi State (Native Library Consumer):**
For any positive semidefinite target state `σ`, the Choi matrix of `traceReplaceMap σ` is `IsSeparableSub`. -/
theorem traceReplaceMap_choi_isSeparableSub_lib {d : ℕ} (σ : Operator d) (hσ : σ.PosSemidef) :
    IsSeparableSub (ChoiMatrix (traceReplaceMap σ)) := by
  have h_eb := isEntanglementBreaking_traceReplaceMap σ hσ
  rw [isEntanglementBreaking_iff_choi_isSeparableSub] at h_eb
  exact h_eb

/-- **Arbitrary-Basis Pinching Map Entanglement Breaking (Native Library Consumer):**
For any operators `U, V` and nonnegative weights `w`, `basisPinchMap U V w` maps every positive semidefinite
operator under `ChannelAmplification` into `IsSeparableSub`. -/
theorem basisPinchMap_entanglementBreaking_lib {d : ℕ}
    (U V : Operator d) (w : Fin d → ℝ) (hw : ∀ k, 0 ≤ w k) :
    ∀ (r : ℕ) (X : Matrix (Fin r × Fin d) (Fin r × Fin d) ℂ),
      X.PosSemidef →
      IsSeparableSub (ChannelAmplification (basisPinchMap U V w) r X) := by
  intro r X hX
  have h_eb := isEntanglementBreaking_basisPinchMap U V w hw
  rw [isEntanglementBreaking_iff_lib] at h_eb
  exact h_eb.2 r X hX

/-- **Arbitrary-Basis Pinching Map Choi State (Native Library Consumer):**
For any operators `U, V` and nonnegative weights `w`, the Choi matrix of `basisPinchMap U V w` is `IsSeparableSub`. -/
theorem basisPinchMap_choi_isSeparableSub_lib {d : ℕ}
    (U V : Operator d) (w : Fin d → ℝ) (hw : ∀ k, 0 ≤ w k) :
    IsSeparableSub (ChoiMatrix (basisPinchMap U V w)) := by
  have h_eb := isEntanglementBreaking_basisPinchMap U V w hw
  rw [isEntanglementBreaking_iff_choi_isSeparableSub] at h_eb
  exact h_eb

/-- **Measure-and-Prepare Channel Entanglement Breaking (Native Library Consumer):**
For any Kraus measurement operators `K` and positive semidefinite target states `σ`,
`measurePrepareMap K σ` maps every positive semidefinite operator under `ChannelAmplification`
into `IsSeparableSub`. -/
theorem measurePrepareMap_entanglementBreaking_lib {d : ℕ} {k : ℕ}
    (K : Fin k → Operator d) (σ : Fin k → Operator d)
    (hσ : ∀ i, (σ i).PosSemidef) :
    ∀ (r : ℕ) (X : Matrix (Fin r × Fin d) (Fin r × Fin d) ℂ),
      X.PosSemidef →
      IsSeparableSub (ChannelAmplification (measurePrepareMap K σ) r X) := by
  intro r X hX
  have h_eb := isEntanglementBreaking_measurePrepareMap K σ hσ
  rw [isEntanglementBreaking_iff_lib] at h_eb
  exact h_eb.2 r X hX

/-- **Measure-and-Prepare Channel Choi State (Native Library Consumer):**
For any Kraus measurement operators `K` and positive semidefinite target states `σ`,
the Choi matrix of `measurePrepareMap K σ` is `IsSeparableSub`. -/
theorem measurePrepareMap_choi_isSeparableSub_lib {d : ℕ} {k : ℕ}
    (K : Fin k → Operator d) (σ : Fin k → Operator d)
    (hσ : ∀ i, (σ i).PosSemidef) :
    IsSeparableSub (ChoiMatrix (measurePrepareMap K σ)) := by
  have h_eb := isEntanglementBreaking_measurePrepareMap K σ hσ
  rw [isEntanglementBreaking_iff_choi_isSeparableSub] at h_eb
  exact h_eb

/-- **Surrounded PPT Composition Chains (Native Library Consumer):**
For any dimension `d ≥ 2`, any family of `2 * (d - 1)` PPT maps `Φ` on `Operator d`,
and any completely positive pre- and post-processing maps `Ψ_pre, Ψ_post`,
the surrounded composition `(Ψ_post ∘ₗ compList (List.ofFn Φ)) ∘ₗ Ψ_pre` maps every
positive semidefinite operator under `ChannelAmplification` into `IsSeparableSub`. -/
theorem compose_ppt_maps_surrounded_entanglementBreaking_lib (d : ℕ) (hd : 2 ≤ d)
    (Φ : Fin (2 * (d - 1)) → Module.End ℂ (Operator d))
    (hΦ : ∀ i, IsPPT (Φ i))
    (Ψ_post Ψ_pre : Module.End ℂ (Operator d))
    (hpost : CompletelyPositive Ψ_post)
    (hpre : CompletelyPositive Ψ_pre) :
    ∀ (r : ℕ) (X : Matrix (Fin r × Fin d) (Fin r × Fin d) ℂ),
      X.PosSemidef →
      IsSeparableSub (ChannelAmplification ((Ψ_post ∘ₗ compList (List.ofFn Φ)) ∘ₗ Ψ_pre) r X) := by
  intro r X hX
  have h_eb := compose_ppt_maps_surrounded_entanglementBreaking d hd Φ
    (fun i => (isPPT_iff_isPPTMap _).mp (hΦ i))
    Ψ_post Ψ_pre
    ((isCompletelyPositive_iff_completelyPositive _).mpr hpost)
    ((isCompletelyPositive_iff_completelyPositive _).mpr hpre)
  rw [isEntanglementBreaking_iff_lib] at h_eb
  exact h_eb.2 r X hX

/-- **Surrounded PPT Composition Chains Choi State (Native Library Consumer):**
For any dimension `d ≥ 2`, any family of `2 * (d - 1)` PPT maps `Φ` on `Operator d`,
and any completely positive pre- and post-processing maps `Ψ_pre, Ψ_post`,
the Choi matrix of the surrounded composition is `IsSeparableSub`. -/
theorem compose_ppt_maps_surrounded_choi_isSeparableSub (d : ℕ) (hd : 2 ≤ d)
    (Φ : Fin (2 * (d - 1)) → Module.End ℂ (Operator d))
    (hΦ : ∀ i, IsPPT (Φ i))
    (Ψ_post Ψ_pre : Module.End ℂ (Operator d))
    (hpost : CompletelyPositive Ψ_post)
    (hpre : CompletelyPositive Ψ_pre) :
    IsSeparableSub (ChoiMatrix ((Ψ_post ∘ₗ compList (List.ofFn Φ)) ∘ₗ Ψ_pre)) := by
  have h_eb := compose_ppt_maps_surrounded_entanglementBreaking d hd Φ
    (fun i => (isPPT_iff_isPPTMap _).mp (hΦ i))
    Ψ_post Ψ_pre
    ((isCompletelyPositive_iff_completelyPositive _).mpr hpost)
    ((isCompletelyPositive_iff_completelyPositive _).mpr hpre)
  rw [isEntanglementBreaking_iff_choi_isSeparableSub] at h_eb
  exact h_eb

/-! ## Bridge 8: Schmidt-Number Conic Bounds, Reference-Limited Collapse, and Heterogeneous Interleaving -/

/-- **Separability Cone Equivalence with Schmidt-Number-One Cone:**
A bipartite operator `X` is subnormalized separable (`IsSeparableSub X`) if and only if
it has Schmidt number at most one (`HasSchmidtNumberLE 1 X`). -/
theorem isSeparableSub_iff_hasSchmidtNumberLE_one
    {k d : ℕ} (X : Matrix (Fin k × Fin d) (Fin k × Fin d) ℂ) :
    IsSeparableSub X ↔ HasSchmidtNumberLE 1 X := by
  rw [← isSeparable_iff_isSeparableSub]
  exact isSeparable_iff_hasSchmidtNumberLE_one

/-- **Reference-Dimension-Limited Separability Collapse (Native Library Consumer):**
For any reference dimension `k ≥ 1` and system dimension `d`, the composition of only
`2 * (k - 1)` PPT maps on `Operator d` adjoined to a `k`-dimensional reference register
via `ChannelAmplification` maps every positive semidefinite operator into `IsSeparableSub`. -/
theorem isSeparableSub_amplification_comp_ppt_maps_of_ref_le_lib
    (k d : ℕ) (hk : 1 ≤ k)
    (Φ : Fin (2 * (k - 1)) → Module.End ℂ (Operator d))
    (hΦ : ∀ i, IsPPT (Φ i))
    (X : Matrix (Fin k × Fin d) (Fin k × Fin d) ℂ)
    (hX : X.PosSemidef) :
    IsSeparableSub (ChannelAmplification (compList (List.ofFn Φ)) k X) := by
  have h_sep := isSeparable_refMap_comp_ppt_maps_of_ref_le k d hk Φ
    (fun i => (isPPT_iff_isPPTMap _).mp (hΦ i)) X hX
  rw [refMap_eq_channelAmplification_apply] at h_sep
  exact (isSeparable_iff_isSeparableSub _).mp h_sep

/-- **Heterogeneous Interleaved PPT-CP Composition (Native Library Consumer):**
For any dimension `d ≥ 2`, any sequence of `2 * (d - 1)` PPT maps `Φ_i` and arbitrary
completely positive maps `S_i` on `Operator d`, the interleaved composition
`compList (List.ofFn fun i => Φ i ∘ₗ S i)` maps every positive semidefinite operator
under `ChannelAmplification` into `IsSeparableSub`. -/
theorem compose_heterogeneous_ppt_interleaved_entanglementBreaking_lib
    (d : ℕ) (hd : 2 ≤ d)
    (Φ : Fin (2 * (d - 1)) → Module.End ℂ (Operator d))
    (hΦ : ∀ i, IsPPT (Φ i))
    (S : Fin (2 * (d - 1)) → Module.End ℂ (Operator d))
    (hS : ∀ i, CompletelyPositive (S i)) :
    ∀ (r : ℕ) (X : Matrix (Fin r × Fin d) (Fin r × Fin d) ℂ),
      X.PosSemidef →
      IsSeparableSub (ChannelAmplification (compList (List.ofFn fun i => Φ i ∘ₗ S i)) r X) := by
  intro r X hX
  have h_eb := compose_heterogeneous_ppt_interleaved_entanglementBreaking d hd Φ
    (fun i => (isPPT_iff_isPPTMap _).mp (hΦ i)) S
    (fun i => (isCompletelyPositive_iff_completelyPositive _).mpr (hS i))
  rw [isEntanglementBreaking_iff_lib] at h_eb
  exact h_eb.2 r X hX

/-- **Heterogeneous Interleaved PPT-CP Composition Choi State (Native Library Consumer):**
For any dimension `d ≥ 2`, any sequence of `2 * (d - 1)` PPT maps `Φ_i` and arbitrary
completely positive maps `S_i` on `Operator d`, the Choi matrix of the interleaved
composition `compList (List.ofFn fun i => Φ i ∘ₗ S i)` is `IsSeparableSub`. -/
theorem compose_heterogeneous_ppt_interleaved_choi_isSeparableSub_lib
    (d : ℕ) (hd : 2 ≤ d)
    (Φ : Fin (2 * (d - 1)) → Module.End ℂ (Operator d))
    (hΦ : ∀ i, IsPPT (Φ i))
    (S : Fin (2 * (d - 1)) → Module.End ℂ (Operator d))
    (hS : ∀ i, CompletelyPositive (S i)) :
    IsSeparableSub (ChoiMatrix (compList (List.ofFn fun i => Φ i ∘ₗ S i))) := by
  have h_eb := compose_heterogeneous_ppt_interleaved_entanglementBreaking d hd Φ
    (fun i => (isPPT_iff_isPPTMap _).mp (hΦ i)) S
    (fun i => (isCompletelyPositive_iff_completelyPositive _).mpr (hS i))
  rw [isEntanglementBreaking_iff_choi_isSeparableSub] at h_eb
  exact h_eb

/-! ## Bridge 9: Peres–Horodecki Criterion, CP Chain Absorption, and All-Power Thresholds -/

/-- **Peres–Horodecki Positive Partial Transpose for Separable States (Native Library Consumer):**
Every subnormalized separable bipartite operator has a positive semidefinite partial transpose. -/
theorem isSeparableSub_partialTranspose_posSemidef_lib {k d : ℕ}
    (X : Matrix (Fin k × Fin d) (Fin k × Fin d) ℂ)
    (hX : IsSeparableSub X) :
    (PartialTranspose X).PosSemidef := by
  have h_sep : Qatlib.Foundations.PPTMatrix.OperatorCones.IsSeparable X :=
    (isSeparable_iff_isSeparableSub X).mpr hX
  have h_pt : (partialTransposeRef X).PosSemidef :=
    IsSeparable.posSemidef_partialTransposeRef h_sep
  exact (posSemidef_partialTransposeRef_iff_posSemidef_partialTranspose X).mp h_pt

/-- **Universal EB ⊆ PPT Cone Inclusion (Native Library Consumer):**
If `T : Operator d →ₗ[ℂ] Operator d` satisfies the native entanglement-breaking predicate,
then `IsPPT T`. -/
theorem isPPT_of_isEntanglementBreaking_lib {d : ℕ}
    (T : Operator d →ₗ[ℂ] Operator d)
    (hT : CompletelyPositive T ∧
      ∀ (r : ℕ) (X : Matrix (Fin r × Fin d) (Fin r × Fin d) ℂ),
        X.PosSemidef → IsSeparableSub (ChannelAmplification T r X)) :
    IsPPT T := by
  have h_eb : IsEntanglementBreaking T :=
    (isEntanglementBreaking_iff_lib T).mpr hT
  exact (isPPT_iff_isPPTMap T).mpr (IsEntanglementBreaking.isPPTMap h_eb)

/-- **Multi-Step Ideal Absorption in CP Chains (Native Library Consumer):**
For any finite sequence `Φ : Fin N → Module.End ℂ (Operator d)` of completely positive maps
in which at least one map `Φ i₀` is entanglement breaking, the composite channel
`compList (List.ofFn Φ)` maps every positive semidefinite operator under `ChannelAmplification`
into `IsSeparableSub`. -/
theorem isEntanglementBreaking_ofFn_of_exists_lib {d N : ℕ}
    (Φ : Fin N → Module.End ℂ (Operator d))
    (hCP : ∀ i, CompletelyPositive (Φ i))
    (hEB : ∃ i₀ : Fin N, IsEntanglementBreaking (Φ i₀)) :
    ∀ (r : ℕ) (X : Matrix (Fin r × Fin d) (Fin r × Fin d) ℂ),
      X.PosSemidef →
      IsSeparableSub (ChannelAmplification (compList (List.ofFn Φ)) r X) := by
  intro r X hX
  have h_eb := isEntanglementBreaking_ofFn_of_exists Φ
    (fun i => (isCompletelyPositive_iff_completelyPositive _).mpr (hCP i))
    hEB
  rw [isEntanglementBreaking_iff_lib] at h_eb
  exact h_eb.2 r X hX

/-- **Universal All-Power Entanglement-Breaking Threshold (Native Library Consumer):**
For any dimension `d ≥ 2`, any PPT map `T` on `Operator d`, and any exponent `M ≥ 2 * (d - 1)`,
`T ^ M` maps every bipartite positive semidefinite operator under `ChannelAmplification` into `IsSeparableSub`. -/
theorem isEntanglementBreaking_pow_of_le_lib (d : ℕ) (hd : 2 ≤ d)
    (T : Module.End ℂ (Operator d)) (hT : IsPPT T)
    (M : ℕ) (hM : 2 * (d - 1) ≤ M) :
    ∀ (r : ℕ) (X : Matrix (Fin r × Fin d) (Fin r × Fin d) ℂ),
      X.PosSemidef →
      IsSeparableSub (ChannelAmplification (T ^ M) r X) := by
  intro r X hX
  have h_eb := isEntanglementBreaking_pow_of_le d hd T ((isPPT_iff_isPPTMap _).mp hT) M hM
  rw [isEntanglementBreaking_iff_lib] at h_eb
  exact h_eb.2 r X hX

/-- **Universal All-Power Choi State Separability (Native Library Consumer):**
For any dimension `d ≥ 2`, any PPT map `T` on `Operator d`, and any exponent `M ≥ 2 * (d - 1)`,
the Choi matrix of `T ^ M` is `IsSeparableSub`. -/
theorem choi_pow_isSeparableSub_of_le_lib (d : ℕ) (hd : 2 ≤ d)
    (T : Module.End ℂ (Operator d)) (hT : IsPPT T)
    (M : ℕ) (hM : 2 * (d - 1) ≤ M) :
    IsSeparableSub (ChoiMatrix (T ^ M)) := by
  have h_eb := isEntanglementBreaking_pow_of_le d hd T ((isPPT_iff_isPPTMap _).mp hT) M hM
  rw [isEntanglementBreaking_iff_choi_isSeparableSub] at h_eb
  exact h_eb

end Qatlib.Papers.PPTCompose26.Composition
