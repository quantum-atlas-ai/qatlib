/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.ResourceIff.FourFixedCorrectionsMaxEntConverseStat
import Qatlib.Concepts.QuditTeleport.ResourceIff.FourFixedCorrectionsMaxEntConverse
import Qatlib.Concepts.QuditTeleport.ResourceIff.ConverseTools

/-!
# The four-correction marginal converse and positivity

`fourFixedCorrectionsMaxEntConverse` proves the receiver-marginal converse for positive
semidefinite resources using branch positivity and no-signalling. The proof gives the maximally
mixed receiver marginal required by perfect teleportation with fixed unitary corrections.

An explicit matrix `indefiniteResource` produces the identity channel with Bell measurements and
Pauli corrections but is not positive semidefinite, disproving the unrestricted contract. The
resource setting is the qubit teleportation protocol of [BennettEtAl1993Teleportation].

## Main statements

* `fourFixedCorrectionsMaxEntConverse`: Every positive semidefinite resource enabling four fixed
  unitary corrections has receiver marginal `(1 / 2) • 1`. See [Bennett et al., 1993, Eq.
  (9)][BennettEtAl1993Teleportation].
* `fourFixedCorrectionsMaxEntConverse_impossible`: The receiver-marginal converse without a
  resource-positivity hypothesis is false.
* `indefiniteResource_not_positive`: The matrix `indefiniteResource` is not positive
  semidefinite.

## References

* [Bennett et al., 1993][BennettEtAl1993Teleportation]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.FiniteLocc.LOCCProgram

namespace Qatlib.Concepts.QuditTeleport.ResourceIff
open Matrix
open scoped Classical BigOperators ComplexOrder
set_option maxRecDepth 8192
set_option maxHeartbeats 0

/-- The four Bell-state projectors as matrices indexed by `Fin 4`. -/
private noncomputable def bellProjectorRaw (s : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ :=
  ![!![1/2,0,0,1/2; 0,0,0,0; 0,0,0,0; 1/2,0,0,1/2],
    !![1/2,0,0,-1/2; 0,0,0,0; 0,0,0,0; -1/2,0,0,1/2],
    !![0,0,0,0; 0,1/2,1/2,0; 0,1/2,1/2,0; 0,0,0,0],
    !![0,0,0,0; 0,1/2,-1/2,0; 0,-1/2,1/2,0; 0,0,0,0]] s

/-- The Bell-state projectors reindexed by pairs of qubit basis indices. -/
private noncomputable def bellProjectors (s : Fin 4) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (bellProjectorRaw s).submatrix finProdFinEquiv finProdFinEquiv

/-- The four correction matrices `1`, `Z`, `X`, and `Z * X` in the chosen Bell-outcome order. -/
private noncomputable def pauliCorrections (s : Fin 4) : Operator 2 :=
  ![!![1,0;0,1], !![1,0;0,-1], !![0,1;1,0], !![0,1;-1,0]] s

/-- The two-qubit matrix with entries `1` at `(00, 00)` and `1 / 2` at `(00, 11)` and `(11,
00)`, and zero elsewhere. -/
private noncomputable def indefiniteResource : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  ( !![1,0,0,1/2; 0,0,0,0; 0,0,0,0; 1/2,0,0,0] : Matrix (Fin 4) (Fin 4) ℂ).submatrix
    finProdFinEquiv finProdFinEquiv

/-- Each of the four chosen Pauli correction matrices is unitary. -/
private theorem pauliCorrections_unitary (s : Fin 4) :
    pauliCorrections s ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  ext i j
  fin_cases s <;> fin_cases i <;> fin_cases j <;>
    norm_num [pauliCorrections, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, Matrix.one_apply]

/-- The Bell projector Kraus family, tensored with the identity on Bob's qubit, satisfies the
completeness relation. -/
private theorem bellProjectors_complete :
    ∑ s : Fin 4, (TensorGate (bellProjectors s) (1 : Operator 2))ᴴ *
      TensorGate (bellProjectors s) (1 : Operator 2) = 1 := by
  ext ⟨a,b⟩ ⟨c,d⟩
  rcases a with ⟨a₁,a₂⟩
  rcases c with ⟨c₁,c₂⟩
  fin_cases a₁ <;> fin_cases a₂ <;> fin_cases b <;>
    fin_cases c₁ <;> fin_cases c₂ <;> fin_cases d <;>
    norm_num [bellProjectors, bellProjectorRaw, TensorGate, Matrix.kroneckerMap_apply,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_four, Matrix.one_apply, Matrix.cons_val_two, Matrix.cons_val_three, map_ofNat,
      finProdFinEquiv]

/-- Bell measurement with `indefiniteResource` and the chosen Pauli corrections recovers every
input operator after summing branches. -/
private theorem indefiniteResource_channel (ρ : Operator 2) :
    ∑ s : Fin 4, pauliCorrections s * bobBranchMarginal bellProjectors
      indefiniteResource s ρ * (pauliCorrections s)ᴴ = ρ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliCorrections, bobBranchMarginal, PartialTrace, relabelGate,
      bobFirstEquiv, TensorGate, Matrix.kroneckerMap_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.submatrix_apply, Matrix.reindex_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_four,
      bellProjectors, bellProjectorRaw, indefiniteResource, finProdFinEquiv,
      Matrix.one_apply, Matrix.vecMul, dotProduct, Matrix.add_apply, Matrix.cons_val_two,
      Matrix.cons_val_three, map_ofNat] <;> ring

/-- The receiver-marginal converse without a resource-positivity hypothesis is false. -/
theorem fourFixedCorrectionsMaxEntConverse_impossible :
    ¬ FourFixedCorrectionsMaxEntConverseCore := by
  intro h
  have ht : FourFixedCorrectionsTeleport bellProjectors pauliCorrections
      indefiniteResource :=
    ⟨pauliCorrections_unitary, bellProjectors_complete, indefiniteResource_channel⟩
  have he := congrArg (fun A : Operator 2 => A 0 0)
    (h bellProjectors pauliCorrections indefiniteResource ht)
  norm_num [PartialTrace, relabelGate, indefiniteResource, Matrix.submatrix_apply,
    Matrix.reindex_apply, Fin.sum_univ_two, finProdFinEquiv, Matrix.one_apply] at he

/-- Every positive semidefinite resource enabling four fixed unitary corrections has receiver
marginal `(1 / 2) • 1`. See [Bennett et al., 1993, Eq. (9)][BennettEtAl1993Teleportation]. -/
theorem fourFixedCorrectionsMaxEntConverse : FourFixedCorrectionsMaxEntConverse := by
  intro K U ω hω htele
  obtain ⟨hU, hK, hsum⟩ := htele
  let F := fun s : Fin 4 => fun ρ : Operator 2 => U s * bobBranchMarginal K ω s ρ * (U s)ᴴ
  have hadd : ∀ s A B, F s (A + B) = F s A + F s B := by
    intro s A B
    simp only [F, bobBranchMarginal_add, Matrix.mul_add, Matrix.add_mul]
  have hsmul : ∀ s (c : ℂ) A, F s (c • A) = c • F s A := by
    intro s c A
    simp only [F, bobBranchMarginal_smul, Matrix.mul_smul, Matrix.smul_mul]
  have hpos : ∀ s (A : Operator 2), A.PosSemidef → (F s A).PosSemidef := by
    intro s A hA
    have h := (bobBranchMarginal_positive K ω hω s A hA).conjTranspose_mul_mul_same (U s)ᴴ
    simpa only [Matrix.conjTranspose_conjTranspose] using h
  have hscalar := positive_qubit_family_scalar_one 4 F hadd hsmul hpos hsum
  have hraw (s : Fin 4) : bobBranchMarginal K ω s 1 = F s 1 := by
    obtain ⟨a, ha⟩ := hscalar s
    have hu : (U s)ᴴ * U s = 1 := by
      simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp (hU s)
    have hundo : (U s)ᴴ * F s 1 * U s = bobBranchMarginal K ω s 1 := by
      have he : ((U s)ᴴ * U s) * bobBranchMarginal K ω s 1 * ((U s)ᴴ * U s) =
          bobBranchMarginal K ω s 1 := by rw [hu, Matrix.one_mul, Matrix.mul_one]
      simpa only [F, Matrix.mul_assoc] using he
    rw [ha] at hundo
    have hc : (U s)ᴴ * (a • (1 : Operator 2)) * U s = a • (1 : Operator 2) := by
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hu]
    rw [hc] at hundo
    exact hundo.symm.trans ha.symm
  have hb : (∑ s, bobBranchMarginal K ω s 1) = (1 : Operator 2) := by
    simp_rw [hraw]
    exact hsum 1
  have hn := bobBranchMarginal_no_signalling K ω hK (1 : Operator 2)
  rw [hb, show Matrix.trace (1 : Operator 2) = (2 : ℂ) by simp] at hn
  ext i j
  have he := congrArg (fun A : Operator 2 => A i j) hn
  simp only [Matrix.smul_apply, smul_eq_mul] at he ⊢
  linear_combination -he / 2

/-- The matrix `indefiniteResource` is not positive semidefinite. -/
theorem indefiniteResource_not_positive : ¬ indefiniteResource.PosSemidef := by
  intro h
  let v : Fin 2 × Fin 2 → ℂ := fun x => (![1, 0, 0, -2] : Fin 4 → ℂ) (finProdFinEquiv x)
  have hh := h.re_dotProduct_nonneg v
  norm_num [v, indefiniteResource, Matrix.mulVec, dotProduct, Matrix.submatrix_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two, finProdFinEquiv, Matrix.cons_val_two,
    Matrix.cons_val_three, map_ofNat] at hh

end Qatlib.Concepts.QuditTeleport.ResourceIff
