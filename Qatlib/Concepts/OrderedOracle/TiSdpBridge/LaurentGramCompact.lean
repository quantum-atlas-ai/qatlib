/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedOracle.TiSdpBridge.LaurentGram
import QuantumInfo.ForMathlib.HermitianMat.Inner

/-!
# Compactness of Gram representation sets

The Lean declarations prove continuity of generalized traces and compactness of the positive
semidefinite Hermitian matrices with prescribed generalized traces. They then obtain a matrix
maximizing any chosen diagonal entry in that set. The finite dimensional positivity and trace
bounds belong to the matrix analysis setting of [Bhatia1997].

## Main statements

* `continuous_genTrace`: each generalized trace depends continuously on the matrix.
* `isCompact_gramFace`: the positive semidefinite set with fixed generalized traces is compact.
* `exists_maximal_gram`: a prescribed diagonal entry attains its maximum among matrices with the
  same generalized traces.

## References

* [Bhatia, 1997][Bhatia1997]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace Qatlib.Concepts.OrderedOracle.TiSdpBridge
open scoped Classical BigOperators ComplexOrder

variable {n : ℕ}

/-- For each integer offset, the generalized trace is a continuous function of the matrix
entries. -/
theorem continuous_genTrace (j : ℤ) : Continuous (fun A : Matrix (Fin n) (Fin n) ℂ => genTrace A j) := by
  unfold genTrace
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro i' _
  by_cases h : ((i' : ℕ) : ℤ)-((i : ℕ) : ℤ)=j
  · simp only [h,if_true]
    exact (continuous_apply i').comp (continuous_apply i)
  · simp only [h,if_false]
    exact continuous_const

/-- The set of nonnegative Hermitian matrices having the same generalized traces as `A` is
closed. -/
theorem isClosed_gramFace (A : Matrix (Fin n) (Fin n) ℂ) :
    IsClosed {B : HermitianMat (Fin n) ℂ | 0≤B ∧ ∀ j : ℤ,genTrace B.mat j=genTrace A j} := by
  have hc : IsClosed {B : HermitianMat (Fin n) ℂ | ∀ j : ℤ,genTrace B.mat j=genTrace A j} := by
    rw [Set.setOf_forall]
    apply isClosed_iInter
    intro j
    exact isClosed_eq ((continuous_genTrace j).comp HermitianMat.continuous_mat) continuous_const
  exact HermitianMat.isClosed_nonneg.inter hc

/-- The set of nonnegative Hermitian matrices having the same generalized traces as `A` is
compact. -/
theorem isCompact_gramFace (A : Matrix (Fin n) (Fin n) ℂ) :
    IsCompact {B : HermitianMat (Fin n) ℂ | 0≤B ∧ ∀ j : ℤ,genTrace B.mat j=genTrace A j} := by
  have hs : {B : HermitianMat (Fin n) ℂ | 0≤B ∧ ∀ j : ℤ,genTrace B.mat j=genTrace A j}⊆
      Set.Icc 0 ((A.trace.re : ℝ) • (1 : HermitianMat (Fin n) ℂ)) := by
    intro B hB
    refine ⟨hB.1,?_⟩
    have ht : B.trace=A.trace.re := by
      have h := congrArg Complex.re (hB.2 0)
      simpa only [genTrace_zero,HermitianMat.trace_eq_re_trace] using! h
    simpa only [ht] using HermitianMat.le_trace_smul_one hB.1
  exact isCompact_Icc.of_isClosed_subset (isClosed_gramFace A) hs

/-- For a positive semidefinite matrix `A` and a chosen index `i`, there is a positive
semidefinite matrix with the same generalized traces whose `i`th diagonal entry is maximal
among all such matrices. Its chosen entry is at least `A i i`. -/
theorem exists_maximal_gram (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosSemidef)
    (i : Fin n) :
    ∃ B : Matrix (Fin n) (Fin n) ℂ,B.PosSemidef ∧ (∀ j : ℤ,genTrace B j=genTrace A j) ∧
      A i i≤B i i ∧
      ∀ C : Matrix (Fin n) (Fin n) ℂ,C.PosSemidef → (∀ j : ℤ,genTrace C j=genTrace A j) → C i i≤B i i := by
  let AH : HermitianMat (Fin n) ℂ := ⟨A,hA.isHermitian⟩
  have hmem : AH∈{B : HermitianMat (Fin n) ℂ | 0≤B ∧ ∀ j : ℤ,genTrace B.mat j=genTrace A j} :=
    ⟨HermitianMat.zero_le_iff.mpr hA,fun _ => rfl⟩
  have hc : Continuous (fun B : HermitianMat (Fin n) ℂ => (B.mat i i).re) :=
    Complex.continuous_re.comp ((continuous_apply_apply i i).comp HermitianMat.continuous_mat)
  obtain ⟨B,hB,hmax⟩ := (isCompact_gramFace A).exists_isMaxOn ⟨AH,hmem⟩ hc.continuousOn
  have hBpsd : B.mat.PosSemidef := HermitianMat.zero_le_iff.mp hB.1
  have him (C : Matrix (Fin n) (Fin n) ℂ) (hC : C.PosSemidef) : (C i i).im=0 :=
    (Complex.nonneg_iff.mp (hC.diag_nonneg (i := i))).2.symm
  have hle (C : Matrix (Fin n) (Fin n) ℂ) (hC : C.PosSemidef)
      (htrace : ∀ j : ℤ,genTrace C j=genTrace A j) : C i i≤B.mat i i := by
    apply Complex.le_def.mpr
    let CH : HermitianMat (Fin n) ℂ := ⟨C,hC.isHermitian⟩
    have hCH : CH∈{B : HermitianMat (Fin n) ℂ | 0≤B ∧ ∀ j : ℤ,genTrace B.mat j=genTrace A j} :=
      ⟨HermitianMat.zero_le_iff.mpr hC,htrace⟩
    refine ⟨hmax hCH,?_⟩
    rw [him C hC,him B.mat hBpsd]
  exact ⟨B.mat,hBpsd,hB.2,hle A hA (fun _ => rfl),hle⟩
end Qatlib.Concepts.OrderedOracle.TiSdpBridge
