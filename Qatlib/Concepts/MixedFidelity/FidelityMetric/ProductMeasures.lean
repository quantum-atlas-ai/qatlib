/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.MixedFidelity.FidelityMetric.ClassicalCopies
public import QuantumInfo.Measurements.POVM

@[expose] public section


/-! # Independent finite product measurements

Actual tensor effects are positive and sum to the identity. On actual mixed
pi-product states, their Born probabilities factor into marginal probabilities.
Repeated measurements consume Physlib npow and the normalized sequence law,
including the empty family.
-/

set_option autoImplicit false
set_option warningAsError true
open scoped BigOperators RealInnerProductSpace MatrixOrder ComplexOrder
noncomputable section
namespace Qatlib.Concepts.MixedFidelity.FidelityMetric

/-- Finite dependent matrix products commute with the actual tensor carrier. -/
theorem piProd_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    {d : ι → Type*} [∀ i, Fintype (d i)]
    (A B : ∀ i, Matrix (d i) (d i) ℂ) :
    Matrix.piProd (fun i => A i * B i) = Matrix.piProd A * Matrix.piProd B := by
  ext a b
  simp only [Matrix.piProd, Matrix.of_apply, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  simp only [Finset.prod_mul_distrib]

set_option backward.isDefEq.respectTransparency false in
/-- The independent tensor POVM of a finite family of actual POVMs. -/
def independentPOVM {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X d : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (d i)]
    [∀ i, DecidableEq (d i)] (Λ : ∀ i, POVM (X i) (d i)) :
    POVM (∀ i, X i) (∀ i, d i) where
  mats x := ⟨Matrix.piProd (fun i => (Λ i).mats (x i) |>.mat),
    Matrix.IsHermitian.piProd (fun i => ((Λ i).mats (x i)).H)⟩
  nonneg x := by
    rw [HermitianMat.zero_le_iff]
    exact Matrix.PosSemidef.piProd (fun i =>
      HermitianMat.zero_le_iff.mp ((Λ i).nonneg (x i)))
  normalized := by
    ext a b
    rw [HermitianMat.mat_finset_sum, Matrix.sum_apply]
    change (∑ x : ∀ i, X i, ∏ i, ((Λ i).mats (x i)).mat (a i) (b i)) =
      (1 : Matrix (∀ i, d i) (∀ i, d i) ℂ) a b
    have heq := Fintype.prod_sum (fun i x => ((Λ i).mats x).mat (a i) (b i))
    rw [← heq]
    have h (i : ι) : (∑ x : X i, ((Λ i).mats x).mat (a i) (b i)) =
        if a i = b i then 1 else 0 := by
      have hh := congrArg (fun A : HermitianMat (d i) ℂ => A.mat (a i) (b i))
        (Λ i).normalized
      simpa only [HermitianMat.mat_finset_sum, Matrix.sum_apply,
        HermitianMat.mat_one, Matrix.one_apply] using hh
    simp_rw [h]
    by_cases hab : a = b
    · subst b
      simp
    · rw [Matrix.one_apply, ite_eq_right hab]
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hab
      exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

/-- The Born probabilities of independent POVMs on product states factorize. -/
theorem independentPOVM_measure_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X d : ι → Type*} [∀ i, Fintype (X i)]
    [∀ i, Fintype (d i)] [∀ i, DecidableEq (d i)]
    (Λ : ∀ i, POVM (X i) (d i)) (ρ : ∀ i, MState (d i)) (x : ∀ i, X i) :
    ((independentPOVM Λ).measure (MState.piProd ρ) x : ℝ) =
      ∏ i, ((Λ i).measure (ρ i) (x i) : ℝ) := by
  change inner ℝ ((independentPOVM Λ).mats x) (MState.piProd ρ).M =
    ∏ i, inner ℝ ((Λ i).mats (x i)) (ρ i).M
  apply Complex.ofReal_injective
  change (algebraMap ℝ ℂ) (inner ℝ ((independentPOVM Λ).mats x) (MState.piProd ρ).M) =
    (algebraMap ℝ ℂ) (∏ i, inner ℝ ((Λ i).mats (x i)) (ρ i).M)
  rw [map_prod]
  simp only [HermitianMat.inner_eq_trace_mul]
  change (Matrix.piProd (fun i => ((Λ i).mats (x i)).mat) *
    Matrix.piProd (fun i => (ρ i).m)).trace = _
  rw [← piProd_mul, Matrix.trace_piProd]
  rfl

/-- The actual n-copy tensor measurement of a single finite POVM. -/
def copyPOVM {X d : Type*} [Fintype X] [Fintype d] [DecidableEq d]
    (Λ : POVM X d) (n : ℕ) : POVM (Fin n → X) (Fin n → d) :=
  independentPOVM (fun _ : Fin n => Λ)

/-- Measuring the actual tensor power yields the normalized independent sequence law. -/
theorem copyPOVM_measure {X d : Type*} [Fintype X]
    [Fintype d] [DecidableEq d] (Λ : POVM X d) (ρ : MState d) (n : ℕ) :
    (copyPOVM Λ n).measure (ρ.npow n) = seqDist (Λ.measure ρ) n := by
  ext x
  exact independentPOVM_measure_apply (fun _ : Fin n => Λ) (fun _ => ρ) x

end Qatlib.Concepts.MixedFidelity.FidelityMetric
