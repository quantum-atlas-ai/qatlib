/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QPCAAssume18.ClassicalPca.Budget

/-!
# A paid small-SVD model for PCA

Packages exact spectral output on the small matrix with an explicit nonnegative cubic work
bound. The resulting `pcaPaidOutput` agrees with the canonical lifted output, while
`pcaPaidPreprocess` accounts for SVD and oracle work in the classical PCA model of [Tang2021].

## Main statements

* `pcaPaidOutput_eq`: The output of the supplied small-SVD primitive equals the canonical
  `pcaOutput`.
* `pcaPaidPreprocess_le`: The paid preprocessing ledger is at most `pcaPreprocessWork q T`
  [Tang2021].

## References

* [Tang, 2021][Tang2021]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace Qatlib.Papers.QPCAAssume18.ClassicalPca
open Matrix
open Qatlib.Concepts.SketchArith.SketchBuild

/-- A small-matrix SVD primitive returning the canonical squared singular values and left
singular vectors, with nonnegative recorded work at most `q^3`. -/
structure PcaSmallSvdPrimitive (q : ℕ) where
  run : Matrix (Fin q) (Fin q) ℂ → (Fin q→ℝ) × (Fin q→EuclideanSpace ℂ (Fin q)) × ℝ
  values : ∀ W i,(run W).1 i=pcaSmallValue W i
  vectors : ∀ W i,(run W).2.1 i=pcaSmallVector W i
  cost_nonneg : ∀ W,0≤(run W).2.2
  cost_cubic : ∀ W,(run W).2.2≤(q:ℝ)^3

/-- The PCA output formed by lifting and rescaling the spectral data returned by the supplied
small-SVD primitive. -/
def pcaPaidOutput {q d : ℕ} (svd : PcaSmallSvdPrimitive q)
    (R : Matrix (Fin q) (Fin d) ℂ) (W : Matrix (Fin q) (Fin q) ℂ) (i : Fin q) :
    EuclideanSpace ℂ (Fin d) :=
  (Real.sqrt ((svd.run W).1 i):ℂ)⁻¹ • Rᴴ.toEuclideanLin ((svd.run W).2.1 i)

/-- The output of the supplied small-SVD primitive equals the canonical `pcaOutput`. -/
theorem pcaPaidOutput_eq {q d : ℕ} (svd : PcaSmallSvdPrimitive q)
    (R : Matrix (Fin q) (Fin d) ℂ) (W : Matrix (Fin q) (Fin q) ℂ) (i : Fin q) :
    pcaPaidOutput svd R W i=pcaOutput R W i := by
  rw [pcaPaidOutput,svd.values,svd.vectors]
  rfl

/-- The preprocessing work ledger combining the supplied SVD cost, small-entry queries,
column-energy reads, and explicit remaining access work. -/
def pcaPaidPreprocess {n d q : ℕ} (svd : PcaSmallSvdPrimitive q)
    (A : Matrix (Fin n) (Fin d) ℂ) (hA : 0<sketchSquared A) (hd : 0<d)
    (rows : Fin q→Fin n) (cols : Fin q→Fin d) (T : ℝ) : ℝ :=
  (svd.run (pcaSmallMatrix A hA hd q rows cols)).2.2 + T*(
    (((pcaSmallEntryTable A hA rows cols).map Prod.snd).sum:ℝ)+
    (∑ l,((pcaColumnEnergyRead A hA q rows (cols l)).2:ℝ))+3*(q:ℝ)^2+3*q+3)

/-- The paid preprocessing ledger is at most `pcaPreprocessWork q T` [Tang2021]. -/
theorem pcaPaidPreprocess_le {n d q : ℕ} (svd : PcaSmallSvdPrimitive q)
    (A : Matrix (Fin n) (Fin d) ℂ) (hA : 0<sketchSquared A) (hd : 0<d)
    (rows : Fin q→Fin n) (cols : Fin q→Fin d) (T : ℝ) :
    pcaPaidPreprocess svd A hA hd rows cols T≤pcaPreprocessWork q T := by
  unfold pcaPaidPreprocess pcaPreprocessWork pcaSmallSvdWork
  simp only [pcaSmallEntryTable_count,(pcaColumnEnergyRead_spec A hA q rows _).2,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_pow]
  have h := svd.cost_cubic (pcaSmallMatrix A hA hd q rows cols)
  nlinarith

end Qatlib.Papers.QPCAAssume18.ClassicalPca
