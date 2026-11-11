/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Hom
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.FunLike.Equiv
import Mathlib.Basic.IsEmpty.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Init
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Function.Defs
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Nat
import Mathlib.Order.RelClasses
import Mathlib.Tactic
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

/-!
# Tensor amplitudes and orthogonal error components

`column` forms tensor-product amplitudes from a finite kernel, and `diagonalAmplitude` selects
their diagonal entries. For a lower-triangular kernel, equal total index mass forces every
off-diagonal amplitude to vanish; normalized rows and a diagonal lower bound give
`diagonal_tensor_budget`.

`tensor_decomposition` separates a histogram-supported diagonal contribution from `errorColumn`,
which is orthogonal to the histogram basis on a fixed mass layer. Gram identities are preserved
by tensor formation, supporting the framework of [TangWright2025].

## Main statements

* `diagonal_tensor_budget`: Diagonal tensor mass bound in terms of total index mass.
* `tensor_decomposition`: Diagonal histogram contribution plus error.
* `columns_gram_preserved`: Preservation of Gram equality by tensor amplitudes.

## References

* [Tang and Wright, 2025][TangWright2025]
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Matrix
namespace Qatlib.Foundations.MatrixAlgebra.FrameProject.Tensor

/-- The tensor amplitude `∏ i, K (h i) (y i)` for two finite index configurations. -/
def column {d q : ℕ} (K : Fin q → Fin q → ℂ) (h y : Fin d → Fin q) : ℂ :=
  ∏ i, K (h i) (y i)

/-- The diagonal tensor amplitude `column K h h`. -/
def diagonalAmplitude {d q : ℕ} (K : Fin q → Fin q → ℂ) (h : Fin d → Fin q) : ℂ :=
  column K h h

/-- For a lower-triangular kernel, a tensor amplitude vanishes if any output index exceeds its
corresponding input index. -/
theorem column_zero_of_increase {d q : ℕ} (K : Fin q → Fin q → ℂ)
    (hK : ∀k y, k<y → K k y=0) (h y : Fin d → Fin q)
    (hi : ∃i,h i<y i) : column K h y=0 := by
  obtain ⟨i,hi⟩ := hi
  exact Finset.prod_eq_zero (Finset.mem_univ i) (hK _ _ hi)

/-- Distinct finite configurations with equal total index mass have a coordinate where the
second configuration is strictly larger. -/
theorem exists_increase_of_equal_mass {d q : ℕ} (h y : Fin d → Fin q)
    (hm : ∑i,(h i:ℕ)=∑i,(y i:ℕ)) (hne : h≠y) : ∃i,h i<y i := by
  by_contra hn
  push Not at hn
  have hle : ∀i,(y i:ℕ)≤(h i:ℕ) := fun i => hn i
  have heq : ∀i,(y i:ℕ)=(h i:ℕ) := by
    intro i
    exact (Finset.sum_eq_sum_iff_of_le (fun j (_ : j ∈ Finset.univ) => hle j)).mp hm.symm i
        (Finset.mem_univ i)
  apply hne
  funext i
  exact Fin.ext (heq i).symm

/-- For a lower-triangular kernel, equal-mass tensor amplitudes equal the diagonal amplitude
when the configurations agree and vanish otherwise. -/
theorem column_same_mass {d q : ℕ} (K : Fin q → Fin q → ℂ)
    (hK : ∀k y, k<y → K k y=0) (h y : Fin d → Fin q)
    (hm : ∑i,(h i:ℕ)=∑i,(y i:ℕ)) :
    column K h y = if h=y then diagonalAmplitude K h else 0 := by
  by_cases heq : h=y
  · subst y
    simp [diagonalAmplitude]
  · rw [if_neg heq]
    exact column_zero_of_increase K hK h y (exists_increase_of_equal_mass h y hm heq)

/-- For finitely many real numbers in `[0, 1]`, one minus their product is at most the sum of
their individual deficits from one. -/
private theorem product_loss {J : Type*} [DecidableEq J] (b : J → ℝ) (s : Finset J)
    (hb0 : ∀i∈s,0≤b i) (hb1 : ∀i∈s,b i≤1) :
    1-∏i∈s,b i ≤ ∑i∈s,(1-b i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have hba0 := hb0 a (Finset.mem_insert_self a s)
    have hba1 := hb1 a (Finset.mem_insert_self a s)
    have hs0 : ∀i∈s,0≤b i := fun i hi => hb0 i (Finset.mem_insert_of_mem hi)
    have hs1 : ∀i∈s,b i≤1 := fun i hi => hb1 i (Finset.mem_insert_of_mem hi)
    have hprod1 : ∏i∈s,b i ≤ 1 := Finset.prod_le_one₀ (fun i hi => hs0 i hi) (fun i hi => hs1 i hi)
    have h := ih hs0 hs1
    nlinarith

/-- If every row has squared norm one, each diagonal entry has squared norm between zero and
one. -/
theorem diagonal_mass_bounds {q : ℕ} (K : Fin q → Fin q → ℂ)
    (hunit : ∀k,∑y,‖K k y‖^2=1) (k : Fin q) : 0≤‖K k k‖^2 ∧ ‖K k k‖^2≤1 := by
  refine ⟨sq_nonneg _,?_⟩
  have h := Finset.single_le_sum (f := fun y : Fin q => ‖K k y‖^2)
    (fun y (_ : y ∈ Finset.univ) => sq_nonneg _) (Finset.mem_univ k)
  simpa only [hunit] using h

/-- For a nonempty lower-triangular kernel with normalized rows, the squared norm of its first
diagonal entry is one. -/
theorem zero_diagonal_mass {q : ℕ} (hq : 0<q) (K : Fin q → Fin q → ℂ)
    (hK : ∀k y, k<y → K k y=0) (hunit : ∀k,∑y,‖K k y‖^2=1) :
    ‖K ⟨0,hq⟩ ⟨0,hq⟩‖^2=1 := by
  have h := hunit ⟨0,hq⟩
  have hz (y : Fin q) (hy : y≠⟨0,hq⟩) : K ⟨0,hq⟩ y=0 := by
    apply hK
    have : y.val≠0 := by intro h; apply hy; exact Fin.ext h
    exact this.bot_lt
  rw [Finset.sum_eq_single (⟨0,hq⟩:Fin q) (by
    intro y _ hy; rw [hz y hy]; simp) (by simp)] at h
  exact h

/-- For a lower-triangular kernel with normalized rows and diagonal squared norms at least `1 -
delta`, the diagonal tensor squared norm is at least one minus `delta` times the total input
index mass. -/
theorem diagonal_tensor_budget {d q : ℕ} (hq : 0<q) (K : Fin q → Fin q → ℂ)
    (hK : ∀k y, k<y → K k y=0) (hunit : ∀k,∑y,‖K k y‖^2=1)
    (delta : ℝ) (hd : 0≤delta) (hdiag : ∀k,1-delta≤‖K k k‖^2)
    (h : Fin d → Fin q) :
    1-delta*(∑i,(h i:ℕ):ℕ) ≤ ‖diagonalAmplitude K h‖^2 := by
  have hloss (i : Fin d) : 1-‖K (h i) (h i)‖^2 ≤ delta*(h i:ℕ) := by
    by_cases hi : (h i).val=0
    · have heq : h i=(⟨0,hq⟩:Fin q) := Fin.ext hi
      rw [heq,zero_diagonal_mass hq K hK hunit]
      simp
    · have hh : (1:ℝ)≤(h i:ℕ) := by exact_mod_cast (by omega : 1≤(h i).val)
      nlinarith [hdiag (h i)]
  have hprod := product_loss (fun i : Fin d => ‖K (h i) (h i)‖^2) Finset.univ
    (fun i _ => (diagonal_mass_bounds K hunit (h i)).1)
    (fun i _ => (diagonal_mass_bounds K hunit (h i)).2)
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hloss i)
  have hn : ‖diagonalAmplitude K h‖^2 = ∏i,‖K (h i) (h i)‖^2 := by
    simp only [diagonalAmplitude,column,norm_prod]
    rw [← Finset.prod_pow]
  rw [← Finset.mul_sum] at hs
  push_cast at hs ⊢
  rw [hn]
  nlinarith

/-- The matrix of tensor amplitudes whose input configurations are specified by `hist`. -/
def columns {H : Type*} {d q : ℕ} (K : Fin q → Fin q → ℂ)
    (hist : H → Fin d → Fin q) : Matrix H (Fin d → Fin q) ℂ :=
  fun h y => column K (hist h) y

/-- The matrix of coordinate indicator vectors supported on the configurations specified by
`hist`. -/
def histogramBasis {H : Type*} {d q : ℕ} (hist : H → Fin d → Fin q) :
    Matrix H (Fin d → Fin q) ℂ := fun h y => if hist h=y then 1 else 0

/-- The tensor amplitude matrix after subtracting each histogram-supported diagonal
contribution. -/
def errorColumn {H : Type*} {d q : ℕ} (K : Fin q → Fin q → ℂ)
    (hist : H → Fin d → Fin q) : Matrix H (Fin d → Fin q) ℂ :=
  fun h y => column K (hist h) y - diagonalAmplitude K (hist h) * histogramBasis hist h y

/-- An injective histogram map gives coordinate indicator vectors with pairwise inner products
equal to the Kronecker delta. -/
theorem histogramBasis_orthonormal {H : Type*} [DecidableEq H] {d q : ℕ}
    (hist : H → Fin d → Fin q) (hinj : Function.Injective hist) (a b : H) :
    (∑y, histogramBasis hist a y * star (histogramBasis hist b y)) = if a=b then 1 else 0 := by
  classical
  simp [histogramBasis, hinj.eq_iff]

/-- For a lower-triangular kernel and histograms of fixed total mass, every error amplitude at
another histogram configuration is zero. -/
theorem errorColumn_same_layer {H : Type*} {d q n : ℕ} (K : Fin q → Fin q → ℂ)
    (hK : ∀k y,k<y → K k y=0) (hist : H → Fin d → Fin q)
    (hm : ∀h,∑i,(hist h i:ℕ)=n) (a b : H) : errorColumn K hist b (hist a)=0 := by
  unfold errorColumn
  rw [column_same_mass K hK (hist b) (hist a) ((hm b).trans (hm a).symm)]
  unfold histogramBasis
  split_ifs <;> simp

/-- For a lower-triangular kernel on a fixed histogram mass layer, every histogram basis vector
is orthogonal to every error vector. -/
theorem histogramBasis_error_orthogonal {H : Type*} {d q n : ℕ} (K : Fin q → Fin q → ℂ)
    (hK : ∀k y,k<y → K k y=0) (hist : H → Fin d → Fin q)
    (hm : ∀h,∑i,(hist h i:ℕ)=n) (a b : H) :
    (∑y,histogramBasis hist a y * star (errorColumn K hist b y))=0 := by
  simp [histogramBasis,errorColumn_same_layer K hK hist hm]

/-- The tensor amplitude matrix is the sum of its diagonal-amplitude-scaled histogram basis and
its error matrix. -/
theorem tensor_decomposition {H : Type*} [Fintype H] [DecidableEq H] {d q : ℕ}
    (K : Fin q → Fin q → ℂ) (hist : H → Fin d → Fin q) :
    columns K hist =
      Matrix.diagonal (fun h => diagonalAmplitude K (hist h)) * histogramBasis hist + errorColumn K hist := by
  ext h y
  simp [Matrix.mul_apply,Matrix.diagonal,errorColumn,columns]

/-- Equality of the kernel row Gram entries implies equality of the corresponding
tensor-amplitude inner products. -/
theorem tensor_gram_preserved {d q : ℕ} (K L : Fin q → Fin q → ℂ)
    (hGram : ∀j k,(∑y,star (K j y)*K k y)=(∑y,star (L j y)*L k y))
    (h k : Fin d → Fin q) :
    (∑y,star (column K h y)*column K k y) =
      ∑y,star (column L h y)*column L k y := by
  simp only [column,star_prod,← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (i : Fin d) (y : Fin q) => star (K (h i) y)*K (k i) y),
    ← Fintype.prod_sum (fun (i : Fin d) (y : Fin q) => star (L (h i) y)*L (k i) y)]
  simp_rw [hGram]

/-- Kernels with equal row Gram entries produce histogram-indexed tensor amplitude matrices with
equal products with their conjugate transposes. -/
theorem columns_gram_preserved {H : Type*} {d q : ℕ} (K L : Fin q → Fin q → ℂ)
    (hGram : ∀j k,(∑y,star (K j y)*K k y)=(∑y,star (L j y)*L k y))
    (hist : H → Fin d → Fin q) :
    columns K hist * (columns K hist)ᴴ=columns L hist * (columns L hist)ᴴ := by
  ext h k
  have h := tensor_gram_preserved K L hGram (hist k) (hist h)
  simpa only [Matrix.mul_apply,Matrix.conjTranspose_apply,columns,mul_comm] using h

end Qatlib.Foundations.MatrixAlgebra.FrameProject.Tensor
