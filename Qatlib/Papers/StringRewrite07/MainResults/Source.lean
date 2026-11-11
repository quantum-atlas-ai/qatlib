/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Notation.Pi.Basic
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Erase
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Init
import Mathlib.Data.ZMod.Defs
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Logic.Function.Defs
import Mathlib.Order.Basic
import Mathlib.Order.BooleanAlgebra.Defs
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Order.Filter.Defs
import Mathlib.Order.Lattice
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.MinMax
import Mathlib.Order.Notation
import Mathlib.Order.RelClasses
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.Order.Group
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Separation.GDelta
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.UniformSpace.Defs
import Qatlib.Concepts.QueryComplexity.DegreeMethod.Complexity

/-!
# String rewriting and spectral walk-count estimates

This module defines length-preserving rewriting on finite words, its adjacency matrix, and
promised walk-count differences through `Instance`. It develops polarization and spectral-moment
identities, coefficient-vanishing arguments, and quantitative estimation bounds used in the
string-rewriting construction of [JanzingWocjan2010].

The final definitions describe promise problems and abstract circuit reductions. Further lemmas
relate block sign expectations to output weights and bound spectral moments and dominant
contributions.

## Main statements

* `step_symm`: symmetric rules give symmetric rewriting steps.
* `spectral_moment_expansion`: rewrites a walk-count difference using spectral moments.
* `spectral_coeff_vanishes_of_growth`: removes spectral contributions beyond the growth
  threshold.
* `sign_decision_from_estimate`: recovers the promised sign from an accurate estimate.

## References

* [Janzing and Wocjan, 2010][JanzingWocjan2010]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.StringRewrite07.MainResults

open Matrix

/-- Words of length `L` over the alphabet `α`, represented as functions on `Fin L`. -/
abbrev Word (α : Type) (L : ℕ) := Fin L → α

/-- Extracts the length-`k` subword beginning at position `i`, using the bound `i + k ≤ L`. -/
def subwordAt {α : Type} {L : ℕ} (w : Word α L) (i k : ℕ) (h : i + k ≤ L) : Fin k → α :=
  fun j => w ⟨i + j.1, by omega⟩

/-- States that the length-`k` subword of `w` beginning at `i` equals `u`. -/
def HasSubwordAt {α : Type} {L : ℕ} (w : Word α L) (i k : ℕ) (h : i + k ≤ L)
    (u : Fin k → α) : Prop :=
  subwordAt w i k h = u

/-- Replaces the length-`k` subword beginning at `i` by `v`, preserving all other letters. -/
def overwriteSubword {α : Type} {L : ℕ} (w : Word α L) (i k : ℕ) (v : Fin k → α)
    (h : i + k ≤ L) : Word α L :=
  fun j =>
    if h1 : (j : ℕ) < i then w j
    else if h2 : (j : ℕ) < i + k then v ⟨(j : ℕ) - i, by omega⟩
    else w j

/-- Relates two words when one is obtained from the other by a single length-preserving
replacement allowed by `R`. -/
def Step {α : Type} {L : ℕ} (R : ∀ k, (Fin k → α) → (Fin k → α) → Prop)
    (w w' : Word α L) : Prop :=
  ∃ (i k : ℕ) (h : i + k ≤ L) (u v : Fin k → α),
    R k u v ∧ HasSubwordAt w i k h u ∧ w' = overwriteSubword w i k v h

/-- States that every replacement allowed by `R` is also allowed in the reverse direction. -/
def IsSymmetricRule {α : Type} (R : ∀ k, (Fin k → α) → (Fin k → α) → Prop) : Prop :=
  ∀ k (u v : Fin k → α), R k u v → R k v u

/-- Extracting a subword immediately after overwriting it returns the replacement word. -/
@[simp]
theorem subwordAt_overwrite {α : Type} {L : ℕ} (w : Word α L) (i k : ℕ)
    (v : Fin k → α) (h : i + k ≤ L) :
    HasSubwordAt (overwriteSubword w i k v h) i k h v := by
  funext j
  have hj : (j : ℕ) < k := j.isLt
  unfold subwordAt overwriteSubword
  dsimp only
  have h1 : ¬ ((⟨i + j.1, by omega⟩ : Fin L) : ℕ) < i := by
    simp only [Fin.val_mk]
    omega
  have h2 : ((⟨i + j.1, by omega⟩ : Fin L) : ℕ) < i + k := by
    simp only [Fin.val_mk]
    omega
  rw [dif_neg h1, dif_pos h2]
  congr 1
  ext
  simp only [Fin.val_mk]
  omega

/-- Overwriting the same interval twice has the same effect as the second overwrite alone. -/
theorem overwrite_overwrite {α : Type} {L : ℕ} (w : Word α L) (i k : ℕ)
    (u v : Fin k → α) (h : i + k ≤ L) :
    overwriteSubword (overwriteSubword w i k u h) i k v h = overwriteSubword w i k v h := by
  funext j
  unfold overwriteSubword
  by_cases h1 : (j : ℕ) < i
  · simp only [dif_pos h1]
  · by_cases h2 : (j : ℕ) < i + k
    · simp only [dif_neg h1, dif_pos h2]
    · simp only [dif_neg h1, dif_neg h2]

/-- Replacing a subword by its existing contents leaves the word unchanged. -/
theorem overwrite_self {α : Type} {L : ℕ} (w : Word α L) (i k : ℕ) (u : Fin k → α)
    (h : i + k ≤ L) (hu : HasSubwordAt w i k h u) :
    overwriteSubword w i k u h = w := by
  funext j
  unfold overwriteSubword
  by_cases h1 : (j : ℕ) < i
  · simp only [dif_pos h1]
  · by_cases h2 : (j : ℕ) < i + k
    · have hx : (⟨i + ((j : ℕ) - i), by omega⟩ : Fin L) = j := by
        ext
        simp only [Fin.val_mk]
        omega
      have hux : u ⟨(j : ℕ) - i, by omega⟩ = w j := by
        rw [← congrFun hu ⟨(j : ℕ) - i, by omega⟩]
        simp only [HasSubwordAt, subwordAt, Fin.val_mk]
        rw [hx]
      simp only [dif_neg h1, dif_pos h2]
      exact hux
    · simp only [dif_neg h1, dif_neg h2]

/-- A symmetric replacement rule induces a symmetric relation on words. -/
theorem step_symm {α : Type} {L : ℕ} {R : ∀ k, (Fin k → α) → (Fin k → α) → Prop}
    (hR : IsSymmetricRule R) {w w' : Word α L} (h : Step R w w') : Step R w' w := by
  obtain ⟨i, k, hik, u, v, huv, hu, rfl⟩ := h
  refine ⟨i, k, hik, v, u, hR k u v huv, subwordAt_overwrite w i k v hik, ?_⟩
  rw [overwrite_overwrite, overwrite_self w i k u hik hu]

/-- The real zero-one adjacency matrix of the one-step rewriting relation. -/
noncomputable def adjMatrix {α : Type} [Fintype α] [DecidableEq α] {L : ℕ}
    (R : ∀ k, (Fin k → α) → (Fin k → α) → Prop) : Matrix (Word α L) (Word α L) ℝ :=
  fun w w' => @ite ℝ (Step R w w') (Classical.propDecidable (Step R w w')) 1 0

/-- The adjacency matrix of a symmetric replacement rule is symmetric. -/
theorem adjMatrix_isSymm {α : Type} [Fintype α] [DecidableEq α] {L : ℕ}
    {R : ∀ k, (Fin k → α) → (Fin k → α) → Prop} (hR : IsSymmetricRule R) :
    (adjMatrix (L := L) R).IsSymm := by
  refine Matrix.IsSymm.ext (A := adjMatrix (L := L) R) (fun w w' => ?_)
  unfold adjMatrix
  by_cases h : Step R w w'
  · rw [if_pos h, if_pos (step_symm hR h)]
  · by_cases h' : Step R w' w
    · exact absurd (step_symm hR h') h
    · rw [if_neg h', if_neg h]

/-- The `(s, t)` entry of `A ^ n`, which counts length-`n` walks when `A` is an adjacency
matrix. -/
def walkCount {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (n : ℕ)
    (s t : ι) : ℝ :=
  (A ^ n) s t

/-- The difference between the `(s, t)` and `(s, t')` entries of `A ^ n`. -/
def Delta {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (n : ℕ)
    (s t t' : ι) : ℝ :=
  walkCount A n s t - walkCount A n s t'

/-- Requires the absolute walk-count difference at every length `n` to be at most `c ^ n`. -/
def GrowthCondition {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ)
    (s t t' : ι) (c : ℝ) : Prop :=
  ∀ n : ℕ, |Delta A n s t t'| ≤ c ^ n

/-- Requires the absolute walk-count difference at length `m` to be at least `ε * c ^ m`. -/
def GapCondition {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (m : ℕ)
    (s t t' : ι) (ε c : ℝ) : Prop :=
  ε * c ^ m ≤ |Delta A m s t t'|

/-- A symmetric string-rewriting instance with three distinguished words, a target length, and
growth and gap promises. -/
structure Instance (α : Type) [Fintype α] [DecidableEq α] where
  L : ℕ
  rule : ∀ k, (Fin k → α) → (Fin k → α) → Prop
  rule_symm : IsSymmetricRule rule
  s : Word α L
  t : Word α L
  t' : Word α L
  m : ℕ
  c : ℝ
  ε : ℝ
  hc : 0 < c
  hε : 0 ≤ ε
  growth : GrowthCondition (adjMatrix rule) s t t' c
  gap : GapCondition (adjMatrix rule) m s t t' ε c

namespace Instance

variable {α : Type} [Fintype α] [DecidableEq α]

/-- The rewriting adjacency matrix associated with the instance. -/
def matrix (I : Instance α) : Matrix (Word α I.L) (Word α I.L) ℝ :=
  adjMatrix I.rule

/-- The adjacency matrix of a rewriting instance is symmetric. -/
theorem matrix_isSymm (I : Instance α) : I.matrix.IsSymm :=
  adjMatrix_isSymm I.rule_symm

/-- The walk-count difference for the instance at length `n`. -/
def delta (I : Instance α) (n : ℕ) : ℝ :=
  Delta I.matrix n I.s I.t I.t'

/-- The walk-count difference for the instance at its designated length `m`. -/
def deltaAtM (I : Instance α) : ℝ :=
  I.delta I.m

/-- States that the designated walk-count difference is positive. -/
def IsYes (I : Instance α) : Prop := 0 < I.deltaAtM

/-- States that the designated walk-count difference is negative. -/
def IsNo (I : Instance α) : Prop := I.deltaAtM < 0

/-- The instance satisfies its prescribed growth bound for all walk lengths. -/
theorem growth_condition (I : Instance α) : GrowthCondition I.matrix I.s I.t I.t' I.c :=
  I.growth

/-- The instance satisfies its prescribed gap bound at the designated walk length. -/
theorem gap_condition (I : Instance α) : GapCondition I.matrix I.m I.s I.t I.t' I.ε I.c :=
  I.gap

end Instance

section Polarization

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The coordinate vector with value one at `i` and zero elsewhere. -/
def basisVec (i : ι) : ι → ℝ := Pi.single i 1

/-- The difference of the coordinate vectors at `t` and `t'`, divided by `√2`. -/
def phiVec (t t' : ι) : ι → ℝ := fun j => (basisVec t j - basisVec t' j) / Real.sqrt 2

/-- The sum of `basisVec s` and `phiVec t t'`, divided by `√2`. -/
def psiPlus (s t t' : ι) : ι → ℝ := fun j => (basisVec s j + phiVec t t' j) / Real.sqrt 2

/-- The difference of `basisVec s` and `phiVec t t'`, divided by `√2`. -/
def psiMinus (s t t' : ι) : ι → ℝ := fun j => (basisVec s j - phiVec t t' j) / Real.sqrt 2

/-- Taking the dot product with a coordinate vector extracts the corresponding coordinate. -/
@[simp]
lemma basisVec_dot (s : ι) (v : ι → ℝ) : basisVec s ⬝ᵥ v = v s := by
  rw [dotProduct, Finset.sum_eq_single s]
  · simp [basisVec]
  · intro i _ hi
    have h0 : basisVec s i = 0 := by
      simp only [basisVec, Pi.single_eq_of_ne hi]
    simp [h0]
  · intro hs
    exact absurd (Finset.mem_univ s) hs

/-- Summing against the coordinate vector at `t` extracts `v t`. -/
lemma sum_mul_basisVec (v : ι → ℝ) (t : ι) :
    (∑ j, v j * basisVec t j) = v t := by
  rw [Finset.sum_eq_single t]
  · simp [basisVec]
  · intro j _ hj
    have h0 : basisVec t j = 0 := by
      simp only [basisVec, Pi.single_eq_of_ne hj]
    simp [h0]
  · intro h
    exact absurd (Finset.mem_univ t) h

/-- Multiplication by `phiVec t t'` extracts the difference of the corresponding matrix columns,
divided by `√2`. -/
lemma mulVec_phi_apply (A : Matrix ι ι ℝ) (s t t' : ι) :
    (A *ᵥ phiVec t t') s = (A s t - A s t') / Real.sqrt 2 := by
  rw [Matrix.mulVec, dotProduct]
  simp only [phiVec, mul_div_assoc', mul_sub]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, sum_mul_basisVec, sum_mul_basisVec]

/-- For a symmetric matrix, the associated bilinear form is symmetric. -/
lemma dot_mulVec_comm {A : Matrix ι ι ℝ} (hA : A.IsSymm) (x y : ι → ℝ) :
    x ⬝ᵥ (A *ᵥ y) = y ⬝ᵥ (A *ᵥ x) := by
  calc x ⬝ᵥ (A *ᵥ y) = y ⬝ᵥ (Aᵀ *ᵥ x) := (dotProduct_transpose_mulVec A y x).symm
    _ = y ⬝ᵥ (A *ᵥ x) := by rw [hA.eq]

/-- For a symmetric matrix, the difference of the quadratic forms at `a + b` and `a - b` equals
four times the mixed bilinear term. -/
lemma polarization {A : Matrix ι ι ℝ} (hA : A.IsSymm) (a b : ι → ℝ) :
    (a + b) ⬝ᵥ (A *ᵥ (a + b)) - (a - b) ⬝ᵥ (A *ᵥ (a - b))
      = 4 * (a ⬝ᵥ (A *ᵥ b)) := by
  have hcomm : b ⬝ᵥ (A *ᵥ a) = a ⬝ᵥ (A *ᵥ b) := dot_mulVec_comm hA b a
  simp only [Matrix.mulVec_add, Matrix.mulVec_sub, add_dotProduct, sub_dotProduct,
    dotProduct_add, dotProduct_sub, hcomm]
  ring

/-- Scaling both arguments in the difference of two quadratic forms multiplies the result by `c
^ 2`. -/
lemma dot_quad_smul (A : Matrix ι ι ℝ) (c : ℝ) (a b : ι → ℝ) :
    (c • (a + b)) ⬝ᵥ (A *ᵥ (c • (a + b))) - (c • (a - b)) ⬝ᵥ (A *ᵥ (c • (a - b)))
      = c ^ 2 * ((a + b) ⬝ᵥ (A *ᵥ (a + b)) - (a - b) ⬝ᵥ (A *ᵥ (a - b))) := by
  simp only [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
  ring

/-- Expresses `psiPlus` as a scalar multiple of `basisVec s + phiVec t t'`. -/
lemma psiPlus_eq_smul (s t t' : ι) :
    psiPlus s t t' = (Real.sqrt 2)⁻¹ • (basisVec s + phiVec t t') := by
  funext j
  simp only [psiPlus, Pi.add_apply, Pi.smul_apply, div_eq_inv_mul]
  rw [smul_eq_mul, mul_comm]

/-- Expresses `psiMinus` as a scalar multiple of `basisVec s - phiVec t t'`. -/
lemma psiMinus_eq_smul (s t t' : ι) :
    psiMinus s t t' = (Real.sqrt 2)⁻¹ • (basisVec s - phiVec t t') := by
  funext j
  simp only [psiMinus, Pi.sub_apply, Pi.smul_apply, div_eq_inv_mul]
  rw [smul_eq_mul, mul_comm]

/-- Expresses the difference `A s t - A s t'` as `√2 / 2` times the difference of quadratic
forms at `psiPlus` and `psiMinus` for symmetric `A` [JanzingWocjan2010]. -/
theorem delta_eq_polarization {A : Matrix ι ι ℝ} (hA : A.IsSymm) (s t t' : ι) :
    A s t - A s t' =
      (Real.sqrt 2 / 2) *
        ((psiPlus s t t') ⬝ᵥ (A *ᵥ psiPlus s t t')
          - (psiMinus s t t') ⬝ᵥ (A *ᵥ psiMinus s t t')) := by
  have hb : basisVec s ⬝ᵥ (A *ᵥ phiVec t t') = (A s t - A s t') / Real.sqrt 2 := by
    rw [basisVec_dot, mulVec_phi_apply]
  have hc : ((Real.sqrt 2)⁻¹) ^ 2 = (2 : ℝ)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hs : Real.sqrt 2 ≠ 0 := by
    have h : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    positivity
  rw [psiPlus_eq_smul, psiMinus_eq_smul, dot_quad_smul, polarization hA, hb, hc]
  field_simp [hs]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

end Polarization

section Spectral

variable {ι : Type} [Fintype ι] [DecidableEq ι] {κ : Type} [Fintype κ]

/-- A decomposition of a symmetric real matrix into a finite weighted sum of idempotents whose
pairwise products vanish and whose sum is the identity. -/
structure SpectralDecomposition (A : Matrix ι ι ℝ) (lam : κ → ℝ) (Q : κ → Matrix ι ι ℝ) :
    Prop where
  symm : A.IsSymm
  idem : ∀ j, Q j * Q j = Q j
  orth : ∀ i j, i ≠ j → Q i * Q j = 0
  sum_one : ∑ j, Q j = 1
  decomp : A = ∑ j, lam j • Q j

/-- Powers of a matrix with the given spectral decomposition are obtained by raising each
spectral coefficient to the same power. -/
theorem pow_eq_sum_smul {A : Matrix ι ι ℝ} {lam : κ → ℝ} {Q : κ → Matrix ι ι ℝ}
    (h : SpectralDecomposition A lam Q) (m : ℕ) :
    A ^ m = ∑ j, (lam j) ^ m • Q j := by
  induction m with
  | zero =>
      simp only [pow_zero, one_smul]
      exact h.sum_one.symm
  | succ m ih =>
      have hstep : A ^ (m + 1) = (∑ j, (lam j) ^ m • Q j) * (∑ j, lam j • Q j) := by
        rw [pow_succ, ih, h.decomp]
      rw [hstep, Fintype.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_eq_single j]
      · calc (lam j ^ m • Q j) * (lam j • Q j)
            = (lam j ^ m) • (Q j * (lam j • Q j)) := by rw [Matrix.smul_mul]
          _ = (lam j ^ m) • (lam j • (Q j * Q j)) := by rw [Matrix.mul_smul]
          _ = (lam j ^ m * lam j) • (Q j * Q j) := by rw [smul_smul]
          _ = (lam j ^ m * lam j) • Q j := by rw [h.idem j]
          _ = (lam j ^ (m + 1)) • Q j := by rw [pow_succ]
      · intro k _ hk
        calc (lam j ^ m • Q j) * (lam k • Q k)
            = (lam j ^ m) • (Q j * (lam k • Q k)) := by rw [Matrix.smul_mul]
          _ = (lam j ^ m) • (lam k • (Q j * Q k)) := by rw [Matrix.mul_smul]
          _ = (lam j ^ m * lam k) • (Q j * Q k) := by rw [smul_smul]
          _ = 0 := by rw [h.orth j k (Ne.symm hk), smul_zero]
      · intro hj
        exact absurd (Finset.mem_univ j) hj

/-- Expands the quadratic form of `A ^ m` as a weighted sum of quadratic forms of the spectral
idempotents. -/
theorem dot_pow_decomp {A : Matrix ι ι ℝ} {lam : κ → ℝ} {Q : κ → Matrix ι ι ℝ}
    (h : SpectralDecomposition A lam Q) (x : ι → ℝ) (m : ℕ) :
    x ⬝ᵥ ((A ^ m) *ᵥ x) = ∑ j, (lam j) ^ m * (x ⬝ᵥ ((Q j) *ᵥ x)) := by
  rw [pow_eq_sum_smul h m, Matrix.sum_mulVec]
  rw [dotProduct_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

/-- Expands the walk-count difference at length `m` into spectral moments weighted by the
difference of two quadratic forms [JanzingWocjan2010]. -/
theorem spectral_moment_expansion {A : Matrix ι ι ℝ} {lam : κ → ℝ}
    {Q : κ → Matrix ι ι ℝ} (h : SpectralDecomposition A lam Q) (m : ℕ) (s t t' : ι) :
    (A ^ m) s t - (A ^ m) s t' =
      (Real.sqrt 2 / 2) * ∑ j, (lam j) ^ m *
        ((psiPlus s t t') ⬝ᵥ ((Q j) *ᵥ psiPlus s t t')
          - (psiMinus s t t') ⬝ᵥ ((Q j) *ᵥ psiMinus s t t')) := by
  have hp := delta_eq_polarization (A := A ^ m) (h.symm.pow m) s t t'
  rw [hp]
  congr 1
  rw [dot_pow_decomp h (psiPlus s t t') m, dot_pow_decomp h (psiMinus s t t') m]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

end Spectral

/-- Raises `x` to the power `m` after truncating it to the interval from `-c` to `c` when `c` is
nonnegative. -/
def truncFunc (m : ℕ) (c x : ℝ) : ℝ :=
  if x < -c then (-c) ^ m else if x ≤ c then x ^ m else c ^ m

/-- Truncation does not change `x ^ m` when `c` is nonnegative and `|x| ≤ c`. -/
theorem truncFunc_eq_pow {m : ℕ} {c x : ℝ} (hc : 0 ≤ c) (h : |x| ≤ c) :
    truncFunc m c x = x ^ m := by
  have hle : -c ≤ x := (abs_le.mp h).1
  have hle' : x ≤ c := (abs_le.mp h).2
  unfold truncFunc
  rw [if_neg (not_lt.mpr hle), if_pos hle']

/-- For nonnegative `c`, the absolute value of the truncated power is at most `c ^ m`. -/
theorem truncFunc_abs_le {m : ℕ} {c x : ℝ} (hc : 0 ≤ c) :
    |truncFunc m c x| ≤ c ^ m := by
  unfold truncFunc
  by_cases h1 : x < -c
  · rw [if_pos h1, abs_pow, abs_neg, abs_of_nonneg hc]
  · rw [if_neg h1]
    by_cases h2 : x ≤ c
    · rw [if_pos h2, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg x) (abs_le.mpr ⟨not_lt.mp h1, h2⟩) m
    · rw [if_neg h2, abs_of_nonneg (pow_nonneg hc m)]

/-- For nonnegative `c`, the truncated power equals the power of `x` clamped to `[-c, c]`. -/
theorem truncFunc_eq_clamp_pow {m : ℕ} {c x : ℝ} (hc : 0 ≤ c) :
    truncFunc m c x = (max (-c) (min x c)) ^ m := by
  unfold truncFunc
  by_cases h1 : x < -c
  · have hxc : x ≤ c := le_of_lt (lt_of_lt_of_le h1 (by linarith))
    have hxm : x ≤ -c := le_of_lt h1
    rw [if_pos h1, min_eq_left hxc, max_eq_left hxm]
  · rw [if_neg h1]
    have hx : -c ≤ x := not_lt.mp h1
    by_cases h2 : x ≤ c
    · rw [if_pos h2, min_eq_left h2, max_eq_right hx]
    · have hxc : c ≤ x := (not_le.mp h2).le
      rw [if_neg h2, min_eq_right hxc, max_eq_right (by linarith)]

/-- For nonnegative `c`, the truncated power has Lipschitz bound `m * c ^ (m - 1)`
[JanzingWocjan2010]. -/
theorem truncFunc_lipschitz {m : ℕ} {c : ℝ} (hc : 0 ≤ c) (x y : ℝ) :
    |truncFunc m c x - truncFunc m c y| ≤ (m : ℝ) * c ^ (m - 1) * |x - y| := by
  rw [truncFunc_eq_clamp_pow hc, truncFunc_eq_clamp_pow hc]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp
  · have hclamp : |max (-c) (min x c) - max (-c) (min y c)| ≤ |x - y| := by
      calc |max (-c) (min x c) - max (-c) (min y c)|
          ≤ max |(-c) - (-c)| |min x c - min y c| := abs_max_sub_max_le_max _ _ _ _
        _ = |min x c - min y c| := by simp
        _ ≤ max |x - y| |c - c| := abs_min_sub_min_le_max _ _ _ _
        _ = |x - y| := by simp
    have hbound : ∀ z : ℝ, |max (-c) (min z c)| ≤ c := by
      intro z
      rw [abs_le]
      exact ⟨by linarith [le_max_left (-c) (min z c)],
        by linarith [max_le (by linarith : -c ≤ c) (min_le_right z c)]⟩
    have hK : max |max (-c) (min x c)| |max (-c) (min y c)| ≤ c :=
      max_le (hbound x) (hbound y)
    have hpow : max |max (-c) (min x c)| |max (-c) (min y c)| ^ (m - 1) ≤ c ^ (m - 1) :=
      pow_le_pow_left₀ (by positivity) hK (m - 1)
    calc |max (-c) (min x c) ^ m - max (-c) (min y c) ^ m|
        ≤ |max (-c) (min x c) - max (-c) (min y c)| * (m : ℝ) *
            max |max (-c) (min x c)| |max (-c) (min y c)| ^ (m - 1) :=
          abs_pow_sub_pow_le _ _ m
      _ ≤ |x - y| * (m : ℝ) * c ^ (m - 1) := by gcongr
      _ = (m : ℝ) * c ^ (m - 1) * |x - y| := by ring

/-- A real sequence bounded in absolute value by `B * q ^ n` tends to zero when `0 ≤ q < 1`. -/
theorem tendsto_zero_of_abs_le_mul_pow {u : ℕ → ℝ} {B q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (h : ∀ n, |u n| ≤ B * q ^ n) :
    Filter.Tendsto u Filter.atTop (nhds 0) := by
  have hgeom : Filter.Tendsto (fun n : ℕ => B * q ^ n) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul B
  have habs : Filter.Tendsto (fun n : ℕ => |u n|) Filter.atTop (nhds 0) :=
    squeeze_zero (fun n => abs_nonneg _) h hgeom
  exact (tendsto_zero_iff_abs_tendsto_zero u).mpr habs

/-- A sequence of period two that tends to zero has both its initial values equal to zero. -/
theorem eq_zero_of_tendsto_of_period_two {u : ℕ → ℝ}
    (hlim : Filter.Tendsto u Filter.atTop (nhds 0)) (hper : ∀ n, u (n + 2) = u n) :
    u 0 = 0 ∧ u 1 = 0 := by
  have heven : ∀ k : ℕ, u (2 * k) = u 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have h2 : 2 * (k + 1) = 2 * k + 2 := by ring
        rw [h2, hper, ih]
  have hodd : ∀ k : ℕ, u (2 * k + 1) = u 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have h2 : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by ring
        rw [h2, hper, ih]
  constructor
  · by_contra hne
    have hpos : 0 < |u 0| := abs_pos.mpr hne
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim |u 0| hpos
    have hNN : N ≤ 2 * (N + 1) := by omega
    have h1 := hN (2 * (N + 1)) hNN
    rw [Real.dist_eq, sub_zero, heven (N + 1)] at h1
    exact absurd h1 (lt_irrefl _)
  · by_contra hne
    have hpos : 0 < |u 1| := abs_pos.mpr hne
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim |u 1| hpos
    have hNN : N ≤ 2 * (N + 1) + 1 := by omega
    have h1 := hN (2 * (N + 1) + 1) hNN
    rw [Real.dist_eq, sub_zero, hodd (N + 1)] at h1
    exact absurd h1 (lt_irrefl _)

/-- In a finite sum of distinct real exponential terms with the stated decay bound and support
in `[-1, 1]`, every coefficient at a base of absolute value one vanishes. -/
theorem coeff_zero_of_unit_modulus {κ : Type} [Fintype κ] (a mu : κ → ℝ)
    {B q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (hinj : Function.Injective mu)
    (hbound : ∀ n : ℕ, |∑ j, a j * (mu j) ^ n| ≤ B * q ^ n)
    (hmu : ∀ j, a j ≠ 0 → |mu j| ≤ 1) :
    ∀ j, |mu j| = 1 → a j = 0 := by
  classical
  have hlim : Filter.Tendsto (fun n => ∑ j, a j * (mu j) ^ n) Filter.atTop (nhds 0) :=
    tendsto_zero_of_abs_le_mul_pow hq0 hq1 hbound
  set S : Finset κ := Finset.univ.filter (fun j => |mu j| = 1) with hS
  have hmem : ∀ j, j ∈ S ↔ |mu j| = 1 := by
    intro j; simp [hS]
  have hcompllim : Filter.Tendsto (fun n => ∑ j ∈ Sᶜ, a j * (mu j) ^ n)
      Filter.atTop (nhds 0) := by
    have hterm : ∀ j ∈ Sᶜ, Filter.Tendsto (fun n => a j * (mu j) ^ n)
        Filter.atTop (nhds (a j * 0)) := by
      intro j hj
      have hjS : j ∉ S := Finset.mem_compl.mp hj
      by_cases ha : a j = 0
      · simp [ha]
      · have hjlt : |mu j| < 1 := by
          have hle := hmu j ha
          rcases lt_or_eq_of_le hle with h | h
          · exact h
          · exact absurd ((hmem j).mpr h) hjS
        exact (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hjlt).const_mul (a j)
    have hs := tendsto_finsetSum (s := Sᶜ) (f := fun j n => a j * (mu j) ^ n)
      (a := fun j => a j * 0) hterm
    simpa using hs
  have hSlim : Filter.Tendsto (fun n => ∑ j ∈ S, a j * (mu j) ^ n) Filter.atTop (nhds 0) := by
    have hsub := hlim.sub hcompllim
    convert hsub using 1
    · ext n
      have h := Finset.sum_add_sum_compl S (fun j => a j * (mu j) ^ n)
      rw [← h]; ring
    · ring
  have hper : ∀ n, (∑ j ∈ S, a j * (mu j) ^ (n + 2)) = (∑ j ∈ S, a j * (mu j) ^ n) := by
    intro n
    apply Finset.sum_congr rfl
    intro j hj
    have h1 : mu j = 1 ∨ mu j = -1 :=
      (abs_eq (show (0 : ℝ) ≤ 1 by norm_num)).mp ((hmem j).mp hj)
    rcases h1 with h1 | h1
    · rw [h1, one_pow, one_pow]
    · rw [h1]
      have h2 : (-1 : ℝ) ^ (n + 2) = (-1 : ℝ) ^ n * (-1) ^ 2 := by rw [pow_add]
      rw [h2]; norm_num
  obtain ⟨h0, h1⟩ := eq_zero_of_tendsto_of_period_two hSlim hper
  have hS0 : (∑ i ∈ S, a i) = 0 := by
    simpa using h0
  have hS1 : (∑ i ∈ S, a i * mu i) = 0 := by
    simpa using h1
  intro j hj
  have hSj : j ∈ S := (hmem j).mpr hj
  have hSins : S = insert j (S.erase j) := (Finset.insert_erase hSj).symm
  have hnotmem : j ∉ S.erase j := Finset.notMem_erase j S
  have herase : ∀ i ∈ S.erase j, mu i = - mu j := by
    intro i hi
    have hiS : i ∈ S := Finset.mem_of_mem_erase hi
    have hij : i ≠ j := Finset.ne_of_mem_erase hi
    have hi1 : |mu i| = 1 := (hmem i).mp hiS
    have hx : (mu i) ^ 2 = 1 := by
      rw [← sq_abs, hi1]; norm_num
    have hy : (mu j) ^ 2 = 1 := by
      rw [← sq_abs, hj]; norm_num
    have hne : mu i - mu j ≠ 0 := by
      intro h
      exact hij (hinj (sub_eq_zero.mp h))
    have hprod : (mu i - mu j) * (mu i + mu j) = 0 := by nlinarith
    have hplus : mu i + mu j = 0 := by
      rcases mul_eq_zero.mp hprod with h | h
      · exact absurd h hne
      · exact h
    linarith
  have hsum0 : a j + (∑ i ∈ S.erase j, a i) = 0 := by
    have h := hS0
    rw [hSins, Finset.sum_insert hnotmem] at h
    exact h
  have hsum1 : a j * mu j + (∑ i ∈ S.erase j, a i * mu i) = 0 := by
    have h := hS1
    rw [hSins, Finset.sum_insert hnotmem] at h
    exact h
  have herasesum : (∑ i ∈ S.erase j, a i * mu i) = -mu j * (∑ i ∈ S.erase j, a i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [herase i hi]
    ring
  have herase0 : (∑ i ∈ S.erase j, a i) = - a j := by linarith
  have hmuj : mu j ≠ 0 := by
    intro h
    rw [h, abs_zero] at hj
    norm_num at hj
  rw [herasesum, herase0] at hsum1
  have h2 : a j * mu j = 0 := by nlinarith
  exact (mul_eq_zero.mp h2).resolve_right hmuj

/-- In a finite sum with distinct real bases and growth bounded by `B * c ^ n`, every
coefficient at a base of absolute value greater than `c` vanishes [JanzingWocjan2010]. -/
theorem coefficient_vanishes_of_growth {κ : Type} [Fintype κ] (a lam : κ → ℝ) {B c : ℝ}
    (_hB : 0 ≤ B) (hc : 0 ≤ c) (hinj : Function.Injective lam)
    (hgrowth : ∀ n : ℕ, |∑ j, a j * (lam j) ^ n| ≤ B * c ^ n)
    (j : κ) (hj : c < |lam j|) : a j = 0 := by
  classical
  have main : ∀ K : ℕ, ∀ (b : κ → ℝ),
      (Finset.univ.filter (fun j => b j ≠ 0 ∧ c < |lam j|)).card ≤ K →
      (∀ n, |∑ j, b j * (lam j) ^ n| ≤ B * c ^ n) →
      ∀ i, c < |lam i| → b i = 0 := by
    intro K
    induction K with
    | zero =>
        intro b hcard hb i hi
        by_contra hne
        have hpos : 0 < (Finset.univ.filter (fun j => b j ≠ 0 ∧ c < |lam j|)).card :=
          Finset.card_pos.mpr
            ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne, hi⟩⟩
        omega
    | succ K ih =>
        intro b hcard hb i hi
        by_cases hbi : b i = 0
        · exact hbi
        · set W : Finset κ := Finset.univ.filter (fun j => b j ≠ 0 ∧ c < |lam j|) with hW
          have hiW : i ∈ W := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hbi, hi⟩
          obtain ⟨x, hxW, hxmax⟩ := Finset.exists_max_image W (fun j => |lam j|) (h := ⟨i, hiW⟩)
          set M : ℝ := |lam x| with hMdef
          have hxi : c < M := by
            rw [hMdef]
            exact (Finset.mem_filter.mp hxW).2.2
          have hMpos : 0 < M := lt_of_le_of_lt hc hxi
          have hMne : M ≠ 0 := ne_of_gt hMpos
          have hsupp : ∀ j, b j ≠ 0 → |lam j / M| ≤ 1 := by
            intro j hj
            have hle : |lam j| ≤ M := by
              by_cases hjW : j ∈ W
              · exact hxmax j hjW
              · have hnot : ¬ (c < |lam j|) :=
                  fun hlt => hjW (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj, hlt⟩)
                exact le_trans (not_lt.mp hnot) hxi.le
            rw [abs_div, abs_of_pos hMpos, div_le_one hMpos]
            exact hle
          have hinj_mu : Function.Injective (fun j => lam j / M) := by
            intro y z hyz
            simp only at hyz
            have h : lam y / M * M = lam z / M * M := by rw [hyz]
            rw [div_mul_cancel₀ _ hMne, div_mul_cancel₀ _ hMne] at h
            exact hinj h
          have hbound_mu : ∀ n, |∑ j, b j * (lam j / M) ^ n| ≤ B * (c / M) ^ n := by
            intro n
            have hMn : (0 : ℝ) < M ^ n := pow_pos hMpos n
            have h1 : (∑ j, b j * (lam j / M) ^ n) = (∑ j, b j * (lam j) ^ n) / M ^ n := by
              have hpt : ∀ j, b j * (lam j / M) ^ n = b j * (lam j) ^ n / M ^ n := by
                intro j
                rw [div_pow]
                ring
              rw [Finset.sum_congr rfl (fun j _ => hpt j), ← Finset.sum_div]
            rw [h1, abs_div, abs_of_pos hMn]
            calc |∑ j, b j * (lam j) ^ n| / M ^ n ≤ (B * c ^ n) / M ^ n :=
                  div_le_div_of_nonneg_right (hb n) hMn.le
              _ = B * (c / M) ^ n := by
                rw [mul_div_assoc, div_pow]
          have hq0 : 0 ≤ c / M := div_nonneg hc hMpos.le
          have hq1 : c / M < 1 := (div_lt_one hMpos).mpr hxi
          have hkill : ∀ j, |lam j / M| = 1 → b j = 0 :=
            coeff_zero_of_unit_modulus b (fun j => lam j / M) hq0 hq1 hinj_mu hbound_mu hsupp
          by_cases htop : |lam i| = M
          · have h1 : |lam i / M| = 1 := by
              rw [abs_div, abs_of_pos hMpos, htop, div_self hMne]
            exact hkill i h1
          · have hxM : |lam x| = M := hMdef.symm
            have hb'bound : ∀ n, |∑ j, (if |lam j| = M then 0 else b j) * (lam j) ^ n|
                ≤ B * c ^ n := by
              intro n
              have hcongr : (∑ j, (if |lam j| = M then 0 else b j) * (lam j) ^ n)
                  = (∑ j, b j * (lam j) ^ n) := by
                apply Finset.sum_congr rfl
                intro j _
                by_cases h : |lam j| = M
                · have h1 : |lam j / M| = 1 := by
                    rw [abs_div, abs_of_pos hMpos, h, div_self hMne]
                  rw [if_pos h, hkill j h1, zero_mul]
                · rw [if_neg h]
              rw [hcongr]; exact hb n
            have hsub : (Finset.univ.filter
                  (fun j => (if |lam j| = M then 0 else b j) ≠ 0 ∧ c < |lam j|)) ⊆ W := by
              intro j hj
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
              refine Finset.mem_filter.mpr ⟨Finset.mem_univ j, ?_, hj.2⟩
              intro hb0
              apply hj.1
              by_cases h : |lam j| = M
              · rw [if_pos h]
              · rw [if_neg h]; exact hb0
            have hnotsub : ¬ (W ⊆ Finset.univ.filter
                (fun j => (if |lam j| = M then 0 else b j) ≠ 0 ∧ c < |lam j|)) := by
              intro hsub'
              have hx' := hsub' hxW
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx'
              rw [if_pos hxM] at hx'
              exact hx'.1 rfl
            have hssub : (Finset.univ.filter
                  (fun j => (if |lam j| = M then 0 else b j) ≠ 0 ∧ c < |lam j|)) ⊂ W := by
              rw [Finset.ssubset_iff_subset_ne]
              refine ⟨hsub, ?_⟩
              intro hEq
              exact hnotsub (by rw [← hEq])
            have hcardlt := Finset.card_lt_card hssub
            have hcard' : (Finset.univ.filter
                  (fun j => (if |lam j| = M then 0 else b j) ≠ 0 ∧ c < |lam j|)).card ≤ K := by
              omega
            have hres := ih (fun j => if |lam j| = M then 0 else b j) hcard' hb'bound i hi
            by_cases h : |lam i| = M
            · exact absurd h htop
            · change (if |lam i| = M then 0 else b i) = 0 at hres
              rw [if_neg h] at hres
              exact hres
  exact main (Finset.univ.filter (fun j => a j ≠ 0 ∧ c < |lam j|)).card a (le_refl _)
    (fun n => hgrowth n) j hj

/-- Under the walk-count growth promise and distinct spectral values, the difference of spectral
quadratic-form weights vanishes whenever `|lam j| > c` [JanzingWocjan2010]. -/
theorem spectral_coeff_vanishes_of_growth {ι : Type} [Fintype ι] [DecidableEq ι]
    {κ : Type} [Fintype κ] {A : Matrix ι ι ℝ} {lam : κ → ℝ} {Q : κ → Matrix ι ι ℝ}
    (h : SpectralDecomposition A lam Q) (hinj : Function.Injective lam) (s t t' : ι)
    {c : ℝ} (hc : 0 ≤ c) (hgrowth : ∀ n : ℕ, |Delta A n s t t'| ≤ c ^ n)
    (j : κ) (hj : c < |lam j|) :
    (psiPlus s t t') ⬝ᵥ ((Q j) *ᵥ psiPlus s t t')
      - (psiMinus s t t') ⬝ᵥ ((Q j) *ᵥ psiMinus s t t') = 0 := by
  have hS : ∀ n : ℕ, Delta A n s t t' =
      (Real.sqrt 2 / 2) * ∑ k, ((psiPlus s t t') ⬝ᵥ ((Q k) *ᵥ psiPlus s t t')
        - (psiMinus s t t') ⬝ᵥ ((Q k) *ᵥ psiMinus s t t')) * (lam k) ^ n := by
    intro n
    rw [show Delta A n s t t' = (A ^ n) s t - (A ^ n) s t' from rfl,
      spectral_moment_expansion h n s t t']
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hsqrtpos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hbound : ∀ n : ℕ,
      |∑ k, ((psiPlus s t t') ⬝ᵥ ((Q k) *ᵥ psiPlus s t t')
        - (psiMinus s t t') ⬝ᵥ ((Q k) *ᵥ psiMinus s t t')) * (lam k) ^ n|
        ≤ Real.sqrt 2 * c ^ n := by
    intro n
    have h1 : (∑ k, ((psiPlus s t t') ⬝ᵥ ((Q k) *ᵥ psiPlus s t t')
        - (psiMinus s t t') ⬝ᵥ ((Q k) *ᵥ psiMinus s t t')) * (lam k) ^ n)
        = Delta A n s t t' / (Real.sqrt 2 / 2) := by
      rw [hS n]
      field_simp
    have hinv : (Real.sqrt 2 / 2)⁻¹ = Real.sqrt 2 := by
      rw [inv_div, div_eq_iff (ne_of_gt hsqrtpos)]
      rw [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    rw [h1, abs_div, abs_of_pos (by positivity : (0 : ℝ) < Real.sqrt 2 / 2),
      div_eq_mul_inv, hinv]
    calc |Delta A n s t t'| * Real.sqrt 2 ≤ c ^ n * Real.sqrt 2 :=
          mul_le_mul_of_nonneg_right (hgrowth n) hsqrtpos.le
      _ = Real.sqrt 2 * c ^ n := by ring
  exact coefficient_vanishes_of_growth
    (fun k => (psiPlus s t t') ⬝ᵥ ((Q k) *ᵥ psiPlus s t t')
      - (psiMinus s t t') ⬝ᵥ ((Q k) *ᵥ psiMinus s t t'))
    lam (Real.sqrt_nonneg 2) hc hinj hbound j hj

/-- Bounds the error of a finite probability-weighted estimate by its error on a set of mass at
least `1 - θ` plus `2 * c ^ m * θ` for the remaining mass [JanzingWocjan2010]. -/
theorem measurement_error_bound {κ : Type} [Fintype κ] [DecidableEq κ] {m : ℕ} (p v : κ → ℝ)
    (S : Finset κ) (lam : ℝ) {c η θ : ℝ} (hc : 0 ≤ c) (hη : 0 ≤ η) (hθ : 0 ≤ θ)
    (hlam : |lam| ≤ c)
    (hp : ∀ k, 0 ≤ p k) (hpsum : (∑ k, p k) = 1)
    (hvS : ∀ k, k ∈ S → |v k - lam ^ m| ≤ η * (m : ℝ) * c ^ (m - 1))
    (hv : ∀ k, |v k| ≤ c ^ m)
    (hS : 1 - θ ≤ ∑ k ∈ S, p k) :
    |(∑ k, p k * v k) - lam ^ m| ≤ η * (m : ℝ) * c ^ (m - 1) + 2 * c ^ m * θ := by
  have hdecomp : (∑ k, p k * (v k - lam ^ m)) = (∑ k, p k * v k) - lam ^ m := by
    rw [Finset.sum_congr rfl (fun k _ => mul_sub (p k) (v k) (lam ^ m)),
      Finset.sum_sub_distrib]
    congr 1
    rw [← Finset.sum_mul, hpsum, one_mul]
  have hlam' : |lam ^ m| ≤ c ^ m := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg lam) hlam m
  have htri (k : κ) : |v k - lam ^ m| ≤ 2 * c ^ m := by
    calc |v k - lam ^ m| = |v k + -(lam ^ m)| := by rw [sub_eq_add_neg]
      _ ≤ |v k| + |-(lam ^ m)| := abs_add_le _ _
      _ = |v k| + |lam ^ m| := by rw [abs_neg]
      _ ≤ c ^ m + c ^ m := add_le_add (hv k) hlam'
      _ = 2 * c ^ m := by ring
  have hterm : (0 : ℝ) ≤ η * (m : ℝ) * c ^ (m - 1) := by
    have h1 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have h2 : (0 : ℝ) ≤ c ^ (m - 1) := pow_nonneg hc _
    exact mul_nonneg (mul_nonneg hη h1) h2
  have hcoef : (0 : ℝ) ≤ 2 * c ^ m := by
    have := pow_nonneg hc m
    linarith
  have hgood : |∑ k ∈ S, p k * (v k - lam ^ m)| ≤ η * (m : ℝ) * c ^ (m - 1) := by
    calc |∑ k ∈ S, p k * (v k - lam ^ m)|
        ≤ ∑ k ∈ S, |p k * (v k - lam ^ m)| :=
          Finset.abs_sum_le_sum_abs (fun k => p k * (v k - lam ^ m)) S
      _ = ∑ k ∈ S, p k * |v k - lam ^ m| := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [abs_mul, abs_of_nonneg (hp k)]
      _ ≤ ∑ k ∈ S, p k * (η * (m : ℝ) * c ^ (m - 1)) := by
          refine Finset.sum_le_sum (fun k hk => ?_)
          exact mul_le_mul_of_nonneg_left (hvS k hk) (hp k)
      _ = (∑ k ∈ S, p k) * (η * (m : ℝ) * c ^ (m - 1)) := by rw [Finset.sum_mul]
      _ ≤ 1 * (η * (m : ℝ) * c ^ (m - 1)) := by
          refine mul_le_mul_of_nonneg_right ?_ hterm
          rw [← hpsum]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
            (fun k _ _ => hp k)
      _ = η * (m : ℝ) * c ^ (m - 1) := one_mul _
  have hSc : (∑ k ∈ Sᶜ, p k) = 1 - ∑ k ∈ S, p k := by
    have h := Finset.sum_add_sum_compl S p
    rw [hpsum] at h
    linarith
  have hbad : |∑ k ∈ Sᶜ, p k * (v k - lam ^ m)| ≤ 2 * c ^ m * θ := by
    calc |∑ k ∈ Sᶜ, p k * (v k - lam ^ m)|
        ≤ ∑ k ∈ Sᶜ, |p k * (v k - lam ^ m)| :=
          Finset.abs_sum_le_sum_abs (fun k => p k * (v k - lam ^ m)) Sᶜ
      _ = ∑ k ∈ Sᶜ, p k * |v k - lam ^ m| := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [abs_mul, abs_of_nonneg (hp k)]
      _ ≤ ∑ k ∈ Sᶜ, p k * (2 * c ^ m) := by
          refine Finset.sum_le_sum (fun k _ => ?_)
          exact mul_le_mul_of_nonneg_left (htri k) (hp k)
      _ = (∑ k ∈ Sᶜ, p k) * (2 * c ^ m) := by rw [Finset.sum_mul]
      _ = (1 - ∑ k ∈ S, p k) * (2 * c ^ m) := by rw [hSc]
      _ ≤ θ * (2 * c ^ m) := by
          refine mul_le_mul_of_nonneg_right ?_ hcoef
          linarith
      _ = 2 * c ^ m * θ := by ring
  calc |(∑ k, p k * v k) - lam ^ m|
      = |∑ k, p k * (v k - lam ^ m)| := by rw [← hdecomp]
    _ = |∑ k ∈ S, p k * (v k - lam ^ m) + ∑ k ∈ Sᶜ, p k * (v k - lam ^ m)| := by
          rw [Finset.sum_add_sum_compl S (fun k => p k * (v k - lam ^ m))]
    _ ≤ |∑ k ∈ S, p k * (v k - lam ^ m)| + |∑ k ∈ Sᶜ, p k * (v k - lam ^ m)| :=
          abs_add_le _ _
    _ ≤ η * (m : ℝ) * c ^ (m - 1) + 2 * c ^ m * θ := add_le_add hgood hbad

/-- For positive `ε` and `0 < δ < 1`, the prescribed rounded sample count bounds the scaled
square-root sampling radius by `ε * b / 2` when `b ≥ 0` [JanzingWocjan2010]. -/
theorem sampling_radius_budget {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1)
    (b : ℝ) (hb : 0 ≤ b) :
    b * Real.sqrt (2 * Real.log (2 / δ) /
        ((Nat.ceil (8 * Real.log (2 / δ) / ε ^ 2) + 1 : ℕ) : ℝ)) ≤ ε * b / 2 := by
  set L := Real.log (2 / δ) with hLdef
  have hL : 0 < L := by
    rw [hLdef]
    apply Real.log_pos
    rw [lt_div_iff₀ hδ]
    linarith
  have hNpos : (0 : ℝ) < ((Nat.ceil (8 * L / ε ^ 2) + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_pos]
    exact Nat.succ_pos _
  have hNgt : 8 * L / ε ^ 2 < ((Nat.ceil (8 * L / ε ^ 2) + 1 : ℕ) : ℝ) := by
    have h1 : 8 * L / ε ^ 2 ≤ ((Nat.ceil (8 * L / ε ^ 2) : ℕ) : ℝ) :=
      Nat.le_ceil (8 * L / ε ^ 2)
    have h2 : ((Nat.ceil (8 * L / ε ^ 2) : ℕ) : ℝ)
        < ((Nat.ceil (8 * L / ε ^ 2) + 1 : ℕ) : ℝ) := by
      rw [Nat.cast_lt]
      exact Nat.lt_succ_self _
    linarith
  have hkey : 2 * L / ((Nat.ceil (8 * L / ε ^ 2) + 1 : ℕ) : ℝ) < ε ^ 2 / 4 := by
    rw [div_lt_iff₀ hNpos]
    have hmid : ε ^ 2 / 4 * (8 * L / ε ^ 2) = 2 * L := by
      rw [div_mul_div_comm,
        mul_comm (ε ^ 2) (8 * L),
        mul_div_mul_right (8 * L) 4 (show (ε ^ 2) ≠ 0 by positivity)]
      ring
    have hmul := mul_lt_mul_of_pos_left hNgt (by positivity : (0 : ℝ) < ε ^ 2 / 4)
    rw [hmid] at hmul
    linarith
  have hsqrt : Real.sqrt (2 * L / ((Nat.ceil (8 * L / ε ^ 2) + 1 : ℕ) : ℝ)) ≤ ε / 2 := by
    calc Real.sqrt (2 * L / ((Nat.ceil (8 * L / ε ^ 2) + 1 : ℕ) : ℝ))
        ≤ Real.sqrt (ε ^ 2 / 4) := Real.sqrt_le_sqrt hkey.le
      _ = ε / 2 := by
          rw [show ε ^ 2 / 4 = (ε / 2) ^ 2 by ring]
          exact Real.sqrt_sq (by positivity)
  calc b * Real.sqrt (2 * L / ((Nat.ceil (8 * L / ε ^ 2) + 1 : ℕ) : ℝ))
      ≤ b * (ε / 2) := mul_le_mul_of_nonneg_left hsqrt hb
    _ = ε * b / 2 := by ring

/-- Chooses positive precision and failure parameters and a rounded sample count so that both
measurement and sampling error bounds are at most `ε * I.c ^ I.m / 2` [JanzingWocjan2010]. -/
theorem section3_parameter_budget {α : Type} [Fintype α] [DecidableEq α] (I : Instance α)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ (η θ : ℝ) (N : ℕ),
      0 < η ∧ 0 < θ ∧
      N = Nat.ceil (8 * Real.log (2 / δ) / ε ^ 2) + 1 ∧
      η * (I.m : ℝ) * I.c ^ (I.m - 1) + 2 * I.c ^ I.m * θ ≤ ε * I.c ^ I.m / 2 ∧
      I.c ^ I.m * Real.sqrt (2 * Real.log (2 / δ) / (N : ℝ)) ≤ ε * I.c ^ I.m / 2 := by
  have hc : 0 < I.c := I.hc
  have hcm : (0 : ℝ) < I.c ^ I.m := pow_pos hc I.m
  set x := (I.m : ℝ) * I.c ^ (I.m - 1) with hxdef
  have hx : (0 : ℝ) ≤ x := by
    rw [hxdef]
    exact mul_nonneg (Nat.cast_nonneg I.m) (pow_nonneg hc.le _)
  refine ⟨ε * I.c ^ I.m / (4 * (x + 1)), ε / 8,
    Nat.ceil (8 * Real.log (2 / δ) / ε ^ 2) + 1, ?_, ?_, rfl, ?_, ?_⟩
  · have hpos : (0 : ℝ) < ε * I.c ^ I.m := mul_pos hε hcm
    have hden : (0 : ℝ) < 4 * (x + 1) := by linarith
    exact div_pos hpos hden
  · exact div_pos hε (by norm_num)
  · have hfrac : ε * I.c ^ I.m / (4 * (x + 1)) * x ≤ ε * I.c ^ I.m / 4 := by
      rw [mul_comm (ε * I.c ^ I.m / (4 * (x + 1))) x, mul_div_assoc',
        div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (x + 1))]
      calc x * (ε * I.c ^ I.m) ≤ (x + 1) * (ε * I.c ^ I.m) := by
            have hpos : (0 : ℝ) < ε * I.c ^ I.m := mul_pos hε hcm
            nlinarith [hx]
        _ = ε * I.c ^ I.m / 4 * (4 * (x + 1)) := by ring
    calc ε * I.c ^ I.m / (4 * (x + 1)) * ↑I.m * I.c ^ (I.m - 1)
          + 2 * I.c ^ I.m * (ε / 8)
        = (ε * I.c ^ I.m / (4 * (x + 1)) * x) + ε * I.c ^ I.m / 4 := by
          rw [hxdef]
          ring
      _ ≤ ε * I.c ^ I.m / 4 + ε * I.c ^ I.m / 4 := add_le_add hfrac le_rfl
      _ = ε * I.c ^ I.m / 2 := by ring
  · simpa using sampling_radius_budget hε hδ hδ1 (I.c ^ I.m) hcm.le

/-- An estimate within distance strictly less than a lower bound on `|Δ|` has the same positive
and negative sign tests as `Δ`. -/
theorem sign_eq_of_close {Δ est g : ℝ} (hgap : g ≤ |Δ|) (h : |est - Δ| < g) :
    (0 < est ↔ 0 < Δ) ∧ (est < 0 ↔ Δ < 0) := by
  have h1 : Δ - g < est := by
    have := (abs_lt.mp h).1; linarith
  have h2 : est < Δ + g := by
    have := (abs_lt.mp h).2; linarith
  constructor
  · constructor
    · intro he
      by_contra hΔ
      rw [not_lt] at hΔ
      have h3 : |Δ| = -Δ := abs_of_nonpos hΔ
      nlinarith [hgap, h2, h3]
    · intro hΔ
      have h3 : |Δ| = Δ := abs_of_pos hΔ
      nlinarith [hgap, h1, h3]
  · constructor
    · intro he
      by_contra hΔ
      rw [not_lt] at hΔ
      have h3 : |Δ| = Δ := abs_of_nonneg hΔ
      nlinarith [hgap, h1, h3]
    · intro hΔ
      have h3 : |Δ| = -Δ := abs_of_neg hΔ
      nlinarith [hgap, h2, h3]

namespace Instance

variable {α : Type} [Fintype α] [DecidableEq α]

/-- The designated walk-count difference is nonzero when the instance gap parameter is positive. -/
theorem deltaAtM_ne_zero (I : Instance α) (hε : 0 < I.ε) : I.deltaAtM ≠ 0 := by
  have hcm : (0 : ℝ) < I.c ^ I.m := pow_pos I.hc I.m
  have hpos : 0 < I.ε * I.c ^ I.m := mul_pos hε hcm
  have hgap := I.gap
  unfold GapCondition at hgap
  intro h0
  have h0' : Delta (adjMatrix I.rule) I.m I.s I.t I.t' = 0 := h0
  have h : I.ε * I.c ^ I.m ≤ 0 := by
    have hh := hgap
    rw [h0', abs_zero] at hh
    exact hh
  linarith

/-- An estimate with error strictly below the promised gap determines whether the rewriting
instance is a yes or no instance [JanzingWocjan2010]. -/
theorem sign_decision_from_estimate (I : Instance α) {est : ℝ} (_hε : 0 < I.ε)
    (hest : |est - I.deltaAtM| < I.ε * I.c ^ I.m) :
    (0 < est ↔ I.IsYes) ∧ (est < 0 ↔ I.IsNo) :=
  sign_eq_of_close I.gap hest

end Instance

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.DegreeMethod

/-- A pair of disjoint yes and no predicates on finite Boolean registers of each length. -/
structure PromiseProblem where
  Yes : (n : ℕ) → Reg n → Prop
  No : (n : ℕ) → Reg n → Prop
  disjoint : ∀ (n : ℕ) (x : Reg n), Yes n x → No n x → False

/-- Requires a circuit family whose acceptance probabilities are at least `2 / 3` on yes inputs
and at most `1 / 3` on no inputs of positive length. -/
def AbstractCircuitPromise (P : PromiseProblem) : Prop :=
  ∃ F : CircuitFamily, ∀ (n : ℕ) (hn : 0 < n) (x : Reg n),
    (P.Yes n x →
      (2 / 3 : ℝ) ≤
        AcceptProb (Run (1 : Matrix (Reg n) (Reg n) ℂ) (F.build n) (Ket x)) hn) ∧
    (P.No n x →
      AcceptProb (Run (1 : Matrix (Reg n) (Reg n) ℂ) (F.build n) (Ket x)) hn ≤
        (1 / 3 : ℝ))

/-- Pads a Boolean register to length `D` with false entries. -/
def padReg {n D : ℕ} (h : n ≤ D) (x : Reg n) : Reg D :=
  fun i => if hi : (i : ℕ) < n then x ⟨(i : ℕ), hi⟩ else false

/-- A promise-preserving map computed exactly on padded basis inputs by circuits of polynomially
bounded size and output length. -/
structure AbstractCircuitReduction (P Q : PromiseProblem) where
  outLen : ℕ → ℕ
  map : (n : ℕ) → Reg n → Reg (outLen n)
  le_outLen : ∀ n, n ≤ outLen n
  poly_len : ∃ k c : ℕ, ∀ n, outLen n ≤ c * n ^ k + c
  circuit : (n : ℕ) → Circuit (Reg (outLen n))
  poly_size : ∃ k c : ℕ, ∀ n, Size (circuit n) ≤ c * n ^ k + c
  computes : ∀ (n : ℕ) (x : Reg n),
    Run (1 : Matrix (Reg (outLen n)) (Reg (outLen n)) ℂ) (circuit n)
        (Ket (padReg (le_outLen n) x)) = Ket (map n x)
  maps_yes : ∀ (n : ℕ) (x : Reg n), P.Yes n x → Q.Yes (outLen n) (map n x)
  maps_no : ∀ (n : ℕ) (x : Reg n), P.No n x → Q.No (outLen n) (map n x)

/-- States that an abstract circuit reduction from `Q` to `P` exists. -/
def AbstractCircuitReduces (Q P : PromiseProblem) : Prop := Nonempty (AbstractCircuitReduction Q P)

/-- Requires every promise problem satisfying `AbstractCircuitPromise` to reduce to `P` by an
abstract circuit reduction. -/
def AbstractCircuitHardness (P : PromiseProblem) : Prop :=
  ∀ Q : PromiseProblem, AbstractCircuitPromise Q → AbstractCircuitReduces Q P

/-- A partial decoder from finite Boolean registers to string-rewriting instances. -/
structure Encoding (α : Type) [Fintype α] [DecidableEq α] where

  decode : (n : ℕ) → Reg n → Option (Instance α)

/-- The promise problem whose decoded rewriting instances have positive or negative designated
walk-count difference [JanzingWocjan2010]. -/
def StringRewritingProblem {α : Type} [Fintype α] [DecidableEq α] (enc : Encoding α) :
    PromiseProblem where
  Yes n x := ∃ I : Instance α, enc.decode n x = some I ∧ I.IsYes
  No n x := ∃ I : Instance α, enc.decode n x = some I ∧ I.IsNo
  disjoint := by
    rintro n x ⟨I, hI, hy⟩ ⟨J, hJ, hn⟩
    rw [hI] at hJ
    injection hJ with hIJ
    subst hIJ
    have hn' : I.deltaAtM < 0 := hn
    exact absurd hy (not_lt.mpr hn'.le)

/-- Combines `AbstractCircuitPromise` with hardness under abstract circuit reductions. -/
def AbstractCircuitCompleteness (P : PromiseProblem) : Prop :=
  AbstractCircuitPromise P ∧ AbstractCircuitHardness P

section SigmaZ

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The diagonal real matrix acting by `+1` on the first Boolean block and `-1` on the second. -/
def blockZ : Matrix (Fin 2 × ι) (Fin 2 × ι) ℝ :=
  fun a b =>
    if a.2 = b.2 then (if a.1 = b.1 then (if a.1 = 0 then (1 : ℝ) else -1) else 0) else 0

/-- The sum of squared real amplitudes in block `j`, giving its outcome probability for a
normalized vector. -/
def outProb (φ : Fin 2 × ι → ℝ) (j : Fin 2) : ℝ := ∑ i, (φ (j, i)) ^ 2

/-- The block sign matrix multiplies each coordinate by the sign determined by its first index. -/
theorem blockZ_mulVec (φ : Fin 2 × ι → ℝ) (a : Fin 2 × ι) :
    (blockZ *ᵥ φ) a = (if a.1 = 0 then (1 : ℝ) else -1) * φ a := by
  rw [mulVec, dotProduct, Finset.sum_eq_single a]
  · simp [blockZ]
  · intro b _ hba
    have h : blockZ a b = 0 := by
      simp only [blockZ]
      by_cases h2 : a.2 = b.2
      · rw [if_pos h2]
        by_cases h1 : a.1 = b.1
        · exact absurd (Prod.ext h1 h2).symm hba
        · rw [if_neg h1]
      · rw [if_neg h2]
    rw [h, zero_mul]
  · intro ha
    exact absurd (Finset.mem_univ a) ha

/-- The quadratic form of `blockZ` equals the difference of the two block weights
[JanzingWocjan2010]. -/
theorem blockZ_expect (φ : Fin 2 × ι → ℝ) :
    φ ⬝ᵥ (blockZ *ᵥ φ) = outProb φ 0 - outProb φ 1 := by
  have hstep : φ ⬝ᵥ (blockZ *ᵥ φ) = ∑ a, (if a.1 = 0 then (1 : ℝ) else -1) * (φ a) ^ 2 := by
    rw [dotProduct]
    apply Finset.sum_congr rfl
    intro a _
    rw [blockZ_mulVec]
    ring
  rw [hstep, Fintype.sum_prod_type, Fin.sum_univ_two]
  norm_num
  simp only [outProb]
  ring

/-- The quadratic form of the transpose-conjugated block sign matrix equals the output-weight
difference of the transformed vector [JanzingWocjan2010]. -/
theorem conj_blockZ_expect (Y : Matrix (Fin 2 × ι) (Fin 2 × ι) ℝ) (ξ : Fin 2 × ι → ℝ) :
    ξ ⬝ᵥ ((Yᵀ * (blockZ * Y)) *ᵥ ξ) = outProb (Y *ᵥ ξ) 0 - outProb (Y *ᵥ ξ) 1 := by
  have h1 : (Yᵀ * (blockZ * Y)) *ᵥ ξ = Yᵀ *ᵥ ((blockZ * Y) *ᵥ ξ) := by rw [mulVec_mulVec]
  have h2 : (blockZ * Y) *ᵥ ξ = blockZ *ᵥ (Y *ᵥ ξ) := by rw [mulVec_mulVec]
  have h3 : ξ ⬝ᵥ (Yᵀ *ᵥ (blockZ *ᵥ (Y *ᵥ ξ)))
      = (ξ ᵥ* Yᵀ) ⬝ᵥ (blockZ *ᵥ (Y *ᵥ ξ)) := by rw [dotProduct_mulVec]
  have h4 : ξ ᵥ* Yᵀ = Y *ᵥ ξ := by rw [vecMul_transpose]
  rw [h1, h2, h3, h4]
  exact blockZ_expect _

end SigmaZ

/-- A positive multiple of `p - q` is positive exactly when `q < p`, and negative exactly when
`p < q` [JanzingWocjan2010]. -/
theorem delta_sign_iff_outcome {Δ k p q : ℝ} (hk : 0 < k) (h : Δ = k * (p - q)) :
    (0 < Δ ↔ q < p) ∧ (Δ < 0 ↔ p < q) := by
  constructor <;> rw [h] <;> constructor <;> intro h' <;> nlinarith

/-- Bounds a finite spectral moment by `lam₀ ^ m` when all bases have absolute value at most
nonnegative `lam₀` and the absolute weights sum to at most one [JanzingWocjan2010]. -/
theorem spectral_sum_growth_bound {κ : Type} [Fintype κ] (lam w : κ → ℝ) {lam₀ : ℝ}
    (hlam₀ : 0 ≤ lam₀) (hlam : ∀ j, |lam j| ≤ lam₀) (hw : ∑ j, |w j| ≤ 1) (m : ℕ) :
    |∑ j, (lam j) ^ m * w j| ≤ lam₀ ^ m := by
  have h1 : |∑ j, (lam j) ^ m * w j| ≤ ∑ j, |lam j| ^ m * |w j| := by
    refine (Finset.abs_sum_le_sum_abs (fun j => (lam j) ^ m * w j) Finset.univ).trans_eq ?_
    apply Finset.sum_congr rfl
    intro j _
    rw [abs_mul, abs_pow]
  have h2 : ∑ j, |lam j| ^ m * |w j| ≤ ∑ j, lam₀ ^ m * |w j| := by
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (hlam j) m) (abs_nonneg _)
  have h3 : ∑ j, lam₀ ^ m * |w j| = lam₀ ^ m * ∑ j, |w j| := by rw [Finset.mul_sum]
  have h4 : lam₀ ^ m * ∑ j, |w j| ≤ lam₀ ^ m * 1 :=
    mul_le_mul_of_nonneg_left hw (pow_nonneg hlam₀ m)
  linarith

/-- If two distinct summands equal `dom` and the sum of the absolute remaining terms is at most
`rest ≤ dom`, then the full sum is at least `dom`. -/
theorem sum_lower_of_two_dominant {κ : Type} [Fintype κ] [DecidableEq κ] (f : κ → ℝ) (p q : κ)
    {dom rest : ℝ} (hpq : p ≠ q) (hp : f p = dom) (hq : f q = dom)
    (hrest : ∑ j ∈ Finset.univ.filter (fun j => j ≠ p ∧ j ≠ q), |f j| ≤ rest)
    (hdom : rest ≤ dom) :
    dom ≤ ∑ j, f j := by
  classical
  set T : Finset κ := Finset.univ.filter (fun j => j ≠ p ∧ j ≠ q) with hT
  have hmemT : ∀ j, j ∈ T ↔ j ≠ p ∧ j ≠ q := by
    intro j; simp [hT]
  have hpT : p ∉ T := by
    rw [hmemT]; exact fun h => h.1 rfl
  have hqT : q ∉ T := by
    rw [hmemT]; exact fun h => h.2 rfl
  have hpnot : p ∉ insert q T := by
    rw [Finset.mem_insert, not_or]
    exact ⟨hpq, hpT⟩
  have hins : insert p (insert q T) = (Finset.univ : Finset κ) := by
    ext j
    simp only [Finset.mem_insert, hmemT, Finset.mem_univ, iff_true]
    by_cases h1 : j = p
    · exact Or.inl h1
    · by_cases h2 : j = q
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr ⟨h1, h2⟩)
  have hsum : (∑ j, f j) = f p + f q + ∑ j ∈ T, f j := by
    have hfirst : (∑ j, f j) = ∑ j ∈ insert p (insert q T), f j := by rw [hins]
    rw [hfirst, Finset.sum_insert hpnot, Finset.sum_insert hqT]
    ring
  have h1 : |∑ j ∈ T, f j| ≤ ∑ j ∈ T, |f j| := Finset.abs_sum_le_sum_abs f T
  have h2 : -(∑ j ∈ T, |f j|) ≤ ∑ j ∈ T, f j := (abs_le.mp h1).1
  have h3 : ∑ j ∈ T, |f j| ≤ rest := by rw [hT]; exact hrest
  rw [hsum, hp, hq]
  linarith

/-- Two equal dominant spectral contributions give a lower bound of one dominant contribution
when the absolute remainder is bounded by that contribution [JanzingWocjan2010]. -/
theorem lineGraph_gap_bound {κ : Type} [Fintype κ] [DecidableEq κ] (lam w : κ → ℝ) (p q : κ)
    {m : ℕ} {lam₀ lam₁ w₀ : ℝ} (hpq : p ≠ q)
    (hp : (lam p) ^ m * w p = lam₀ ^ m * w₀)
    (hq : (lam q) ^ m * w q = lam₀ ^ m * w₀)
    (hmid : ∑ j ∈ Finset.univ.filter (fun j => j ≠ p ∧ j ≠ q),
        |(lam j) ^ m * w j| ≤ lam₁ ^ m)
    (hratio : lam₁ ^ m ≤ lam₀ ^ m * w₀) :
    lam₀ ^ m * w₀ ≤ ∑ j, (lam j) ^ m * w j :=
  sum_lower_of_two_dominant (fun j => (lam j) ^ m * w j) p q hpq hp hq hmid hratio

/-- A spectral value `-lam₀` paired with the parity-adjusted weight `(-1) ^ m * w₀` contributes
`lam₀ ^ m * w₀` to the moment [JanzingWocjan2010]. -/
theorem dom_weight_eq {lam₀ w₀ lamq wq : ℝ} {m : ℕ} (hlam : lamq = -lam₀)
    (hw : wq = (-1 : ℝ) ^ m * w₀) : lamq ^ m * wq = lam₀ ^ m * w₀ := by
  rw [hlam, hw, neg_pow]
  have h2 : (-1 : ℝ) ^ m * (-1 : ℝ) ^ m = 1 := by
    rw [← sq, ← pow_mul, show m * 2 = 2 * m by ring, pow_mul]
    norm_num
  calc (-1 : ℝ) ^ m * lam₀ ^ m * ((-1 : ℝ) ^ m * w₀)
      = ((-1 : ℝ) ^ m * (-1 : ℝ) ^ m) * (lam₀ ^ m * w₀) := by ring
    _ = lam₀ ^ m * w₀ := by rw [h2, one_mul]

end Qatlib.Papers.StringRewrite07.MainResults
