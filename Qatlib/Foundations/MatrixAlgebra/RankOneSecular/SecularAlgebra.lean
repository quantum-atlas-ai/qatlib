/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Action.Pi
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Hom
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Ring.CompTypeclasses
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.FunLike.Equiv
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Rat.Init
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Insert
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Logic.Equiv.Defs
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.LinearCombination.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

/-!
# Secular equations for diagonal rank-one perturbations

`diagonalMinusRankOne` defines a real diagonal matrix minus a real multiple of a complex
rank-one outer product. `resolventVector` and `secularSum` describe its eigenvectors and scalar
secular equation away from the diagonal poles.

`secular_iff_eigenvalue` proves the equivalence between the secular equation and a nonzero
eigenvector, and the remaining lemmas show that each such eigenspace lies in the span of its
resolvent vector. This is finite rank-one spectral algebra in the setting of [Bhatia1997].

## Main statements

* `eigenvector_scalar`: every eigenvector away from the poles is a specified multiple of the
  resolvent vector.
* `secular_iff_eigenvalue`: the secular equation characterizes real eigenvalues away from the
  poles.
* `eigenvector_mem_span`: the corresponding eigenspace lies in a single-vector span.

## References

* [Bhatia, 1997][Bhatia1997]
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Matrix
open scoped Classical BigOperators
namespace Qatlib.Foundations.MatrixAlgebra.RankOneSecular
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The diagonal matrix with real entries `d i`, minus `a` times the outer product of `u` with
its conjugate. -/
def diagonalMinusRankOne (d : I→ℝ) (u : I→ℂ) (a : ℝ) : Matrix I I ℂ :=
  Matrix.diagonal (fun i=>(d i:ℂ))-(a:ℂ)•Matrix.vecMulVec u (star u)

/-- The vector with coordinates `u i / (d i - z)`. -/
def resolventVector (d : I→ℝ) (u : I→ℂ) (z : ℝ) : I→ℂ :=
  fun i=>u i/((d i-z:ℝ):ℂ)

/-- The real secular sum `∑ i, normSq (u i) / (d i - z)`. -/
def secularSum (d : I→ℝ) (u : I→ℂ) (z : ℝ) : ℝ :=
  ∑i,Complex.normSq (u i)/(d i-z)

/-- The coordinate action of the diagonal rank-one perturbation separates into the diagonal term
and the rank-one overlap term. -/
theorem action (d : I→ℝ) (u x : I→ℂ) (a : ℝ) (i : I) :
    (diagonalMinusRankOne d u a *ᵥ x) i=
      (d i:ℂ)*x i-(a:ℂ)*u i*(∑j,star (u j)*x j) := by
  simp [diagonalMinusRankOne,Matrix.mulVec,dotProduct,Matrix.diagonal,Matrix.vecMulVec,
    sub_mul,Finset.sum_sub_distrib,Finset.mul_sum,mul_assoc]

/-- The eigenvector equation for the rank-one perturbation is equivalent to its coordinate
equations with factors `d i - z`. -/
theorem eigen_equation_iff (d : I→ℝ) (u x : I→ℂ) (a z : ℝ) :
    diagonalMinusRankOne d u a *ᵥ x=(z:ℂ)•x ↔
      ∀i,((d i-z:ℝ):ℂ)*x i=(a:ℂ)*u i*(∑j,star (u j)*x j) := by
  rw [funext_iff]
  apply forall_congr'
  intro i
  rw [action]
  change (d i:ℂ)*x i-(a:ℂ)*u i*(∑j,star (u j)*x j)=(z:ℂ)*x i ↔ _
  push_cast
  constructor <;> intro h <;> linear_combination h

omit [Fintype I] in

/-- A real diagonal matrix minus a real multiple of `u * uᴴ` equals its conjugate transpose. -/
theorem hermitian (d : I→ℝ) (u : I→ℂ) (a : ℝ) :
    (diagonalMinusRankOne d u a)ᴴ =diagonalMinusRankOne d u a := by
  ext i j
  simp only [diagonalMinusRankOne,Matrix.conjTranspose_apply,Matrix.sub_apply,
    Matrix.smul_apply,Matrix.vecMulVec_apply,Pi.star_apply,smul_eq_mul,map_sub,map_mul,
    Complex.star_def,Complex.conj_ofReal]
  by_cases h : i=j
  · subst j; simp [mul_comm,mul_left_comm]
  · simp [h,Ne.symm h,mul_comm,mul_left_comm]

omit [DecidableEq I] in

/-- The pairing of `u` with its resolvent vector equals the complex cast of the real secular
sum. -/
theorem resolvent_pairing (d : I→ℝ) (u : I→ℂ) (z : ℝ) :
    (∑i,star (u i)*resolventVector d u z i)=(secularSum d u z:ℂ) := by
  unfold secularSum
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  simp only [resolventVector,Complex.ofReal_sub]
  have he : star (u i)*u i=(Complex.normSq (u i):ℂ) := by
    apply Complex.ext
    · simp [Complex.normSq_apply]
    · simp [mul_comm]
  rw [← mul_div_assoc,he]

omit [Fintype I] [DecidableEq I] in

/-- Away from all diagonal poles, a nonzero vector `u` has a nonzero resolvent vector. -/
theorem resolvent_ne_zero (d : I→ℝ) (u : I→ℂ) (z : ℝ)
    (hpole : ∀i,d i≠z) (hu : u≠0) : resolventVector d u z≠0 := by
  intro h
  apply hu
  funext i
  have hi:=congrFun h i
  have hd : ((d i-z:ℝ):ℂ)≠0 := by exact_mod_cast sub_ne_zero.mpr (hpole i)
  change u i/((d i-z:ℝ):ℂ)=0 at hi
  exact (div_eq_zero_iff.mp hi).resolve_right hd

/-- Away from the diagonal poles, any eigenvector at `z` is the resolvent vector scaled by `a`
times its overlap with `u`. -/
theorem eigenvector_scalar (d : I→ℝ) (u x : I→ℂ) (a z : ℝ)
    (hpole : ∀i,d i≠z) (heig : diagonalMinusRankOne d u a *ᵥ x=(z:ℂ)•x) :
    x=((a:ℂ)*(∑j,star (u j)*x j))•resolventVector d u z := by
  have hs:=(eigen_equation_iff d u x a z).mp heig
  funext i
  have hd : ((d i-z:ℝ):ℂ)≠0 := by exact_mod_cast sub_ne_zero.mpr (hpole i)
  change x i=((a:ℂ)*(∑j,star (u j)*x j))*(u i/((d i-z:ℝ):ℂ))
  rw [← mul_div_assoc]
  apply (eq_div_iff hd).mpr
  linear_combination hs i

/-- A nonzero eigenvector away from the diagonal poles has nonzero overlap with `u`. -/
theorem eigenvector_overlap_ne_zero (d : I→ℝ) (u x : I→ℂ) (a z : ℝ)
    (hpole : ∀i,d i≠z) (hx : x≠0) (heig : diagonalMinusRankOne d u a *ᵥ x=(z:ℂ)•x) :
    (∑j,star (u j)*x j)≠0 := by
  intro hc
  have he:=eigenvector_scalar d u x a z hpole heig
  rw [hc,mul_zero,zero_smul] at he
  exact hx he

/-- A nonzero eigenvector away from the diagonal poles satisfies the scalar secular equation `a
* secularSum d u z = 1`. -/
theorem secular_of_eigenvector (d : I→ℝ) (u x : I→ℂ) (a z : ℝ)
    (hpole : ∀i,d i≠z) (hx : x≠0) (heig : diagonalMinusRankOne d u a *ᵥ x=(z:ℂ)•x) :
    a*secularSum d u z=1 := by
  let c:=∑j,star (u j)*x j
  have hc : c≠0 := eigenvector_overlap_ne_zero d u x a z hpole hx heig
  have hrepr:=eigenvector_scalar d u x a z hpole heig
  have he : c=((a:ℂ)*c)*(secularSum d u z:ℂ) := by
    calc
      c=∑j,star (u j)*(((a:ℂ)*c)*resolventVector d u z j) := by
        change (∑j,star (u j)*x j)=_
        apply Finset.sum_congr rfl
        intro j _
        exact congrArg (fun w : ℂ=>star (u j)*w) (congrFun hrepr j)
      _=∑j,((a:ℂ)*c)*(star (u j)*resolventVector d u z j) := by
        apply Finset.sum_congr rfl
        intro j _
        ring
      _=((a:ℂ)*c)*(∑j,star (u j)*resolventVector d u z j) := (Finset.mul_sum _ _ _).symm
      _=((a:ℂ)*c)*(secularSum d u z:ℂ) := by rw [resolvent_pairing]
  have hh : (a:ℂ)*(secularSum d u z:ℂ)=1 := by
    apply mul_left_cancel₀ hc
    calc
      c*((a:ℂ)*(secularSum d u z:ℂ))=((a:ℂ)*c)*(secularSum d u z:ℂ) := by ring
      _=c := he.symm
      _=c*1 := (mul_one _).symm
  exact_mod_cast hh

/-- Away from the diagonal poles, the secular equation makes the resolvent vector satisfy the
eigenvector equation at `z`. -/
theorem eigenvector_of_secular (d : I→ℝ) (u : I→ℂ) (a z : ℝ)
    (hpole : ∀i,d i≠z) (hsec : a*secularSum d u z=1) :
    diagonalMinusRankOne d u a *ᵥ resolventVector d u z=(z:ℂ)•resolventVector d u z := by
  apply (eigen_equation_iff d u _ a z).mpr
  intro i
  have hd : ((d i-z:ℝ):ℂ)≠0 := by exact_mod_cast sub_ne_zero.mpr (hpole i)
  have hc : (a:ℂ)*(∑j,star (u j)*resolventVector d u z j)=1 := by
    rw [resolvent_pairing]
    exact_mod_cast hsec
  change ((d i-z:ℝ):ℂ)*(u i/((d i-z:ℝ):ℂ))=(a:ℂ)*u i*(∑j,star (u j)*resolventVector d u z j)
  calc
    _=u i := by field_simp
    _=u i*((a:ℂ)*(∑j,star (u j)*resolventVector d u z j)) := by rw [hc,mul_one]
    _=_ := by ring

/-- For nonzero `u` and `z` away from the diagonal poles, the secular equation holds exactly
when the perturbed matrix has a nonzero eigenvector at `z`. -/
theorem secular_iff_eigenvalue (d : I→ℝ) (u : I→ℂ) (a z : ℝ)
    (hpole : ∀i,d i≠z) (hu : u≠0) :
    a*secularSum d u z=1 ↔ ∃x:I→ℂ,x≠0 ∧diagonalMinusRankOne d u a *ᵥ x=(z:ℂ)•x := by
  constructor
  · intro h
    exact ⟨resolventVector d u z,resolvent_ne_zero d u z hpole hu,eigenvector_of_secular d u a z hpole h⟩
  · rintro ⟨x,hx,he⟩
    exact secular_of_eigenvector d u x a z hpole hx he

/-- Every eigenvector at a real value away from the diagonal poles belongs to the span of the
resolvent vector. -/
theorem eigenvector_mem_span (d : I→ℝ) (u x : I→ℂ) (a z : ℝ)
    (hpole : ∀i,d i≠z) (heig : diagonalMinusRankOne d u a *ᵥ x=(z:ℂ)•x) :
    x∈Submodule.span ℂ {resolventVector d u z} := by
  rw [eigenvector_scalar d u x a z hpole heig]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

/-- The coefficient expressing a nonzero eigenvector as a multiple of its resolvent vector is
nonzero away from the poles. -/
theorem eigenvector_scalar_ne_zero (d : I→ℝ) (u x : I→ℂ) (a z : ℝ)
    (hpole : ∀i,d i≠z) (hx : x≠0) (heig : diagonalMinusRankOne d u a *ᵥ x=(z:ℂ)•x) :
    ((a:ℂ)*(∑j,star (u j)*x j))≠0 := by
  intro h
  have he:=eigenvector_scalar d u x a z hpole heig
  rw [h,zero_smul] at he
  exact hx he

/-- For nonzero `u` away from the diagonal poles, the secular equation is equivalent to the
resolvent vector satisfying the eigenvector equation. -/
theorem secular_iff_resolvent_eigenvector (d : I→ℝ) (u : I→ℂ) (a z : ℝ)
    (hpole : ∀i,d i≠z) (hu : u≠0) :
    a*secularSum d u z=1 ↔
      diagonalMinusRankOne d u a *ᵥ resolventVector d u z=(z:ℂ)•resolventVector d u z := by
  constructor
  · exact eigenvector_of_secular d u a z hpole
  · exact secular_of_eigenvector d u _ a z hpole (resolvent_ne_zero d u z hpole hu)

end Qatlib.Foundations.MatrixAlgebra.RankOneSecular
