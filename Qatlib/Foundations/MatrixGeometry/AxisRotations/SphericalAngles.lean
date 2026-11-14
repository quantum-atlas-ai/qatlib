/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Logic.Function.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Tactic
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

/-!
# Recursive spherical angle coordinates

`coefficients` defines real spherical coordinates recursively using sine and cosine of doubled
angles. The head and tail lemmas expose the recursion, and `circle_angle` supplies the
two-dimensional base parametrization.

`exists_angles` proves that every real unit vector with at least two coordinates has such an
angle representation. This finite parametrization is useful for the rotation constructions
associated with [VonBurgEtAl2021].

## Main statements

* `circle_angle`: every point on the unit circle has a doubled-angle representation.
* `exists_angles`: the recursive coefficients represent every unit vector in dimension at least
  two.

## References

* [von Burg et al., 2021][VonBurgEtAl2021]
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open scoped Classical BigOperators
namespace Qatlib.Foundations.MatrixGeometry.AxisRotations.SphericalAngles

/-- The recursive spherical-coordinate vector formed from doubled angles, with initial
one-coordinate vector equal to one. -/
def coefficients : (n : ℕ)→(Fin n→ℝ)→Fin (n+1)→ℝ
  | 0,_=>fun _=>1
  | n+1,θ=>Fin.cons (Real.cos (2*θ 0)) (fun i=>Real.sin (2*θ 0)*coefficients n (fun j=>θ j.succ) i)

/-- The first spherical coefficient is the cosine of twice the first angle. -/
theorem coefficients_head (n : ℕ) (θ : Fin (n+1)→ℝ) :
    coefficients (n+1) θ 0=Real.cos (2*θ 0) := rfl

/-- Each remaining spherical coefficient is the sine of twice the first angle times the
corresponding coefficient from the remaining angles. -/
theorem coefficients_tail (n : ℕ) (θ : Fin (n+1)→ℝ) (i : Fin (n+1)) :
    coefficients (n+1) θ i.succ=Real.sin (2*θ 0)*coefficients n (fun j=>θ j.succ) i := rfl

/-- Every real pair satisfying `x^2 + y^2 = 1` is the cosine-sine pair of a doubled real angle. -/
theorem circle_angle (x y : ℝ) (h : x^2+y^2=1) :
    ∃θ : ℝ,Real.cos (2*θ)=x ∧Real.sin (2*θ)=y := by
  let z : ℂ := ⟨x,y⟩
  have hn : ‖z‖=1 := by
    rw [Complex.norm_def]
    change Real.sqrt (x*x+y*y)=1
    rw [show x*x+y*y=1 by nlinarith]
    norm_num
  have hz : z≠0 := by intro he; rw [he,norm_zero] at hn; norm_num at hn
  refine ⟨z.arg/2,?_,?_⟩
  · rw [show 2*(z.arg/2)=z.arg by ring,Complex.cos_arg hz,hn,div_one]
  · rw [show 2*(z.arg/2)=z.arg by ring,Complex.sin_arg,hn,div_one]

/-- Every real unit vector with `n + 2` coordinates is represented by `coefficients (n + 1)` for
some vector of `n + 1` real angles. -/
theorem exists_angles (n : ℕ) (u : Fin (n+2)→ℝ) (hu : ∑i,u i^2=1) :
    ∃θ : Fin (n+1)→ℝ,coefficients (n+1) θ=u := by
  induction n with
  | zero =>
    have hxy : (u 0)^2+(u 1)^2=1 := by simpa using hu
    obtain ⟨a,ha,hb⟩ := circle_angle (u 0) (u 1) hxy
    refine ⟨fun _=>a,?_⟩
    funext i
    fin_cases i <;> simp [coefficients,ha,hb]
  | succ n ih =>
    let v : Fin (n+2)→ℝ := fun i=>u i.succ
    let R := ∑i,v i^2
    let r := Real.sqrt R
    have hR : 0≤R := Finset.sum_nonneg (fun i _=>sq_nonneg (v i))
    have hr : 0≤r := Real.sqrt_nonneg R
    have hrsq : r^2=R := Real.sq_sqrt hR
    have hsplit : (u 0)^2+R=1 := by
      have he := Fin.sum_univ_succ (fun i : Fin (n+3)=>u i^2)
      rw [he] at hu
      exact hu
    have hu0 : -1≤u 0 ∧u 0≤1 := by constructor <;> nlinarith
    let a := Real.arccos (u 0)/2
    have hac : Real.cos (2*a)=u 0 := by
      rw [show 2*a=Real.arccos (u 0) by dsimp [a];ring,Real.cos_arccos hu0.1 hu0.2]
    have has : Real.sin (2*a)=r := by
      rw [show 2*a=Real.arccos (u 0) by dsimp [a];ring,Real.sin_arccos]
      congr 1
      linarith
    by_cases hz : r=0
    · have hv : ∀i,v i=0 := by
        intro i
        have hi : (v i)^2≤R := Finset.single_le_sum (fun j _=>sq_nonneg (v j)) (Finset.mem_univ i)
        rw [hz] at hrsq
        nlinarith
      refine ⟨Fin.cons a (fun _=>0),?_⟩
      funext i
      refine Fin.cases ?_ ?_ i
      · simpa only [coefficients_head,Fin.cons_zero] using hac
      · intro i
        rw [coefficients_tail,Fin.cons_zero,has,hz,zero_mul]
        exact (hv i).symm
    · have hrpos : 0<r := lt_of_le_of_ne hr (Ne.symm hz)
      let w : Fin (n+2)→ℝ := fun i=>v i/r
      have hw : ∑i,w i^2=1 := by
        simp only [w,div_pow,← Finset.sum_div]
        change R/r^2=1
        rw [← hrsq,div_self (pow_ne_zero _ hz)]
      obtain ⟨tail,htail⟩ := ih w hw
      refine ⟨Fin.cons a tail,?_⟩
      funext i
      refine Fin.cases ?_ ?_ i
      · simpa only [coefficients_head,Fin.cons_zero] using hac
      · intro i
        rw [coefficients_tail,Fin.cons_zero,has]
        change r*coefficients (n+1) tail i=u i.succ
        rw [htail]
        change r*(v i/r)=v i
        field_simp

end Qatlib.Foundations.MatrixGeometry.AxisRotations.SphericalAngles
