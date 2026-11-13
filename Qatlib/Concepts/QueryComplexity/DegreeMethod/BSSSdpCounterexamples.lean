/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.BSSSdpOriginalContract
import Qatlib.Concepts.OrderedOracle.TiSdpBridge.BSSSdpSymmetry
import Mathlib.Tactic.FinCases

/-!
# A counterexample to a query SDP symmetry contract

This module constructs a three-input feasible matrix family showing that
`BssConjugateOriginalContract` is false. The matrices are built from positive semidefinite outer
products and query phase conjugations; background on positive matrices and semidefinite
optimization is given in [Watrous2018].

The counterexample concerns the particular simultaneous reindexing encoded by the original
contract. The auxiliary theorem `bss_hadamard_posSemidef` verifies positivity under a query sign
matrix.

## Main statements

* `bss_hadamard_posSemidef`: entrywise multiplication by a query sign matrix preserves positive
  semidefiniteness.
* `toy_feasible`: the explicit matrix family satisfies the feasibility constraints.
* `not_BssConjugateOriginalContract`: the original conjugation contract fails.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.OrderedOracle.TiSdpBridge

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace Qatlib.Concepts.QueryComplexity.DegreeMethod
open scoped Classical BigOperators ComplexOrder

/-- The complex query phase, equal to minus one for a true input bit and one for a false input
bit. -/
def bssPhase {X : Type} {m : ℕ} (bit : X → Fin m → Bool) (i : Fin m) (x : X) : ℂ :=
  if bit x i then -1 else 1

/-- Entrywise multiplication by `bssE bit i` preserves positive semidefiniteness. -/
theorem bss_hadamard_posSemidef {X : Type} [Fintype X] [DecidableEq X] {m : ℕ}
    (bit : X → Fin m → Bool) (i : Fin m) (A : Matrix X X ℂ) (hA : A.PosSemidef) :
    (Matrix.hadamard (bssE bit i) A).PosSemidef := by
  let d := bssPhase bit i
  have hsign (x : X) : star (d x)=d x := by
    dsimp [d,bssPhase]
    split_ifs <;> simp
  have he (x y : X) : bssE bit i x y=d x*d y := by
    cases hx : bit x i <;> cases hy : bit y i <;> simp [bssE,d,bssPhase,hx,hy]
  have hmat : Matrix.hadamard (bssE bit i) A=(Matrix.diagonal d).conjTranspose*A*Matrix.diagonal d := by
    ext x y
    rw [Matrix.diagonal_conjTranspose,Matrix.mul_diagonal,Matrix.diagonal_mul]
    simp only [Matrix.hadamard_apply,he]
    change d x*d y*A x y=star (d x)*A x y*d y
    rw [hsign]
    ring
  rw [hmat]
  exact hA.conjTranspose_mul_mul_same (Matrix.diagonal d)

/-- The elements zero and one of `Fin 3` are distinct. -/
private theorem toyFin01 : (0 : Fin 3)≠1 := by decide

/-- The elements zero and two of `Fin 3` are distinct. -/
private theorem toyFin02 : (0 : Fin 3)≠2 := by decide

/-- The elements one and zero of `Fin 3` are distinct. -/
private theorem toyFin10 : (1 : Fin 3)≠0 := by decide

/-- The elements one and two of `Fin 3` are distinct. -/
private theorem toyFin12 : (1 : Fin 3)≠2 := by decide

/-- The elements two and zero of `Fin 3` are distinct. -/
private theorem toyFin20 : (2 : Fin 3)≠0 := by decide

/-- The elements two and one of `Fin 3` are distinct. -/
private theorem toyFin21 : (2 : Fin 3)≠1 := by decide

/-- Adding one to zero in `Fin 3` gives one. -/
private theorem toyFinAdd0 : (0 : Fin 3)+1=1 := rfl

/-- Adding one to one in `Fin 3` gives two. -/
private theorem toyFinAdd1 : (1 : Fin 3)+1=2 := rfl

/-- Adding one to two in `Fin 3` gives zero. -/
private theorem toyFinAdd2 : (2 : Fin 3)+1=0 := rfl
attribute [local simp] toyFin01 toyFin02 toyFin10 toyFin12 toyFin20 toyFin21 toyFinAdd0 toyFinAdd1 toyFinAdd2

/-- The three-input bit table whose query columns test whether the input is zero, two, or one,
respectively. -/
private def toyBit (x i : Fin 3) : Bool :=
  decide (x.val=(if i.val=0 then 0 else if i.val=1 then 2 else 1))
/-- The cyclic permutation of `Fin 3` given by addition of one. -/
private def toyShift : Equiv.Perm (Fin 3) := Equiv.addRight (1 : Fin 3)
/-- The complex outer product of a vector on `Fin 3` with its conjugate. -/
private def toyOuter (v : Fin 3 → ℂ) : Matrix (Fin 3) (Fin 3) ℂ := Matrix.vecMulVec v (star v)
/-- One-third of the outer product of the constant vector with value one. -/
private def toyQ : Matrix (Fin 3) (Fin 3) ℂ := (1/3 : ℝ) • toyOuter (fun _ => 1)
/-- The weighted sum of three coordinate-difference outer products and one coordinate basis
outer product used in the counterexample. -/
private def toyP : Matrix (Fin 3) (Fin 3) ℂ :=
  (1/2 : ℝ) • toyOuter (fun i => if i.val=0 then 1 else if i.val=1 then -1 else 0)+
  (1/3 : ℝ) • toyOuter (fun i => if i.val=0 then 1 else if i.val=2 then -1 else 0)+
  (1/3 : ℝ) • toyOuter (fun i => if i.val=1 then 1 else if i.val=2 then -1 else 0)+
  (1/3 : ℝ) • toyOuter (fun i => if i.val=2 then 1 else 0)
/-- One-sixth of the outer product of the vector with values one, one, and zero. -/
private def toyB : Matrix (Fin 3) (Fin 3) ℂ :=
  (1/6 : ℝ) • toyOuter (fun i => if i.val=2 then 0 else 1)
/-- The sum of `toyP` and `toyB` after their respective query sign transformations. -/
private def toyR : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.hadamard (bssE toyBit 0) toyP+Matrix.hadamard (bssE toyBit 1) toyB
/-- The terminal matrix obtained by entrywise multiplying `toyR` by the sign matrix for query
zero. -/
private def toyΓ : Matrix (Fin 3) (Fin 3) ℂ := Matrix.hadamard (bssE toyBit 0) toyR
/-- The time-indexed query matrix family formed from `toyQ`, `toyP`, `toyB`, and `toyR`, with
zero values at the remaining indices. -/
private def toyM (i : Fin 3) (t : ℕ) : Matrix (Fin 3) (Fin 3) ℂ :=
  if t=0 then toyQ else if t=1 then
    if i.val=0 then toyP else if i.val=1 then toyB else 0
  else if t=2 then if i.val=0 then toyR else 0 else 0

/-- The matrix `toyQ` is positive semidefinite. -/
private theorem toyQ_pos : toyQ.PosSemidef :=
  (Matrix.posSemidef_vecMulVec_self_star _).smul (by norm_num : (0 : ℝ)≤1/3)

/-- The matrix `toyP` is positive semidefinite. -/
private theorem toyP_pos : toyP.PosSemidef := by
  unfold toyP
  exact (((Matrix.posSemidef_vecMulVec_self_star _).smul (by norm_num : (0 : ℝ)≤1/2)).add
    ((Matrix.posSemidef_vecMulVec_self_star _).smul (by norm_num : (0 : ℝ)≤1/3))).add
    ((Matrix.posSemidef_vecMulVec_self_star _).smul (by norm_num : (0 : ℝ)≤1/3)) |>.add
    ((Matrix.posSemidef_vecMulVec_self_star _).smul (by norm_num : (0 : ℝ)≤1/3))

/-- The matrix `toyB` is positive semidefinite. -/
private theorem toyB_pos : toyB.PosSemidef :=
  (Matrix.posSemidef_vecMulVec_self_star _).smul (by norm_num : (0 : ℝ)≤1/6)

/-- The matrix `toyR` is positive semidefinite. -/
private theorem toyR_pos : toyR.PosSemidef :=
  (bss_hadamard_posSemidef toyBit 0 toyP toyP_pos).add (bss_hadamard_posSemidef toyBit 1 toyB toyB_pos)

/-- The terminal matrix `toyΓ` is positive semidefinite. -/
private theorem toyΓ_pos : toyΓ.PosSemidef := bss_hadamard_posSemidef toyBit 0 toyR toyR_pos

/-- The cyclic input and query shifts, together with the identity output permutation, satisfy
`IsBssSymmetry` for the counterexample bit table and constant function. -/
private theorem toy_symmetry : IsBssSymmetry toyBit (fun _ : Fin 3 => (0 : Fin 1))
    toyShift toyShift (Equiv.refl (Fin 1)) := by
  constructor
  · intro i x y
    fin_cases i <;> fin_cases x <;> fin_cases y <;>
      norm_num [bssE,toyBit,toyShift,Equiv.addRight,Fin.val_add] <;> decide
  · intro x
    rfl

/-- The explicit three-query matrix family is feasible for the constant output function with
error parameter one. -/
private theorem toy_feasible : bssFamilyFeasible toyBit (fun _ : Fin 3 => (0 : Fin 1)) 3 1
    toyM (fun _ => 0) (fun _ => toyΓ) := by
  refine ⟨?_,(fun _ => Matrix.PosSemidef.zero),(fun _ => toyΓ_pos),?_,?_,?_,?_⟩
  · intro i t
    unfold toyM
    split_ifs <;> first | exact toyQ_pos | exact toyP_pos | exact toyB_pos | exact toyR_pos | exact Matrix.PosSemidef.zero
  · intro x y
    fin_cases x <;> fin_cases y <;>
      norm_num [toyM,toyQ,toyOuter,Matrix.vecMulVec_apply,Matrix.smul_apply,RCLike.real_smul_eq_coe_mul,Fin.sum_univ_three]
  · intro t ht x y
    have ht' : t=0 ∨ t=1 := by omega
    rcases ht' with rfl | rfl <;> fin_cases x <;> fin_cases y <;>
      norm_num [toyM,toyQ,toyP,toyB,toyR,toyOuter,toyBit,bssE,Matrix.hadamard_apply,Matrix.add_apply,
        Matrix.vecMulVec_apply,Matrix.smul_apply,RCLike.real_smul_eq_coe_mul,Fin.sum_univ_three]
  · intro _ x y
    fin_cases x <;> fin_cases y <;>
      norm_num [toyM,toyΓ,toyR,toyP,toyB,toyOuter,toyBit,bssE,Matrix.hadamard_apply,Matrix.add_apply,
        Matrix.vecMulVec_apply,Matrix.smul_apply,RCLike.real_smul_eq_coe_mul,Fin.sum_univ_three,Fin.sum_univ_succ]
  · intro y
    have hy : y=(0 : Fin 1) := Subsingleton.elim _ _
    subst y
    have he : Matrix.hadamard (bssDelta (fun _ : Fin 3 => (0 : Fin 1)) 0) toyΓ=
        Matrix.diagonal (fun x => toyΓ x x) := by
      ext x y
      by_cases h : x=y
      · subst y
        simp [bssDelta,Matrix.hadamard_apply]
      · simp [bssDelta,Matrix.hadamard_apply,Matrix.diagonal,h]
    norm_num
    rw [he]
    exact Matrix.posSemidef_diagonal_iff.mpr (fun x => toyΓ_pos.diag_nonneg (i := x))

/-- The simultaneous reindexing claim `BssConjugateOriginalContract` is false. -/
theorem not_BssConjugateOriginalContract : ¬BssConjugateOriginalContract := by
  intro h
  have hf := h toyBit (fun _ : Fin 3 => (0 : Fin 1)) 3 1 toyShift toyShift (Equiv.refl (Fin 1))
    toy_symmetry toyM (fun _ => 0) (fun _ => toyΓ) toy_feasible
  have hh := hf.2.2.2.2.1 1 (by norm_num) (0 : Fin 3) (2 : Fin 3)
  norm_num [toyShift,Equiv.addRight,Fin.val_add,toyM,toyQ,toyP,toyB,toyR,toyOuter,toyBit,bssE,
    Matrix.hadamard_apply,Matrix.add_apply,Matrix.of_apply,Matrix.vecMulVec_apply,Matrix.smul_apply,
    RCLike.real_smul_eq_coe_mul,Fin.sum_univ_three] at hh
end Qatlib.Concepts.QueryComplexity.DegreeMethod
