/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.LieStrang.CommutatorProductFormula
import Qatlib.Concepts.TrotterFormula.SuzukiFourth.SuzukiFourthOrder
import Mathlib.Analysis.Calculus.Taylor

/-!
# Raw nested commutator budgets and a Taylor counterexample

This module defines `pfNestedCommList` and the raw tuple sums `pfCommAlphaInner` and
`pfCommAlphaSelf` used in product-formula error estimates. These budgets provide the algebraic
quantities appearing in commutator-scaling analyses such as [ChildsEtAl2021Trotter].

It also constructs an order-zero counterexample to a proposed conjugation estimate using a
Taylor polynomial through degree `p`, and deduces that the stated uniform skew-Hermitian
estimate is false.

## Main statements

* `pfNestedCommList`: successive commutation along a matrix list.
* `pf_comm_alpha_inner_zero`: the order-zero seeded budget is the seed norm.
* `pf_conjugation_zero_order_counterexample`: a two-dimensional counterexample to the proposed
  bound.
* `pf_conjugation_expansion_skew_impossible`: failure of the proposed uniform estimate.

## References

* [Childs et al., 2021][ChildsEtAl2021Trotter]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Qatlib.Concepts.TrotterFormula.LieStrang
open Qatlib.Concepts.TrotterFormula.SuzukiFourth

namespace Qatlib.Concepts.TrotterFormula.GeneralOrder
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- The nested commutator obtained by starting with the first matrix and successively applying
`pfComm Y` for each remaining matrix; the empty list gives zero. -/
noncomputable def pfNestedCommList {I : Type} [Fintype I] :
    List (Matrix I I ℂ) → Matrix I I ℂ
  | [] => 0
  | X :: l => l.foldl (fun D Y => pfComm Y D) X

/-- The list of matrices selected from `xs` by the finite tuple `idx`, in tuple order. -/
def pfChosenList {I : Type} [Fintype I] (xs : List (Matrix I I ℂ)) {k : ℕ}
    (idx : Fin k → Fin xs.length) : List (Matrix I I ℂ) :=
  (List.finRange k).map (fun j => xs.getD (idx j : ℕ) 0)

/-- The sum over all length-`k` tuples of generators of the norms of nested commutators seeded
by `B`. -/
noncomputable def pfCommAlphaInner {I : Type} [Fintype I] (xs : List (Matrix I I ℂ))
    (B : Matrix I I ℂ) (k : ℕ) : ℝ :=
  ∑ idx : Fin k → Fin xs.length,
    ‖pfNestedCommList (B :: pfChosenList xs idx)‖

/-- The sum of the norms of nested commutators over all length-`k` tuples drawn from `xs`. -/
noncomputable def pfCommAlphaSelf {I : Type} [Fintype I] (xs : List (Matrix I I ℂ))
    (k : ℕ) : ℝ :=
  ∑ idx : Fin k → Fin xs.length, ‖pfNestedCommList (pfChosenList xs idx)‖

set_option backward.isDefEq.respectTransparency false

/-- The inner commutator budget at order zero equals the norm of its seed matrix. -/
theorem pf_comm_alpha_inner_zero {I : Type} [Fintype I] [DecidableEq I]
    (xs : List (Matrix I I ℂ)) (B : Matrix I I ℂ) : pfCommAlphaInner xs B 0 = ‖B‖ := by
  simp [pfCommAlphaInner, pfChosenList, pfNestedCommList]

/-- There exists a two-dimensional skew-Hermitian word whose error relative to the degree-zero
Taylor polynomial exceeds the proposed order-zero inner commutator bound. -/
theorem pf_conjugation_zero_order_counterexample :
    ∃ (xs : List (Matrix (Fin 2) (Fin 2) ℂ)) (B : Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ),
      (∀ X ∈ xs, Xᴴ = -X) ∧
      pfCommAlphaInner xs B 0*|t|^0/(Nat.factorial 0 : ℝ) <
        ‖suzukiExponentialWord xs t*B*Ring.inverse (suzukiExponentialWord xs t)-
          taylorWithinEval (fun s => suzukiExponentialWord xs s*B*
            Ring.inverse (suzukiExponentialWord xs s)) 0 Set.univ 0 t‖ := by
  letI : NormedAlgebra ℚ (Matrix (Fin 2) (Fin 2) ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
  let X : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![0, (Real.pi : ℂ)*Complex.I]
  let B : Matrix (Fin 2) (Fin 2) ℂ := !![0,1;0,0]
  let V : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![1,-1]
  have hX : Xᴴ = -X := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [X, Matrix.diagonal, Matrix.conjTranspose_apply, RCLike.star_def]
  have hB : B ≠ 0 := by
    intro hz
    have he := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 1) hz
    norm_num [B] at he
  have hex : NormedSpace.exp X = V := by
    rw [show X = Matrix.diagonal ![0, (Real.pi : ℂ)*Complex.I] from rfl, Matrix.exp_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [V, Matrix.diagonal, Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]
  have heneg : NormedSpace.exp (-X) = V := by
    rw [show -X = Matrix.diagonal ![0, -((Real.pi : ℂ)*Complex.I)] from by
      ext i j; fin_cases i <;> fin_cases j <;> simp [X, Matrix.diagonal], Matrix.exp_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [V, Matrix.diagonal, Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]
  have hword1 : suzukiExponentialWord [X] 1 = NormedSpace.exp X := by simp [suzukiExponentialWord]
  have hword0 : suzukiExponentialWord [X] 0 = 1 := by simp [suzukiExponentialWord]
  have hinv : Ring.inverse (NormedSpace.exp X) = NormedSpace.exp (-X) := by
    simpa only [NormedSpace.exp_eq_tsum_rat] using! Ring.inverse_exp X
  have he : suzukiExponentialWord [X] 1*B*Ring.inverse (suzukiExponentialWord [X] 1)-
      taylorWithinEval (fun s => suzukiExponentialWord [X] s*B*
        Ring.inverse (suzukiExponentialWord [X] s)) 0 Set.univ 0 1 = (-2 : ℝ) • B := by
    rw [taylor_within_zero_eval, hword1, hinv, hex, heneg, hword0]
    simp only [one_mul, Ring.inverse_one, mul_one]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [V, B, Matrix.diagonal, Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨[X], B, 1, ?_, ?_⟩
  · intro Y hY
    have hy : Y = X := List.mem_singleton.mp hY
    simpa only [hy] using! hX
  · rw [pf_comm_alpha_inner_zero, he]
    norm_num [norm_smul]
    linarith only [norm_pos_iff.mpr hB]

/-- The proposed uniform bound for conjugation error relative to the degree-`p` Taylor
polynomial, with coefficient `pfCommAlphaInner xs B p / p!`, is false even for
skew-Hermitian generators. -/
theorem pf_conjugation_expansion_skew_impossible :
    ¬ (∀ (I : Type) [Fintype I] [DecidableEq I] (xs : List (Matrix I I ℂ))
      (B : Matrix I I ℂ) (p : ℕ) (t : ℝ), (∀ X ∈ xs, Xᴴ = -X) →
      ‖suzukiExponentialWord xs t*B*Ring.inverse (suzukiExponentialWord xs t)-
        taylorWithinEval (fun s => suzukiExponentialWord xs s*B*
          Ring.inverse (suzukiExponentialWord xs s)) p Set.univ 0 t‖ ≤
        pfCommAlphaInner xs B p*|t|^p/(p.factorial : ℝ)) := by
  intro h
  obtain ⟨xs, B, t, hskew, hlt⟩ := pf_conjugation_zero_order_counterexample
  exact (not_le_of_gt hlt) (h (Fin 2) xs B 0 t hskew)

end Qatlib.Concepts.TrotterFormula.GeneralOrder
