/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeGadgetTransport

@[expose] public section
open Qatlib.Concepts.ProbabilityCore.DistributionAA

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Qatlib.Concepts.ProbabilityCore.DistributionAA
open scoped Classical BigOperators

def cubeIndicatorPolynomial {n : ℕ} (x : Fin n → Bool) : MvPolynomial (Fin n) ℝ :=
  ∏ i, if x i then MvPolynomial.X i else 1-MvPolynomial.X i

/-- Shows that the cube indicator polynomial evaluates to one at its defining vector and zero
elsewhere. -/
theorem cube_indicator_polynomial_eval {n : ℕ} (x y : Fin n → Bool) :
    MvPolynomial.eval (fun i => if y i then (1 : ℝ) else 0) (cubeIndicatorPolynomial x) =
      if x=y then 1 else 0 := by
  unfold cubeIndicatorPolynomial
  rw [MvPolynomial.eval_prod]
  have he (i) : MvPolynomial.eval (fun j => if y j then (1 : ℝ) else 0)
      (if x i then MvPolynomial.X i else 1-MvPolynomial.X i) = if x i=y i then 1 else 0 := by
    cases x i <;> cases hy : y i <;> simp [hy]
  simp only [he]
  by_cases hxy : x=y
  · subst y; simp
  · rw [ite_eq_right hxy]
    obtain ⟨i,hi⟩ : ∃ i, x i ≠ y i := Function.ne_iff.1 hxy
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

/-- Bounds the degree of a cube indicator polynomial by the dimension. -/
theorem cube_indicator_polynomial_degree {n : ℕ} (x : Fin n → Bool) :
    (cubeIndicatorPolynomial x).totalDegree ≤ n := by
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  calc
    _ ≤ ∑ _i : Fin n, 1 := by
      apply Finset.sum_le_sum
      intro i _
      cases x i
      · exact (MvPolynomial.totalDegree_sub _ _).trans (by simp)
      · simp
    _ = n := by simp

/-- Shows that every real function on the Boolean cube has degree at most the dimension. -/
theorem cube_function_degree {n : ℕ} (f : (Fin n → Bool) → ℝ) : CubeDegreeLE n f := by
  let P : MvPolynomial (Fin n) ℝ := ∑ x, MvPolynomial.C (f x)*cubeIndicatorPolynomial x
  have hP : P.totalDegree ≤ n := by
    apply MvPolynomial.totalDegree_finsetSum_le
    intro x _
    exact (MvPolynomial.totalDegree_mul _ _).trans
        (by simpa using cube_indicator_polynomial_degree x)
  have he (y) : MvPolynomial.eval (fun i => if y i then (1 : ℝ) else 0) P=f y := by
    simp only [P,MvPolynomial.eval_sum,MvPolynomial.eval_mul,MvPolynomial.eval_C,cube_indicator_polynomial_eval]
    simp
  simpa only [he] using cube_degree_of_mv_polynomial P hP

/-- Bounds the degree of a block composition by the original degree times the block size. -/
theorem cube_block_degree {n m d : ℕ} {f : (Fin n → Bool) → ℝ} (hf : CubeDegreeLE d f)
    (g : (Fin m → Bool) → Bool) : CubeDegreeLE (d*m) (fun z => f (cubeBlockMap g z)) := by
  obtain ⟨P,hP,hPe⟩ := cube_degree_to_mv_polynomial hf
  obtain ⟨G,hG,hGe⟩ :=
      cube_degree_to_mv_polynomial (cube_function_degree (fun z => if g z then (1 : ℝ) else 0))
  let Q : Fin n → MvPolynomial (Fin (n*m)) ℝ :=
      fun i => MvPolynomial.rename (fun j => finProdFinEquiv (i,j)) G
  have hQ (i) : (Q i).totalDegree ≤ m := (MvPolynomial.totalDegree_rename_le _ G).trans hG
  have hdeg : (P.eval₂ MvPolynomial.C Q).totalDegree ≤ d*m :=
    (cube_mv_substitution_degree P Q hQ).trans (by simpa only [Nat.mul_comm] using Nat.mul_le_mul_left m hP)
  have he (z : Fin (n*m) → Bool) :
      MvPolynomial.eval (fun k => if z k then (1 : ℝ) else 0) (P.eval₂ MvPolynomial.C Q) = f (cubeBlockMap g z) := by
    rw [← MvPolynomial.eval_assoc]
    change MvPolynomial.eval
        (fun i => MvPolynomial.eval (fun k => if z k then (1 : ℝ) else 0) (Q i)) P = _
    have hvars : (fun i => MvPolynomial.eval (fun k => if z k then (1 : ℝ) else 0) (Q i)) =
        (fun i => if cubeBlockMap g z i then (1 : ℝ) else 0) := by
      ext i
      rw [MvPolynomial.eval_rename]
      change MvPolynomial.eval (fun j => if cubeBlocksEquiv n m z i j then (1 : ℝ) else 0) G =
        if g (cubeBlocksEquiv n m z i) then (1 : ℝ) else 0
      exact hGe _
    rw [hvars,hPe]
  simpa only [he] using cube_degree_of_mv_polynomial (P.eval₂ MvPolynomial.C Q) hdeg

end Qatlib.Concepts.ProbabilityCore.DistributionAA
