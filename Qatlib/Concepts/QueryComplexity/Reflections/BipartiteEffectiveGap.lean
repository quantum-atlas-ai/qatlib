/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Real.StarOrdered
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.SplitIfs
import Qatlib.Concepts.QueryComplexity.Reflections.BipartiteEffectiveGapContracts
import Qatlib.Foundations.PureStateMath.Qubit

/-!
# Counterexample to the uncorrected bipartite gap contract

Refutes `BipartiteEffectiveGap` by constructing a bounded witness family whose marked adjacency
has a kernel vector with a nonzero root coordinate on a false input. A complete Hermitian
eigenframe converts the claimed zero-energy mass bound into a contradiction.

The counterexample concerns the uncorrected local contract; the dual-feasible, complement-marked
formulation is developed separately in the reflection-query framework of [Reichardt2011].

## Main statements

* `bipartiteEffectiveGap_contract_false`: the uncorrected bipartite effective-gap proposition is
  false.

## References

* [Reichardt, 2011][Reichardt2011]
-/

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Qatlib.Concepts.QueryComplexity.Reflections
open Matrix
open scoped BigOperators

/-- A finite Hermitian matrix possesses a complete orthonormal eigenframe indexed by a finite
natural-number range, with real eigenvalues. -/
private theorem reflections_complete_frame {S : Type} [Fintype S] [DecidableEq S]
    (A : Matrix S S ℂ) (hA : A.IsHermitian) :
    ∃ (k : ℕ) (V : Matrix S (Fin k) ℂ) (ρ : Fin k → ℝ),
      Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry V ∧ V*Vᴴ = 1 ∧
      A*V = V*diagonal (fun i => (ρ i : ℂ)) := by
  classical
  let U : Matrix S S ℂ := hA.eigenvectorUnitary
  have hU : U ∈ unitaryGroup S ℂ := hA.eigenvectorUnitary.property
  have hU1 : Uᴴ*U=1 := by simpa only [Matrix.star_eq_conjTranspose] using hU.1
  have hU2 : U*Uᴴ=1 := by simpa only [Matrix.star_eq_conjTranspose] using hU.2
  have hspec : A=U*diagonal (fun i => (hA.eigenvalues i : ℂ))*Uᴴ := by
    simpa only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
      using! hA.spectral_theorem
  have hAU : A*U=U*diagonal (fun i => (hA.eigenvalues i : ℂ)) := by
    calc
      A*U = (U*diagonal (fun i => (hA.eigenvalues i : ℂ))*Uᴴ)*U :=
        congrArg (fun M => M*U) hspec
      _ = U*diagonal (fun i => (hA.eigenvalues i : ℂ)) := by
        simp only [Matrix.mul_assoc, hU1, Matrix.mul_one]
  let e : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
  let V : Matrix S (Fin (Fintype.card S)) ℂ := fun r i => U r (e i)
  let ρ : Fin (Fintype.card S) → ℝ := fun i => hA.eigenvalues (e i)
  refine ⟨Fintype.card S,V,ρ,?_,?_,?_⟩
  · unfold Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry
    ext i j
    have he := congrFun (congrFun hU1 (e i)) (e j)
    simpa only [V, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      e.injective.eq_iff] using he
  · ext r s
    change (∑ i, U r (e i)*star (U s (e i))) = (1 : Matrix S S ℂ) r s
    calc
      (∑ i, U r (e i)*star (U s (e i))) = ∑ j : S, U r j*star (U s j) :=
        e.sum_comp (fun j => U r j*star (U s j))
      _ = (1 : Matrix S S ℂ) r s := congrFun (congrFun hU2 r) s
  · ext r i
    have he := congrFun (congrFun hAU r) (e i)
    rw [Matrix.mul_diagonal] at he ⊢
    simpa only [V, ρ, Matrix.mul_apply] using he

/-- If the zero-eigenvalue spectral mass at coordinate `r` is zero in a complete eigenframe,
every kernel vector vanishes at `r`. -/
private theorem reflections_zero_gap_kernel_coordinate
    {S : Type} [Fintype S] [DecidableEq S] (A : Matrix S S ℂ) (hA : A.IsHermitian)
    (r : S) (k : ℕ) (V : Matrix S (Fin k) ℂ) (ρ : Fin k → ℝ)
    (_hV : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry V) (hVV : V*Vᴴ=1)
    (hEV : A*V=V*diagonal (fun i => (ρ i : ℂ)))
    (hgap : (∑ i : Fin k, if |ρ i| ≤ 0 then ‖V r i‖^2 else 0) ≤ 0)
    (z : QState S) (hz : A*ᵥ z=0) : z r=0 := by
  classical
  let q := Vᴴ*ᵥ z
  have hVE : Vᴴ*A=diagonal (fun i => (ρ i : ℂ))*Vᴴ := by
    have he := congrArg Matrix.conjTranspose hEV
    simpa [Matrix.conjTranspose_mul, Matrix.diagonal_conjTranspose, hA.eq, Pi.star_def] using he
  have hq : diagonal (fun i => (ρ i : ℂ))*ᵥ q=0 := by
    dsimp only [q]
    rw [Matrix.mulVec_mulVec, ← hVE, ← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero]
  have hterm (i : Fin k) : V r i*q i=0 := by
    by_cases hρ : ρ i=0
    · have hn : (if |ρ i| ≤ 0 then ‖V r i‖^2 else 0) ≤
          ∑ j : Fin k, if |ρ j| ≤ 0 then ‖V r j‖^2 else 0 :=
        Finset.single_le_sum (f := fun j => if |ρ j| ≤ 0 then ‖V r j‖^2 else 0)
          (fun j _ => by (try dsimp only); split_ifs <;> positivity) (Finset.mem_univ i)
      have hs : ‖V r i‖^2 ≤ 0 := by simpa [hρ] using hn.trans hgap
      have hnorm : ‖V r i‖=0 := by nlinarith [norm_nonneg (V r i)]
      rw [norm_eq_zero.mp hnorm, zero_mul]
    · have he := congrFun hq i
      simp only [Matrix.mulVec_diagonal, Pi.zero_apply] at he
      have hc : (ρ i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hρ
      rw [mul_eq_zero, or_iff_right hc] at he
      rw [he, mul_zero]
  have hre : V*ᵥ q=z := by
    dsimp only [q]
    rw [Matrix.mulVec_mulVec, hVV, Matrix.one_mulVec]
  rw [← hre]
  change (∑ i : Fin k, V r i*q i)=0
  exact Finset.sum_eq_zero (fun i _ => hterm i)

/-- A column-side kernel vector of a biadjacency matrix extends by zero to a kernel vector of
its block adjacency matrix. -/
private theorem reflections_block_kernel {R C : Type} [Fintype R] [DecidableEq R]
    [Fintype C] [DecidableEq C] (B : Matrix R C ℂ) (ψ : QState C)
    (hψ : B*ᵥ ψ=0) : blockAdjacency B*ᵥ Sum.elim 0 ψ=0 := by
  ext p
  cases p <;>
    simp [blockAdjacency, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      show ∀ r, (∑ c, B r c*ψ c)=0 from congrFun hψ]

/-- The uncorrected proposition `BipartiteEffectiveGap` is false. -/
theorem bipartiteEffectiveGap_contract_false : ¬ BipartiteEffectiveGap := by
  classical
  intro h
  let input : Unit → Fin 1 → Bool := fun _ _ => false
  let f : Unit → Bool := fun _ => false
  let v : Unit → Fin 1 → Fin 1 → ℂ := fun _ _ _ => 1
  let ψ : QState (ColLab Unit f 1 1) := fun c => match c with
    | Sum.inl _ => 1
    | Sum.inr (_,b,_) => if b then -(1/3 : ℂ) else 0
  have hB : markedBiadj input f v 1 ()*ᵥ ψ=0 := by
    ext r
    cases r with
    | inl x =>
      norm_num [markedBiadj, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
        Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_succ,
        ψ, tvec, bigA, input, v]
    | inr jb =>
      rcases jb with ⟨j,b,k⟩
      fin_cases j
      fin_cases k
      cases b <;> norm_num [markedBiadj, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
        Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_succ, ψ, pixBar, input]
  let A := markedAdjacency input f v 1 ()
  have hA : A.IsHermitian := by
    change (blockAdjacency (markedBiadj input f v 1 ()))ᴴ = blockAdjacency
        (markedBiadj input f v 1 ())
    ext p q
    cases p <;> cases q <;> simp [blockAdjacency, Matrix.conjTranspose_apply]
  obtain ⟨k,V,ρ,hV,hVV,hEV⟩ := reflections_complete_frame A hA
  have hnorm : ∀ x : Unit, ∑ j : Fin 1, ∑ k : Fin 1, ‖v x j k‖^2 ≤ (1 : ℝ) := by
    intro x
    norm_num [v, Fin.sum_univ_succ]
  have hgap := (h Unit 1 1 input f v 1 hnorm (by norm_num)).2 () rfl 0 (by norm_num)
    k V ρ hV hVV hEV
  have hgap0 : (∑ i : Fin k, if |ρ i| ≤ 0 then
      ‖V (Sum.inr (Sum.inl ())) i‖^2 else 0) ≤ 0 := by
    simpa only [zero_div, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero] using hgap
  have hz : A*ᵥ Sum.elim 0 ψ=0 := reflections_block_kernel _ ψ hB
  have he := reflections_zero_gap_kernel_coordinate A hA (Sum.inr (Sum.inl ())) k V ρ
    hV hVV hEV hgap0 (Sum.elim 0 ψ) hz
  norm_num [ψ] at he

end Qatlib.Concepts.QueryComplexity.Reflections
