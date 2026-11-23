module

public import Qatlib.Papers.BQPMixSparse06.WalkCounts.LiftedL2WalkBound
public import Qatlib.Papers.BQPMixSparse06.MainResults.LiftedHeatKernel

@[expose] public section

/-!
# Concrete consumer for the BQPMixSparse06 lifted walk and heat-kernel bounds

The triangle on `Fin 3` has three negative edges and unsigned degree two. Its unsigned lift
therefore uses the bit-flipping blocks. The examples exercise the Euclidean operator norm,
the walk bounds, the heat-kernel entry bounds, and the two signed heat-kernel identities.
-/

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace QatlibTests.BQPMixSparse06LiftedBoundConsumer

open Qatlib.Papers.BQPMixSparse06.MainResults
open Qatlib.Papers.BQPMixSparse06.WalkCounts.LiftedL2WalkBound
open Qatlib.Papers.BQPMixSparse06.MainResults.LiftedHeatKernel
open scoped Matrix.Norms.L2Operator

/-- The signed triangle adjacency matrix with every edge negative. -/
private def triA : Matrix (Fin 3) (Fin 3) ℤ := fun i j => if i = j then 0 else -1

/-- Every triangle entry belongs to the signed alphabet. -/
private theorem triA_entries (i j : Fin 3) :
    triA i j = -1 ∨ triA i j = 0 ∨ triA i j = 1 := by
  by_cases h : i = j <;> simp [triA, h]

/-- The signed triangle is undirected. -/
private theorem triA_symm (i j : Fin 3) : triA i j = triA j i := by
  by_cases h : i = j
  · simp [triA, h]
  · have h' : j ≠ i := fun hh => h hh.symm
    simp [triA, h, h']

/-- Every vertex of the signed triangle has unsigned degree two. -/
private theorem triA_degree (i : Fin 3) : ∑ j, |(triA i j : ℝ)| = 2 := by
  have h1 : ∀ j : Fin 3, |(triA i j : ℝ)| = 1 - (if i = j then (1 : ℝ) else 0) := by
    intro j
    by_cases h : i = j <;> simp [triA, h]
  have h2 : (∑ j : Fin 3, |(triA i j : ℝ)|) =
      ∑ j : Fin 3, (1 - (if i = j then (1 : ℝ) else 0)) :=
    Finset.sum_congr rfl (fun j _ => h1 j)
  rw [h2]
  have h3 : (∑ j : Fin 3, (1 - (if i = j then (1 : ℝ) else 0))) =
      3 - ∑ j : Fin 3, (if i = j then (1 : ℝ) else 0) := by
    rw [Finset.sum_sub_distrib]
    have hc : (∑ j : Fin 3, (1 : ℝ)) = 3 := by simp
    rw [hc]
  rw [h3]
  have h4 : (∑ j : Fin 3, (if i = j then (1 : ℝ) else 0)) = 1 := by simp
  rw [h4]
  norm_num

/-- The lift of the signed triangle has L2 operator norm at most two. -/
example : ‖blockConvert triA‖ ≤ 2 :=
  blockConvert_l2_opNorm_le triA triA_entries triA_symm 2 (by norm_num) triA_degree

/-- The uniform walk bound is invoked on the triangle with `d = 2`. -/
example :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, ∀ j : Fin 3,
      |((realCast triA) ^ m) j j| ≤ C * (2 : ℝ) ^ m :=
  lifted_walk_diagonal_l2_bound triA triA_entries triA_symm (d := 2) (by norm_num)
    triA_degree

/-- The explicit moment bound applies at the concrete order `m = 2` and vertex `0`. -/
example : |((realCast triA) ^ 2) (0 : Fin 3) (0 : Fin 3)| ≤ (2 : ℝ) ^ 2 :=
  lifted_walk_diagonal_l2_bound_forall triA triA_entries triA_symm (d := 2) (by norm_num)
    triA_degree 2 (0 : Fin 3)

/-- The paired walk difference is bounded at the positive order three. -/
example : |doubledPathDiff ((blockConvert triA) ^ 3) (0 : Fin 3)| ≤ (2 : ℝ) ^ 3 :=
  lifted_walk_difference_le_degree_pow triA triA_entries triA_symm 2 (by norm_num)
    triA_degree 3 (0 : Fin 3)

/-- The lifted heat-kernel entries are nonnegative at the concrete time `t = 1`. -/
example (p q : Fin 2 × Fin 3) :
    0 ≤ (NormedSpace.exp (-((1 : ℝ) • graphLaplacian (blockConvert triA) 2))) p q :=
  lifted_heatKernel_exp_nonneg triA triA_entries 2 (t := 1) (by norm_num) p q

/-- The uniform heat-kernel entry bound applies on the triangle for every nonnegative time. -/
example :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t → ∀ p q : Fin 2 × Fin 3,
      |(NormedSpace.exp (-(t • graphLaplacian (blockConvert triA) 2))) p q| ≤ C :=
  lifted_heatKernel_exp_bound triA triA_entries (d := 2) triA_degree

/-- The antisymmetric heat-kernel bridge transports to the signed semigroup entry at `t = 1`. -/
example :
    dot (psiMinus (0 : Fin 3))
        (Matrix.mulVec (NormedSpace.exp (-((1 : ℝ) • graphLaplacian (blockConvert triA) 2)))
          (psiMinus (0 : Fin 3))) =
      Real.exp (-((1 : ℝ) * 2)) * (NormedSpace.exp ((1 : ℝ) • realCast triA)) (0 : Fin 3) (0 : Fin 3) :=
  lifted_heatKernel_diag_bridge triA triA_entries 2 (t := 1) (0 : Fin 3)

/-- The actual heat-kernel probability difference equals the signed heat-semigroup entry. -/
example :
    cqrDoubled (NormedSpace.exp (-((1 : ℝ) • graphLaplacian (blockConvert triA) 2))) (0 : Fin 3) =
      Real.exp (-((1 : ℝ) * 2)) *
        (NormedSpace.exp ((1 : ℝ) • realCast triA)) (0 : Fin 3) (0 : Fin 3) :=
  lifted_heatKernel_difference triA triA_entries triA_symm 2 1 (0 : Fin 3)

end QatlibTests.BQPMixSparse06LiftedBoundConsumer
