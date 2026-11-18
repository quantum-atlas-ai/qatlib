/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import QatlibTests.ToolkitProgramBorn
public import Qatlib.Concepts.QPrograms.QueryBilling
public import Qatlib.Concepts.QPrograms.ProdDist

@[expose] public section

/-! # Query billing and independence for measurement programs

The cost model is exercised on a two-round adaptive example (`adaptPol` on `rho34`): an explicit query-cost instance prices the empty history at
one query and the one-step histories at one (after outcome zero) or five (after outcome one)
queries, and the four two-round trajectories are billed 2, 2, 6, 6. The worst-case bill is the
computed supremum six, strictly between the expected bill 114/25 (zero-weight histories
contribute nothing) and the loose uniform bound 2 * 5 from `worstQLe`. The negative example
checks that the chained adaptive weight 9/25 is not the i.i.d. square 81/625, and the
independence bridge cross-checks the joint weight of two one-round programs on the product
input against the public Born weight of the product state. These are program-level billing and
independence semantics, not the five-site-chain SU(2) rotation claim of the paper.
-/

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.QPrograms.MeasureProg
open Qatlib.Concepts.QPrograms.QueryBilling
open Qatlib.Concepts.QPrograms.ProdDist
open QatlibTests.ToolkitProgram

namespace QatlibTests.ToolkitProgramBilling

/-- Query-cost instance: the empty history bills one query, the one-step history after outcome
zero bills one query, and every other history bills five queries. -/
def billCost (h : List (Fin 2)) : ℕ :=
  if h = [] then 1 else if h = [0] then 1 else 5

/-- The empty history bills one query. -/
theorem billCostNil : billCost [] = 1 :=
  rfl

/-- The one-step zero history bills one query. -/
theorem billCostZero : billCost [0] = 1 := by
  simp [billCost]

/-- The one-step one history bills five queries. -/
theorem billCostOne : billCost [1] = 5 := by
  simp [billCost]

/-- Every history bills at most five queries under the instance. -/
theorem billCostLe (h : List (Fin 2)) : billCost h ≤ 5 := by
  unfold billCost
  split
  · omega
  · split <;> omega

/-- A length-two trajectory list is its two outcomes in order. -/
theorem ofFnTwo (xs : Fin 2 → Fin 2) : List.ofFn xs = [xs 0, xs 1] := by
  rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
  simp only [Fin.succ_zero_eq_one]

/-- Both trajectories starting with outcome zero are billed two queries. -/
theorem billZeroHead (b : Fin 2) : progQCost billCost [0, b] = 2 := by
  rw [progQCostTwo, billCostNil, billCostZero]

/-- Both trajectories starting with outcome one are billed six queries. -/
theorem billOneHead (b : Fin 2) : progQCost billCost [1, b] = 6 := by
  rw [progQCostTwo, billCostNil, billCostOne]

/-- The four two-round trajectory bills are 2, 2, 6, 6. -/
theorem fourBills :
    progQCost billCost [0, 0] = 2 ∧ progQCost billCost [0, 1] = 2 ∧
      progQCost billCost [1, 0] = 6 ∧ progQCost billCost [1, 1] = 6 :=
  ⟨billZeroHead 0, billZeroHead 1, billOneHead 0, billOneHead 1⟩

/-- The worst-case two-round bill is six, the computed supremum over the four trajectories. -/
theorem worstQAdapt : worstQ billCost 2 = 6 := by
  refine le_antisymm (Finset.sup_le fun xs _ => ?_) ?_
  · rw [ofFnTwo xs, progQCostTwo, billCostNil]
    have h := billCostLe [xs 0]
    omega
  · have h := worstQGe billCost 2 (![1, 0] : Fin 2 → Fin 2)
    rwa [show List.ofFn (![1, 0] : Fin 2 → Fin 2) = [1, 0] from by decide,
      progQCostTwo, billCostNil, billCostOne] at h

/-- The loose uniform bound of `worstQLe` here is ten, not tight against the computed worst
case six. -/
theorem worstQAdaptLe10 : worstQ billCost 2 ≤ 2 * 5 :=
  worstQLe billCost 2 5 billCostLe

/-- The expected two-round bill is one hundred fourteen twenty-fifths: the two zero-weight
histories contribute nothing. -/
theorem expQAdapt : expQ adaptPol rho34 billCost 2 = 114 / 25 := by
  have hset : (Finset.univ : Finset (Fin 2 → Fin 2))
      = {![0, 0], ![0, 1], ![1, 0], ![1, 1]} := by decide
  have e00 : (progQCost billCost (List.ofFn (![0, 0] : Fin 2 → Fin 2)) : ℝ) = 2 := by
    rw [show List.ofFn (![0, 0] : Fin 2 → Fin 2) = [0, 0] from by decide]
    exact_mod_cast billZeroHead 0
  have e01 : (progQCost billCost (List.ofFn (![0, 1] : Fin 2 → Fin 2)) : ℝ) = 2 := by
    rw [show List.ofFn (![0, 1] : Fin 2 → Fin 2) = [0, 1] from by decide]
    exact_mod_cast billZeroHead 1
  have e10 : (progQCost billCost (List.ofFn (![1, 0] : Fin 2 → Fin 2)) : ℝ) = 6 := by
    rw [show List.ofFn (![1, 0] : Fin 2 → Fin 2) = [1, 0] from by decide]
    exact_mod_cast billOneHead 0
  have e11 : (progQCost billCost (List.ofFn (![1, 1] : Fin 2 → Fin 2)) : ℝ) = 6 := by
    rw [show List.ofFn (![1, 1] : Fin 2 → Fin 2) = [1, 1] from by decide]
    exact_mod_cast billOneHead 1
  rw [expQ, hset]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton,
    fourHistMass.1, fourHistMass.2.1, fourHistMass.2.2.1, fourHistMass.2.2.2,
    e00, e01, e10, e11]
  norm_num

/-- The expected bill is at most the worst case by the general theorem on the density input. -/
theorem expQAdaptLe : expQ adaptPol rho34 billCost 2 ≤ (worstQ billCost 2 : ℝ) :=
  expQLeWorst adaptPol rho34Density billCost 2

/-- The expected bill is strictly below the worst case on this instance. -/
theorem expQAdaptLt : expQ adaptPol rho34 billCost 2 < (worstQ billCost 2 : ℝ) := by
  rw [expQAdapt, worstQAdapt]
  norm_num

/-- The zero-weight trajectory [0, 1] contributes exactly zero to the expected bill. -/
theorem expQZeroTerm :
    histProb adaptPol rho34 2 ![0, 1]
      * (progQCost billCost (List.ofFn (![0, 1] : Fin 2 → Fin 2)) : ℝ) = 0 :=
  expQTermZero adaptPol rho34 billCost 2 ![0, 1] fourHistMass.2.1

/-- The chained two-round weight is not the square of the one-round weight: the adaptive
trajectory is not i.i.d. sampling. -/
theorem notIid00 : progProb adaptPol rho34 [0, 0]
    ≠ progProb adaptPol rho34 [0] * progProb adaptPol rho34 [0] := by
  rw [histMass00, roundOneBorn, bornMass0]
  norm_num

/-- Independence of disjoint copies: the joint weight of two one-round programs on the product
input equals the Born weight of the product state at the paired outcome. -/
theorem pairWeightBorn (b₁ b₂ : Fin 2) :
    pairWeight adaptPol adaptPol rho34 rho34 [b₁] [b₂]
      = BornProb (TensorState psi34 psi34) (b₁, b₂) := by
  rw [pairWeightEq adaptPol adaptPol rho34Density.1 rho34Density.1, roundOneBorn, roundOneBorn,
    bornProb_tensorState]

/-- The joint weight of outcomes zero and zero is eighty-one six-hundred twenty-fifths, the
square of the single-copy Born weight. -/
theorem pairWeight00 : pairWeight adaptPol adaptPol rho34 rho34 [0] [0] = 81 / 625 := by
  rw [pairWeightBorn, bornProb_tensorState, bornMass0]
  norm_num

/-- The Born history weights of the two-round program on the density input form a finite
distribution whose masses are exactly the four history weights. -/
theorem histDistAdapt :
    (histDist adaptPol rho34Density 2).prob ![1, 0] = 16 / 25 := by
  rw [histDistProb, histProb,
    show List.ofFn (![1, 0] : Fin 2 → Fin 2) = [1, 0] from by decide]
  exact histMass10

end QatlibTests.ToolkitProgramBilling
