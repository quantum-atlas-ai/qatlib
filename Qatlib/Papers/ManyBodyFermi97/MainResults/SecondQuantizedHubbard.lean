/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ManyBodyFermi97.MainResults.Defs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Matrix

namespace Qatlib.Papers.ManyBodyFermi97.MainResults

open Qatlib.Concepts.FermionAlgebra.CarJordanWigner
open Qatlib.Foundations.PureStateMath

def interveningCount (m : ℕ) (i j : Fin m) : ℕ :=
  if i.val ≤ j.val then j.val - i.val else i.val - j.val

theorem interveningCount_le (m : ℕ) (i j : Fin m) : interveningCount m i j ≤ m := by
  unfold interveningCount
  split
  · have h := j.isLt; omega
  · have h := i.isLt; omega

theorem potential_pass_cost (m : ℕ) : secondQuantPotentialCost m = m := rfl

theorem pair_cost (m : ℕ) : secondQuantPairCost m = m + 8 := rfl

theorem chain_neighbours_card (m : ℕ) : (chainPairs m).card ≤ m :=
  chainPairs_card m

theorem second_quantized_hubbard_cost {m c : ℕ} (hm : 1 ≤ m)
    (pairs : Finset (Fin m × Fin m)) (hcard : pairs.card ≤ c * m) :
    secondQuantHubbardCost m pairs ≤ (1 + 9 * c) * m ^ 2 :=
  secondQuantHubbardCost_bound hm pairs hcard

theorem chain_hubbard_quadratic (m : ℕ) (hm : 1 ≤ m) :
    secondQuantHubbardCost m (chainPairs m) ≤ 10 * m ^ 2 :=
  chain_hubbard_cost_bound m hm

theorem numberOp_diagonal_action {m : ℕ} (i : Fin m) (x : Reg m) :
    numberOp i x x = if x i then 1 else 0 := by
  rw [num_apply]
  simp

theorem creation_eq_adjoint {m : ℕ} (i : Fin m) :
    creation i = (annihilation i)ᴴ :=
  creation_eq_conjTranspose i

end Qatlib.Papers.ManyBodyFermi97.MainResults
