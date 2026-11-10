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
open scoped Matrix.Norms.L2Operator
open Matrix

namespace Qatlib.Papers.ManyBodyFermi97.MainResults

def blockIndex (n : ℕ) : ℕ := n / 2

def parityIndex (n : ℕ) : ℕ := n % 2

theorem blockIndex_parity_injective :
    Function.Injective (fun n : ℕ => (n / 2, n % 2)) := by
  intro a b h
  have h1 : a / 2 = b / 2 := congrArg Prod.fst h
  have h2 : a % 2 = b % 2 := congrArg Prod.snd h
  have ha : 2 * (a / 2) + a % 2 = a := Nat.div_add_mod a 2
  have hb : 2 * (b / 2) + b % 2 = b := Nat.div_add_mod b 2
  omega

theorem kinetic_split (m : ℕ) (t : ℂ) :
    chainHopping m t = evenBlocks m t + oddBlocks m t :=
  chainHopping_eq_blocks m t

theorem block_diagonal_zero (m : ℕ) (t : ℂ) (i : Fin m) :
    evenBlocks m t i i = 0 :=
  evenBlocks_diagonal_zero m t i

theorem block_split_and_budget_arithmetic {m q : ℕ} (hq : 1 ≤ q) (t : ℂ) :
    chainHopping m t = evenBlocks m t + oddBlocks m t ∧
      (∀ i j : Fin m, evenBlocks m t i j ≠ 0 → i.val / 2 = j.val / 2) ∧
      firstQuantHubbardStepCost q ≤ 14 * q ^ 2 :=
  ⟨chainHopping_eq_blocks m t, evenBlocks_block_diagonal m t,
    firstQuantHubbardStepCost_bound hq⟩

theorem block_evolution_jets {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (k : ℕ) :
    iteratedDeriv k (fun t : ℝ => NormedSpace.exp (t • H)) 0 = H ^ k :=
  local_evolution_jets H k

end Qatlib.Papers.ManyBodyFermi97.MainResults
