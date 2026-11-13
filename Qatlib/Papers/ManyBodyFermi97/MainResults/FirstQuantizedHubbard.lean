/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ManyBodyFermi97.MainResults.Defs

/-!
# First-quantized Hubbard block decomposition

This module formalizes the two-site block indexing and hopping decomposition used in the
first-quantized Hubbard discussion of [AbramsLloyd1997]. The quotient and remainder modulo two
determine a site uniquely, and `kinetic_split` separates the hopping matrix into even and odd
blocks.

The combined theorem `block_split_and_budget_arithmetic` records the even-block support
condition and the bound 14q² for the defined step-cost model. Matrix-exponential derivatives at
zero are also identified with powers of the generator.

## Main statements

* `blockIndex_parity_injective`: Block and parity indices uniquely identify a natural-number
  site.
* `block_split_and_budget_arithmetic`: The kinetic decomposition, support condition, and modeled
  step budget.

## References

* [Abrams and Lloyd, 1997][AbramsLloyd1997]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open scoped Matrix.Norms.L2Operator
open Matrix

namespace Qatlib.Papers.ManyBodyFermi97.MainResults

/-- The two-site block index n / 2 of a natural-number site. -/
def blockIndex (n : ℕ) : ℕ := n / 2

/-- The parity index n modulo two of a natural-number site. -/
def parityIndex (n : ℕ) : ℕ := n % 2

/-- The map sending n to its quotient and remainder on division by two is injective. -/
theorem blockIndex_parity_injective :
    Function.Injective (fun n : ℕ => (n / 2, n % 2)) := by
  intro a b h
  have h1 : a / 2 = b / 2 := congrArg Prod.fst h
  have h2 : a % 2 = b % 2 := congrArg Prod.snd h
  have ha : 2 * (a / 2) + a % 2 = a := Nat.div_add_mod a 2
  have hb : 2 * (b / 2) + b % 2 = b := Nat.div_add_mod b 2
  omega

/-- The open-chain hopping matrix is the sum of its even and odd block components. -/
theorem kinetic_split (m : ℕ) (t : ℂ) :
    chainHopping m t = evenBlocks m t + oddBlocks m t :=
  chainHopping_eq_blocks m t

/-- The even-block hopping matrix has zero diagonal. -/
theorem block_diagonal_zero (m : ℕ) (t : ℂ) (i : Fin m) :
    evenBlocks m t i i = 0 :=
  evenBlocks_diagonal_zero m t i

/-- For q ≥ 1, combines the even/odd hopping decomposition, the support of nonzero even-block
entries within two-site blocks, and the modeled step-cost bound 14q² [AbramsLloyd1997]. -/
theorem block_split_and_budget_arithmetic {m q : ℕ} (hq : 1 ≤ q) (t : ℂ) :
    chainHopping m t = evenBlocks m t + oddBlocks m t ∧
      (∀ i j : Fin m, evenBlocks m t i j ≠ 0 → i.val / 2 = j.val / 2) ∧
      firstQuantHubbardStepCost q ≤ 14 * q ^ 2 :=
  ⟨chainHopping_eq_blocks m t, evenBlocks_block_diagonal m t,
    firstQuantHubbardStepCost_bound hq⟩

/-- The kth derivative at zero of t ↦ exp(tH) equals the kth power of the matrix H. -/
theorem block_evolution_jets {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (k : ℕ) :
    iteratedDeriv k (fun t : ℝ => NormedSpace.exp (t • H)) 0 = H ^ k :=
  local_evolution_jets H k

end Qatlib.Papers.ManyBodyFermi97.MainResults
