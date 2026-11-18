/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.Armillary26.Instances.Rate
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
# Nonempty witnesses for the permutation-block rank interface

The first consumer uses rational matrices, so the shared rank theorem cannot
silently rely on characteristic two. The second is a compatible CSS instance
with one element per group; it checks satisfiability of the rate theorem's
premises, not the distances of the three manuscript instances.
-/

namespace QatlibTests.ArmillaryRateRegression

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Concepts.CodeCert.PermBlocks
open Qatlib.Papers.Armillary26.Instances
open scoped Matrix

/-- Two blocks over the rationals give a consumer independent of binary CSS. -/
def rationalBlocks : Fin 2 → Fin 2 → Equiv.Perm (Fin 2) := fun a b =>
  if a = 1 ∧ b = 1 then Equiv.swap 0 1 else Equiv.refl _

/-- The mixed identity/swap matrix loses at least one row rank over the rationals. -/
theorem rational_bound : Matrix.rank (permBlocks (K := ℚ) rationalBlocks) ≤ 3 := by
  have h := perm_rank_add (K := ℚ) 1 (0 : Fin 2) rationalBlocks
  norm_num at h ⊢
  omega

/-- A one-element fiber gives a nonempty, compatible retained-check example. -/
def singletonBlocks : Fin 3 → Fin 12 → Equiv.Perm (Fin 1) := fun _ _ => Equiv.refl _

/-- Twelve overlapping entries cancel in characteristic two. -/
theorem singleton_compat :
    permBlocks (K := ZMod 2) singletonBlocks *
      (permBlocks (K := ZMod 2) singletonBlocks)ᵀ = 0 := by
  ext i j
  have hi : i.2 = 0 := Subsingleton.elim _ _
  have hj : j.2 = 0 := Subsingleton.elim _ _
  norm_num [Matrix.mul_apply, Matrix.transpose_apply, permBlocks, singletonBlocks,
    Fintype.sum_prod_type, hi, hj]
  decide

/-- The structural bound has a concrete compatible consumer with positive logical dimension. -/
theorem singleton_lower :
    10 ≤ (retainedCode singletonBlocks singletonBlocks singleton_compat).encodedQubits := by
  simpa using encoded_lower (0 : Fin 1) singletonBlocks singletonBlocks singleton_compat

end QatlibTests.ArmillaryRateRegression
