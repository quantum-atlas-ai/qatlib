/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOASupremacy16.LocalGadget.Source

/-!
# Postselected branch words and normalized laws

`BranchLayer` describes Hadamard layers and arbitrary diagonal multipliers on a qubit with
workspace. Replacing each Hadamard by its gadget branch scales the whole word by a power of the
nonzero scalar `1 / sqrt 2`, so normalized Born laws agree whenever the original output has
positive total mass.

This development accompanies the study of QAOA sampling and postselection in [FarhiHarrow2016].

## Main statements

* `branch_foldr_eq_smul`: Evaluating a word of gadget branches equals evaluating the original
  word scaled by `(1 / sqrt 2)` raised to its total Hadamard count.
* `branch_word_normalized_law`: If the original word output has positive total Born mass, the
  branch word and original word have equal normalized probability at every specified output.

## References

* [Farhi and Harrow, 2016][FarhiHarrow2016]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Qatlib.Papers.QAOASupremacy16.BranchWords

open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.QAOASupremacy16.CircuitDefs
open Qatlib.Papers.QAOASupremacy16.LocalGadget
open scoped BigOperators

variable {ι : Type*}

/-- A layer that is either a Hadamard on the first qubit or multiplication by a specified
complex diagonal function. -/
inductive BranchLayer (ι : Type*) where

  | hadamard : BranchLayer ι

  | diag (f : Bool × ι → ℂ) : BranchLayer ι

/-- Evaluates a layer using the original Hadamard or the specified diagonal multiplier. -/
noncomputable def BranchLayer.evalOrig : BranchLayer ι → QState (Bool × ι) → QState (Bool × ι)
  | .hadamard => hadamardOnFst
  | .diag f => fun ψ p => f p * ψ p

/-- Evaluates a layer using the postselected gadget state in place of a Hadamard, retaining
diagonal multipliers. -/
noncomputable def BranchLayer.evalBranch : BranchLayer ι → QState (Bool × ι) → QState (Bool × ι)
  | .hadamard => gadgetState
  | .diag f => fun ψ p => f p * ψ p

/-- Counts one for a Hadamard layer and zero for a diagonal layer. -/
def BranchLayer.countH : BranchLayer ι → ℕ
  | .hadamard => 1
  | .diag _ => 0

/-- Original layer evaluation commutes with complex scalar multiplication of the input state. -/
theorem BranchLayer.evalOrig_smul (c : ℂ) (L : BranchLayer ι) (ψ : QState (Bool × ι)) :
    L.evalOrig (c • ψ) = c • L.evalOrig ψ := by
  cases L with
  | hadamard => exact hadamardOnFst_smul c ψ
  | diag f =>
      funext p
      simp only [BranchLayer.evalOrig, Pi.smul_apply, smul_eq_mul]
      ring

/-- Branch evaluation equals original evaluation scaled by `(1 / sqrt 2)` raised to the layer
Hadamard count. -/
theorem BranchLayer.evalBranch_eq_smul (L : BranchLayer ι) (ψ : QState (Bool × ι)) :
    L.evalBranch ψ = ((Real.sqrt 2 : ℂ)⁻¹) ^ L.countH • L.evalOrig ψ := by
  cases L with
  | hadamard =>
      simpa [BranchLayer.evalBranch, BranchLayer.evalOrig, BranchLayer.countH] using
          gadget_identity ψ
  | diag f =>
      funext p
      simp [BranchLayer.evalBranch, BranchLayer.evalOrig, BranchLayer.countH]

/-- Evaluating a word of gadget branches equals evaluating the original word scaled by `(1 /
sqrt 2)` raised to its total Hadamard count. -/
theorem branch_foldr_eq_smul (ls : List (BranchLayer ι)) (ψ : QState (Bool × ι)) :
    ls.foldr BranchLayer.evalBranch ψ
      = ((Real.sqrt 2 : ℂ)⁻¹) ^ (ls.map BranchLayer.countH).sum
          • ls.foldr BranchLayer.evalOrig ψ := by
  induction ls with
  | nil => simp
  | cons L ls ih =>
      rw [List.foldr_cons, List.map_cons, List.sum_cons, List.foldr_cons, ih,
        BranchLayer.evalBranch_eq_smul, BranchLayer.evalOrig_smul, smul_smul, ← pow_add]

/-- The complex gadget scalar `(sqrt 2)⁻¹` is nonzero. -/
theorem gadgetScalar_ne_zero : ((Real.sqrt 2 : ℂ)⁻¹) ≠ 0 := by
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)).ne'
  exact inv_ne_zero h2

variable [Fintype ι]

/-- If the original word output has positive total Born mass, the branch word and original word
have equal normalized probability at every specified output. -/
theorem branch_word_normalized_law (ls : List (BranchLayer ι)) (ψ : QState (Bool × ι))
    (hZ : 0 < ∑ q, BornProb (ls.foldr BranchLayer.evalOrig ψ) q) (p : Bool × ι) :
    normProb (ls.foldr BranchLayer.evalBranch ψ) p
      = normProb (ls.foldr BranchLayer.evalOrig ψ) p := by
  have hc : ((Real.sqrt 2 : ℂ)⁻¹) ^ (ls.map BranchLayer.countH).sum ≠ 0 :=
    pow_ne_zero _ gadgetScalar_ne_zero
  rw [branch_foldr_eq_smul]
  exact normProb_smul _ hc _ hZ p

/-- If the original word output has positive total Born mass, its normalized Born law agrees
pointwise with the branch word law. -/
theorem branch_word_normalized_law_all (ls : List (BranchLayer ι)) (ψ : QState (Bool × ι))
    (hZ : 0 < ∑ q, BornProb (ls.foldr BranchLayer.evalOrig ψ) q) :
    ∀ p, normProb (ls.foldr BranchLayer.evalBranch ψ) p
      = normProb (ls.foldr BranchLayer.evalOrig ψ) p :=
  fun p => branch_word_normalized_law ls ψ hZ p

end Qatlib.Papers.QAOASupremacy16.BranchWords
