/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOASupremacy16.LocalGadget.Source
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Qatlib.Papers.QAOASupremacy16.BranchWords

open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.QAOASupremacy16.CircuitDefs
open Qatlib.Papers.QAOASupremacy16.LocalGadget
open scoped BigOperators

variable {ι : Type*}

inductive BranchLayer (ι : Type*) where

  | hadamard : BranchLayer ι

  | diag (f : Bool × ι → ℂ) : BranchLayer ι

noncomputable def BranchLayer.evalOrig : BranchLayer ι → QState (Bool × ι) → QState (Bool × ι)
  | .hadamard => hadamardOnFst
  | .diag f => fun ψ p => f p * ψ p

noncomputable def BranchLayer.evalBranch : BranchLayer ι → QState (Bool × ι) → QState (Bool × ι)
  | .hadamard => gadgetState
  | .diag f => fun ψ p => f p * ψ p

def BranchLayer.countH : BranchLayer ι → ℕ
  | .hadamard => 1
  | .diag _ => 0

theorem BranchLayer.evalOrig_smul (c : ℂ) (L : BranchLayer ι) (ψ : QState (Bool × ι)) :
    L.evalOrig (c • ψ) = c • L.evalOrig ψ := by
  cases L with
  | hadamard => exact hadamardOnFst_smul c ψ
  | diag f =>
      funext p
      simp only [BranchLayer.evalOrig, Pi.smul_apply, smul_eq_mul]
      ring

theorem BranchLayer.evalBranch_eq_smul (L : BranchLayer ι) (ψ : QState (Bool × ι)) :
    L.evalBranch ψ = ((Real.sqrt 2 : ℂ)⁻¹) ^ L.countH • L.evalOrig ψ := by
  cases L with
  | hadamard =>
      simpa [BranchLayer.evalBranch, BranchLayer.evalOrig, BranchLayer.countH] using
          gadget_identity ψ
  | diag f =>
      funext p
      simp [BranchLayer.evalBranch, BranchLayer.evalOrig, BranchLayer.countH]

theorem branch_foldr_eq_smul (ls : List (BranchLayer ι)) (ψ : QState (Bool × ι)) :
    ls.foldr BranchLayer.evalBranch ψ
      = ((Real.sqrt 2 : ℂ)⁻¹) ^ (ls.map BranchLayer.countH).sum
          • ls.foldr BranchLayer.evalOrig ψ := by
  induction ls with
  | nil => simp
  | cons L ls ih =>
      rw [List.foldr_cons, List.map_cons, List.sum_cons, List.foldr_cons, ih,
        BranchLayer.evalBranch_eq_smul, BranchLayer.evalOrig_smul, smul_smul, ← pow_add]

theorem gadgetScalar_ne_zero : ((Real.sqrt 2 : ℂ)⁻¹) ≠ 0 := by
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)).ne'
  exact inv_ne_zero h2

variable [Fintype ι]

theorem branch_word_normalized_law (ls : List (BranchLayer ι)) (ψ : QState (Bool × ι))
    (hZ : 0 < ∑ q, BornProb (ls.foldr BranchLayer.evalOrig ψ) q) (p : Bool × ι) :
    normProb (ls.foldr BranchLayer.evalBranch ψ) p
      = normProb (ls.foldr BranchLayer.evalOrig ψ) p := by
  have hc : ((Real.sqrt 2 : ℂ)⁻¹) ^ (ls.map BranchLayer.countH).sum ≠ 0 :=
    pow_ne_zero _ gadgetScalar_ne_zero
  rw [branch_foldr_eq_smul]
  exact normProb_smul _ hc _ hZ p

theorem branch_word_normalized_law_all (ls : List (BranchLayer ι)) (ψ : QState (Bool × ι))
    (hZ : 0 < ∑ q, BornProb (ls.foldr BranchLayer.evalOrig ψ) q) :
    ∀ p, normProb (ls.foldr BranchLayer.evalBranch ψ) p
      = normProb (ls.foldr BranchLayer.evalOrig ψ) p :=
  fun p => branch_word_normalized_law ls ψ hZ p

end Qatlib.Papers.QAOASupremacy16.BranchWords
