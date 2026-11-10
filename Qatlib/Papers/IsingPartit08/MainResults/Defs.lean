/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical

attribute [local instance] Classical.propDecidable

namespace Qatlib.Papers.IsingPartit08.MainResults

abbrev F2Vec (R : ℕ) := Fin R → ZMod 2

def paritySign (x : ZMod 2) : ℝ := if x = 0 then 1 else -1

@[simp] theorem paritySign_zero : paritySign 0 = 1 := if_pos rfl

theorem paritySign_ne_zero {x : ZMod 2} (hx : x ≠ 0) : paritySign x = -1 := if_neg hx

def quadForm {R : ℕ} (B : Matrix (Fin R) (Fin R) (ZMod 2)) (a : F2Vec R) : ZMod 2 :=
  ∑ i, ∑ j, a i * B i j * a j

def wt {R : ℕ} (a : F2Vec R) : ℕ := (Finset.univ.filter (fun i => a i ≠ 0)).card

@[simp] theorem wt_zero_eq_zero : wt (fun _ : Fin 0 => (0 : ZMod 2)) = 0 := by
  simp [wt]

def inKernelCH {R N : ℕ} (CH : Matrix (Fin R) (Fin N) (ZMod 2)) (a : F2Vec N) : Prop :=
  ∀ i, ∑ j, CH i j * a j = 0

def kerSet {R N : ℕ} (CH : Matrix (Fin R) (Fin N) (ZMod 2)) : Finset (F2Vec N) :=
  Finset.univ.filter (fun a => inKernelCH CH a)

def signedEulerianSum {R N : ℕ} (B : Matrix (Fin N) (Fin N) (ZMod 2))
    (CH : Matrix (Fin R) (Fin N) (ZMod 2)) (lam : ℝ) : ℝ :=
  ∑ a ∈ kerSet CH, paritySign (quadForm B a) * lam ^ wt a

def eulerianSum {R N : ℕ} (CH : Matrix (Fin R) (Fin N) (ZMod 2)) (lam : ℝ) : ℝ :=
  ∑ a ∈ kerSet CH, lam ^ wt a

def parityCondition {R N : ℕ} (B : Matrix (Fin N) (Fin N) (ZMod 2))
    (CH : Matrix (Fin R) (Fin N) (ZMod 2)) : Prop :=
  ∀ a ∈ kerSet CH, quadForm B a = 0

def normalizerOf (lam : ℝ) (edges : ℕ) : ℝ := Real.sqrt ((lam ^ 2 + 1) ^ edges)

structure AnsatzGate (R : ℕ) where

  b : F2Vec R

def HadamardTestEstimate (q p m : ℝ) : Prop := |m - q| ≤ p

def MasterCorrespondence (q normalizer s : ℝ) : Prop := q * normalizer = s

end Qatlib.Papers.IsingPartit08.MainResults
