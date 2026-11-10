/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonSparseHam09.MainResults.Defs
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section

open Matrix Finset
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.NonSparseHam09.MainResults

noncomputable def AvgSuccess {M B : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    (A : QuantumQueryAlgorithm (Fin M → Bool) W) (accept : Finset W) : ℝ := by
  classical
  exact 1 / ((promiseStrings M B).card : ℝ) *
    ∑ b ∈ promiseStrings M B,
      (if ∑ i, signVec b i = (B : ℝ) then acceptProb (A.run b) accept
       else 1 - acceptProb (A.run b) accept)

def AvgAlgo (M B q : ℕ) : Prop :=
  ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : QuantumQueryAlgorithm (Fin M → Bool) W) (accept : Finset W),
    A.queryCount ≤ q ∧ (2 : ℝ) / 3 ≤ AvgSuccess (B := B) A accept

def lemma2Statement (M B : ℕ) (hB : 0 < B) (hP : (promiseStrings M B).Nonempty) : Prop :=
  ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
    (∀ q : ℕ, AvgAlgo M B q → c₁ * (M : ℝ) / (B : ℝ) ≤ (q : ℝ)) ∧
    AvgAlgo M B (Nat.ceil (c₂ * (M : ℝ) / (B : ℝ)))

lemma AvgAlgo_mono {M B q q' : ℕ} (hq : q ≤ q') (h : AvgAlgo M B q) :
    AvgAlgo M B q' := by
  obtain ⟨W, fW, dW, A, accept, hcount, hsucc⟩ := h
  exact ⟨W, fW, dW, A, accept, hcount.trans hq, hsucc⟩

end Qatlib.Papers.NonSparseHam09.MainResults
