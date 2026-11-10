/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Log
import Mathlib.Tactic
import Qatlib.Papers.HiddenSubgrp04.MainResults.Defs
import Qatlib.Papers.HiddenSubgrp04.MainResults.LemmaA15
set_option warningAsError false

set_option autoImplicit false

open scoped BigOperators

namespace Qatlib.Papers.HiddenSubgrp04.MainResults

noncomputable section

def lemma_A11Statement (L M N : ℕ) (hN : 13 ≤ N) (hNodd : Odd N)
    (hL : 2 ≤ L) (hM : 16 * N ≤ M)
    (hLpow : ∃ a : ℕ, L = 2 ^ a) (hMpow : ∃ b : ℕ, M = 2 ^ b)
    (u : Fin N → ℂ) (hu : l2 u = 1) : Prop :=
    l2 (fun k : Fin M => ∑ i : Fin N, cyclicQFT u i * Tvec L M N i.val k) ≤
      (2 / Real.pi) *
        Real.sqrt (22 * (Real.log (N : ℝ)) ^ 2 / (L : ℝ) +
          32 * (N : ℝ) ^ 2 / ((L : ℝ) * (M : ℝ)))

def lemma_A12Statement (L M N : ℕ) (hN : 13 ≤ N) (hNodd : Odd N)
    (hL : 16 ≤ L) (hM : L * N ≤ M)
    (hLpow : ∃ a : ℕ, L = 2 ^ a) (hMpow : ∃ b : ℕ, M = 2 ^ b)
    (i : Fin N) : Prop :=
    l2 (fun k : Fin M => Svec L M N i.val k - Bvec L M N i.val k) ≤
      Real.pi * (L : ℝ) * (N : ℝ) / (M : ℝ) * Real.sqrt 3

def lemma_A13Statement (L M N : ℕ) (hN : 13 ≤ N) (hL : 16 ≤ L) (hM : L * N ≤ M)
    (hLpow : ∃ a : ℕ, L = 2 ^ a) (hMpow : ∃ b : ℕ, M = 2 ^ b) (i : Fin N) : Prop :=
    DeltaVec M N (Svec L M N i.val) =
      tensorVec (fun j : Fin N => if j = i then 1 else 0) (garbageVec L M N)

def theorem_A14Statement (L M N : ℕ) (hN : 13 ≤ N) (hNodd : Odd N)
    (hL : 16 ≤ L) (hM : L * N ≤ M)
    (hLpow : ∃ a : ℕ, L = 2 ^ a) (hMpow : ∃ b : ℕ, M = 2 ^ b)
    (u : Fin N → ℂ) (hu : l2 u = 1) : Prop :=
    l2 (fun p => algOutput L M N u p - tensorVec (cyclicQFT u) (garbageVec L M N) p) ≤
      (2 / Real.pi) *
          Real.sqrt (22 * (Real.log (N : ℝ)) ^ 2 / (L : ℝ) +
            32 * (N : ℝ) ^ 2 / ((L : ℝ) * (M : ℝ))) +
        Real.pi * (L : ℝ) * (N : ℝ) / (M : ℝ) * Real.sqrt 3

def theoremA17ErrorBound (L M N : ℕ) : ℝ :=
  (2 / Real.pi) *
      Real.sqrt (22 * (Real.log (N : ℝ)) ^ 2 / (L : ℝ) +
        32 * (N : ℝ) ^ 2 / ((L : ℝ) * (M : ℝ))) +
    Real.pi * (L : ℝ) * (N : ℝ) / (M : ℝ) * Real.sqrt 3

def theorem_A17_part1Statement (N : ℕ) (hNodd : Odd N) (hN : 13 ≤ N)
    (ε : ℝ) (hε0 : 0 < ε) (hε2 : ε ≤ Real.sqrt 2)
    (L M : ℕ) (hL16 : 16 ≤ L) (hM : L * N ≤ M)
    (hLpow : ∃ a : ℕ, L = 2 ^ a) (hMpow : ∃ b : ℕ, M = 2 ^ b)
    (h179 : theoremA17ErrorBound L M N ≤ ε * Real.sqrt 2)
    (u : Fin N → ℂ) (hu : l2 u = 1) : Prop :=
    ∃ ψ : Fin (2 * alphaNat M N + 1) → ℂ,
      l2 ψ = 1 ∧
        l2 (fun p => algOutput L M N u p - tensorVec (cyclicQFT u) ψ p) ≤ ε

def theorem_A17_part2Statement : Prop :=
    ∃ c1 c2 : ℝ,
      65 ≤ c1 ∧ c1 ≤ 2 * 65 ∧ 735 ≤ c2 ∧ c2 ≤ 2 * 735 ∧
        ∀ (N : ℕ), Odd N → 13 ≤ N → ∀ ε : ℝ, 0 < ε → ε ≤ Real.sqrt 2 →
          ∃ L M : ℕ,
            (∃ a : ℕ, L = 2 ^ a) ∧ (∃ b : ℕ, M = 2 ^ b) ∧
              16 ≤ L ∧ L * N ≤ M ∧
              c1 * Real.sqrt (N : ℝ) / ε ^ 2 ≤ (L : ℝ) ∧
              (L : ℝ) < 2 * (c1 * Real.sqrt (N : ℝ) / ε ^ 2) ∧
              c2 * (N : ℝ) * Real.sqrt (N : ℝ) / ε ^ 3 ≤ (M : ℝ) ∧
              (M : ℝ) < 2 * (c2 * (N : ℝ) * Real.sqrt (N : ℝ) / ε ^ 3) ∧
              theoremA17ErrorBound L M N ≤ ε * Real.sqrt 2

def qubitsUsed (M : ℕ) : ℕ := Nat.clog 2 M + 2

theorem theorem_A17_part3_qubits (M : ℕ) : qubitsUsed M = Nat.clog 2 M + 2 := rfl

def theorem_A17_part3_sufficient_qubitsStatement (N : ℕ) (hNodd : Odd N) (hN : 13 ≤ N)
    (ε : ℝ) (hε0 : 0 < ε) (hε2 : ε ≤ Real.sqrt 2) : Prop :=
    ∃ M : ℕ, (∃ b : ℕ, M = 2 ^ b) ∧ 16 ≤ M ∧
      qubitsUsed M ≤ Nat.ceil (12.53 + 3 * Real.logb 2 (Real.sqrt (N : ℝ) / ε))

def paperOperationComplexity (M : ℕ) (ε : ℝ) : ℝ :=
  Real.log (M : ℝ) * (Real.log (Real.log (M : ℝ)) + Real.log (1 / ε))

def theorem_A17_part4Statement (N L M : ℕ) (ε : ℝ) (hε0 : 0 ≤ ε)
    (u : Fin N → ℂ) (ψ : Fin (2 * alphaNat M N + 1) → ℂ) (hψ : l2 ψ = 1)
    (hclose : l2 (fun p =>
      algOutput L M N u p - tensorVec (cyclicQFT u) ψ p) ≤ ε) : Prop :=
    tvDist (algOutput L M N u) (tensorVec (cyclicQFT u) ψ) ≤ 2 * ε + ε ^ 2

end

end Qatlib.Papers.HiddenSubgrp04.MainResults
