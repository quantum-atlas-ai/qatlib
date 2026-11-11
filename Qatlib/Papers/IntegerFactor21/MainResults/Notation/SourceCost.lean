/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Source cost vocabulary for Harvey--Hittmeir, arXiv:2105.11105v1

The paper writes `lg n := ⌊log n / log 2⌋ + 1` (§2, p.2) and measures all
running times in bit operations on a deterministic Turing machine.  This file
fixes that vocabulary in Lean:

* `lg N` is the integer bit length used by the paper;
* `RuntimeIn` is the paper's `O(·)` shape for an algorithm whose input carries
  a size parameter `N` and, possibly, a secondary parameter satisfying the
  paper's `n = O(N)` convention (Remark 2.2, p.3): the constant is allowed to
  depend on the constant hidden in `n = O(N)`, uniformly in `n` and `N`.

The source theorems are imported from the paper layer only through these
notions, so a later replacement of the cost model does not change any
mathematical statement.
-/

set_option autoImplicit false

namespace Qatlib.Papers.IntegerFactor21.MainResults.Notation

/-- The paper's bit length `lg n = ⌊log n / log 2⌋ + 1` (§2, p.2). -/
def lg (n : ℕ) : ℕ := Nat.log 2 n + 1

/-- The bit length is positive for every positive integer. -/
theorem lg_pos {n : ℕ} (_hn : 0 < n) : 0 < lg n := by
  simp only [lg]
  omega

/-- `lg 1 = 1`, matching the paper's observation `lg n ≥ 1` for `n ≥ 1`. -/
@[simp] theorem lg_one : lg 1 = 1 := by
  simp [lg]

/-- The paper's big-O convention for a cost `cost n N` bounded by
`C * bound n N`, where the secondary input satisfies `n = O(N)`.
The constant hidden in `n = O(N)` is the outermost `C₀`; the constant `C` may
depend on it, exactly as Remark 2.2 (p.3) stipulates. -/
def RuntimeIn (cost bound : ℕ → ℕ → ℕ) : Prop :=
  ∀ C₀ : ℕ, ∃ C : ℕ, ∀ n N : ℕ, 1 ≤ n → n ≤ C₀ * N → cost n N ≤ C * bound n N

/-- `RuntimeIn` is monotone in the bounding function. -/
theorem runtimeIn_mono {cost bound bound' : ℕ → ℕ → ℕ}
    (h : RuntimeIn cost bound) (hle : ∀ n N, bound n N ≤ bound' n N) :
    RuntimeIn cost bound' := by
  intro C₀
  obtain ⟨C, hC⟩ := h C₀
  exact ⟨C, fun n N hn hN => (hC n N hn hN).trans (Nat.mul_le_mul_left C (hle n N))⟩

/-- A one-parameter version of the paper's `O(·)` for input size `N`. -/
def RuntimeInOne (cost bound : ℕ → ℕ) : Prop :=
  ∃ C : ℕ, ∀ N : ℕ, 2 ≤ N → cost N ≤ C * bound N

/-- The paper's big-O convention for algorithms with two secondary inputs
`n, κ = O(N)` (Lemma 2.3, Proposition 4.2). -/
def RuntimeIn3 (cost bound : ℕ → ℕ → ℕ → ℕ) : Prop :=
  ∀ C₀ : ℕ, ∃ C : ℕ, ∀ n κ N : ℕ, 1 ≤ n → 1 ≤ κ → n ≤ C₀ * N → κ ≤ C₀ * N →
    cost n κ N ≤ C * bound n κ N

end Qatlib.Papers.IntegerFactor21.MainResults.Notation
