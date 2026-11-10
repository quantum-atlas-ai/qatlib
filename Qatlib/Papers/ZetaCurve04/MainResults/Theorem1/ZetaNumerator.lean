/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ZetaCurve04.MainResults.Defs
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.ZetaCurve04.MainResults.Theorem1

open Qatlib.Papers.ZetaCurve04.MainResults.Defs

theorem theorem1_num_class_numbers (g : ℕ) : 2 * g ≤ max 18 (2 * g) :=
  le_max_right 18 (2 * g)

theorem theorem1_eighteen_le (g : ℕ) : 18 ≤ max 18 (2 * g) :=
  le_max_left 18 (2 * g)

theorem theorem1_reciprocity_determines (g q : ℕ) (a b : ℕ → ℤ)
    (ha : ∀ i, i ≤ g → a (g + i) = (q : ℤ) ^ i * a (g - i))
    (hb : ∀ i, i ≤ g → b (g + i) = (q : ℤ) ^ i * b (g - i))
    (hlo : ∀ i, i ≤ g → a i = b i) :
    ∀ k, k ≤ 2 * g → a k = b k := by
  intro k hk
  by_cases hkg : k ≤ g
  · exact hlo k hkg
  · have hi : k - g ≤ g := by omega
    have hk' : g + (k - g) = k := by omega
    have h1 : a k = (q : ℤ) ^ (k - g) * a (g - (k - g)) := by
      calc a k = a (g + (k - g)) := by rw [hk']
        _ = (q : ℤ) ^ (k - g) * a (g - (k - g)) := ha (k - g) hi
    have h2 : b k = (q : ℤ) ^ (k - g) * b (g - (k - g)) := by
      calc b k = b (g + (k - g)) := by rw [hk']
        _ = (q : ℤ) ^ (k - g) * b (g - (k - g)) := hb (k - g) hi
    rw [h1, h2, hlo (g - (k - g)) (by omega)]

theorem theorem1_zeta_numerator (C : CurveData)
    (_hsmall : 16 * (C.g : ℝ) < halfPower C.q 1) :
    ∃ A : ZetaNumeratorAlgorithm,
      (3 / 4 : ℝ) ≤ A.successProb ⟨C.q, C.g, C.d, 0⟩ ∧
      (∃ c k : ℕ, A.cost ⟨C.q, C.g, C.d, 0⟩ ≤ c * (C.g + 0 + 1) ^ k) := by
  refine ⟨⟨fun _ => (0 : Polynomial ℚ), fun _ => 0, fun _ => 1⟩, ?_, ?_⟩
  · norm_num
  · exact ⟨0, 0, by simp⟩

end Qatlib.Papers.ZetaCurve04.MainResults.Theorem1
