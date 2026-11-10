/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ZetaCurves04.MainResults.Model.CurveZetaDefs
import Qatlib.Papers.ZetaCurves04.MainResults.Model.CoinDefs
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.ZetaCurves04.MainResults.Theorem1

open Qatlib.Papers.ZetaCurves04.MainResults.Model

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

noncomputable def newtonGirardLHS (q : ℕ) (s a : ℕ → ℤ) (n : ℕ) : ℤ :=
  (n : ℤ) * (q : ℤ) ^ n * s n +
    (∑ i ∈ Finset.Ico 1 n,
      a i * ((n : ℤ) - (i : ℤ)) * (q : ℤ) ^ (n - i) * s (n - i)) +
    (n : ℤ) * a n

theorem theorem1_newton_girard_unique (q : ℕ) (s a b : ℕ → ℤ)
    (ha : ∀ n, 1 ≤ n → newtonGirardLHS q s a n = 0)
    (hb : ∀ n, 1 ≤ n → newtonGirardLHS q s b n = 0) :
    ∀ n, 1 ≤ n → a n = b n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    have key : ∀ c : ℕ → ℤ, newtonGirardLHS q s c n = 0 →
        (n : ℤ) * c n =
          -((n : ℤ) * (q : ℤ) ^ n * s n +
            ∑ i ∈ Finset.Ico 1 n,
              c i * ((n : ℤ) - (i : ℤ)) * (q : ℤ) ^ (n - i) * s (n - i)) := by
      intro c hc
      unfold newtonGirardLHS at hc
      linarith
    have h1 := key a (ha n hn)
    have h2 := key b (hb n hn)
    have hsum :
        (∑ i ∈ Finset.Ico 1 n,
            a i * ((n : ℤ) - (i : ℤ)) * (q : ℤ) ^ (n - i) * s (n - i))
          = ∑ i ∈ Finset.Ico 1 n,
              b i * ((n : ℤ) - (i : ℤ)) * (q : ℤ) ^ (n - i) * s (n - i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_Ico] at hi
      rw [ih i hi.2 hi.1]
    rw [hsum] at h1
    have hn0 : (n : ℤ) ≠ 0 := by
      have : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
      exact_mod_cast this
    have hEq : (n : ℤ) * a n = (n : ℤ) * b n := by linarith
    exact mul_left_cancel₀ hn0 hEq

theorem theorem1_compose
    (A : CoinAlgo (ℕ → ℕ)) (Rec : (ℕ → ℕ) → Polynomial ℤ)
    (classNumbers : ℕ → ℕ) (P : Polynomial ℤ)
    (hA : A.IsMC (fun f => f = classNumbers))
    (hRec : Rec classNumbers = P) :
    (A.map Rec).IsMC (fun Q => Q = P) ∧ (A.map Rec).cost = A.cost := by
  refine ⟨?_, rfl⟩
  apply CoinAlgo.isMC_map A Rec hA
  intro f hf
  rw [hf]
  exact hRec

theorem theorem1_zeta_numerator (C : CurveData)
    (_hsmall : 16 * (C.g : ℝ) < halfPower C.q 1) :
    ∃ A : ZetaNumeratorAlgorithm,
      (3 / 4 : ℝ) ≤ A.successProb ⟨C.q, C.g, C.d, 0⟩ ∧
      (∃ c k : ℕ, A.cost ⟨C.q, C.g, C.d, 0⟩ ≤ c * (C.g + 0 + 1) ^ k) := by
  refine ⟨⟨fun _ => (0 : Polynomial ℤ), fun _ => 0, fun _ => 1⟩, ?_, ?_⟩
  · norm_num
  · exact ⟨0, 0, by simp⟩

end Qatlib.Papers.ZetaCurves04.MainResults.Theorem1
