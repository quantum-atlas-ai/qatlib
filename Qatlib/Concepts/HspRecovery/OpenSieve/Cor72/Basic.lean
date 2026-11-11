/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.RecordExtract.NonabelianDefs

/-!
# Hidden substring specifications and unique shifts

`HiddenSubstring` describes an injective substring instance with a positive pattern length and
shift `s < M - N`. This module proves the shift bounds, injectivity consequences, and uniqueness
properties used in the hidden substring application of [Kuperberg2005].

`HiddenSubstringEndpoint` specifies a recovery distribution with no incorrect outputs and
success probability at least `2/3`, together with the stated query and bit-operation ledger
bounds. `spliceShift` records translation of the longer string.

## Main statements

* `hiddenSubstring_unique`: uniqueness of the hidden shift.
* `hiddenSubstring_match_iff`: a candidate shift matches exactly when it is the hidden shift.
* `hiddenSubstring_mismatch_iff`: an incorrect candidate has a mismatching pattern position.

## References

* [Kuperberg, 2005][Kuperberg2005]
-/

set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Concepts.HspRecovery.OpenSieve.Cor72

open Qatlib.Concepts.HspRecovery.RecordExtract
open Qatlib.Concepts.HspRecovery.RecordExtract.Nonabelian

/-- An injective substring instance with `0 < N ≤ M`, shift `s < M - N`, agreement `f x = g (x +
s)` for `x < N`, and injectivity of `f` and `g` on their respective bounded domains. -/
def HiddenSubstring {S : Type} (N M : ℕ) (f g : ℕ → S) (s : ℕ) : Prop :=
  0 < N ∧ N ≤ M ∧ s < M - N ∧
    (∀ x : ℕ, x < N → f x = g (x + s)) ∧
    (∀ x : ℕ, x < N → ∀ y : ℕ, y < N → f x = f y → x = y) ∧
    (∀ x : ℕ, x < M → ∀ y : ℕ, y < M → g x = g y → x = y)

/-- Specifies recovery distributions with no incorrect shifts and success probability at least
`2/3`, together with query and bit-operation ledgers bounded by `2 ^ (C * sqrt (log N))` for
`2 ≤ N ≤ M ≤ 2 * N`. -/
def HiddenSubstringEndpoint : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (N M : ℕ), 2 ≤ N → N ≤ M → M ≤ 2 * N →
    ∃ lg : RecoveryLedger,
      (lg.queries : ℝ) ≤ 2 ^ (C * Real.sqrt (Real.log (N : ℝ))) ∧
      (lg.bitOps : ℝ) ≤ 2 ^ (C * Real.sqrt (Real.log (N : ℝ))) ∧
      ∃ run : (S : Type) → (ℕ → S) → (ℕ → S) → PMF (Option ℕ),
        ∀ (S : Type) [Fintype S] [DecidableEq S] (f g : ℕ → S) (s : ℕ),
          HiddenSubstring N M f g s →
          (∀ u : ℕ, u ≠ s → run S f g (some u) = 0) ∧
            ENNReal.ofReal (2 / 3) ≤ run S f g (some s)

/-- The shift in a hidden substring instance is strictly less than `M - N`. -/
theorem hiddenSubstring_shift_lt {S : Type} {N M : ℕ} {f g : ℕ → S} {s : ℕ}
    (h : HiddenSubstring N M f g s) : s < M - N :=
  h.2.2.1

/-- If the longer string has length at most `2 * N`, the hidden substring shift is less than
`N`. -/
theorem hiddenSubstring_shift_lt_two {S : Type} {N M : ℕ} {f g : ℕ → S} {s : ℕ}
    (h : HiddenSubstring N M f g s) (hM : M ≤ 2 * N) : s < N := by
  have h1 := hiddenSubstring_shift_lt h
  have h2 : N ≤ M := h.2.1
  omega

/-- A hidden substring agrees with the longer string translated by the hidden shift at every
pattern position `x < N`. -/
theorem hiddenSubstring_agree {S : Type} {N M : ℕ} {f g : ℕ → S} {s : ℕ}
    (h : HiddenSubstring N M f g s) :
    ∀ x : ℕ, x < N → f x = g (x + s) :=
  h.2.2.2.1

/-- The pattern function of a hidden substring instance is injective on indices less than `N`. -/
theorem hiddenSubstring_f_injective {S : Type} {N M : ℕ} {f g : ℕ → S} {s : ℕ}
    (h : HiddenSubstring N M f g s) :
    ∀ x : ℕ, x < N → ∀ y : ℕ, y < N → f x = f y → x = y :=
  h.2.2.2.2.1

/-- The longer-string function of a hidden substring instance is injective on indices less than
`M`. -/
theorem hiddenSubstring_g_injective {S : Type} {N M : ℕ} {f g : ℕ → S} {s : ℕ}
    (h : HiddenSubstring N M f g s) :
    ∀ x : ℕ, x < M → ∀ y : ℕ, y < M → g x = g y → x = y :=
  h.2.2.2.2.2

/-- Two hidden substring instances with the same lengths and functions have the same shift. -/
theorem hiddenSubstring_unique {S : Type} {N M : ℕ} {f g : ℕ → S} {s₁ s₂ : ℕ}
    (h₁ : HiddenSubstring N M f g s₁) (h₂ : HiddenSubstring N M f g s₂) :
    s₁ = s₂ := by
  have hN : 0 < N := h₁.1
  have hmatch : ∀ x : ℕ, x < N → f x = g (x + s₂) := hiddenSubstring_agree h₂
  have h0 : f 0 = g s₂ := by simpa using hmatch 0 hN
  have ha : f 0 = g s₁ := by simpa using hiddenSubstring_agree h₁ 0 hN
  have hgt : g s₁ = g s₂ := ha.symm.trans h0
  have hs₁M : s₁ < M := by
    have h1 := hiddenSubstring_shift_lt h₁
    have h2 : N ≤ M := h₁.2.1
    omega
  have hs₂M : s₂ < M := by
    have h1 := hiddenSubstring_shift_lt h₂
    have h2 : N ≤ M := h₂.2.1
    omega
  exact hiddenSubstring_g_injective h₁ s₁ hs₁M s₂ hs₂M hgt

/-- For a candidate shift `t < M`, agreement with every pattern position holds exactly when `t`
equals the hidden shift. -/
theorem hiddenSubstring_match_iff {S : Type} {N M : ℕ} {f g : ℕ → S} {s t : ℕ}
    (h : HiddenSubstring N M f g s) (ht : t < M) :
    (∀ x : ℕ, x < N → f x = g (x + t)) ↔ t = s := by
  constructor
  · intro hmatch
    have hN : 0 < N := h.1
    have h0 : f 0 = g t := by simpa using hmatch 0 hN
    have ha : f 0 = g s := by simpa using hiddenSubstring_agree h 0 hN
    have hgt : g t = g s := h0.symm.trans ha
    have hsM : s < M := by
      have h1 := hiddenSubstring_shift_lt h
      have h2 : N ≤ M := h.2.1
      omega
    exact hiddenSubstring_g_injective h t ht s hsM hgt
  · intro hts x hx
    rw [hts]
    exact hiddenSubstring_agree h x hx

/-- Translates a function on natural indices by setting its value at `y` to `g (y + t)`. -/
def spliceShift {S : Type} (g : ℕ → S) (t : ℕ) : ℕ → S :=
  fun y => g (y + t)

/-- For `t ≤ s`, translating the longer string first by `s - t` and then by `t` preserves its
agreement with the hidden substring on indices below `N`. -/
theorem hiddenSubstring_splice_agree {S : Type} {N M : ℕ} {f g : ℕ → S} {s t : ℕ}
    (h : HiddenSubstring N M f g s) (hts : t ≤ s) :
    ∀ x : ℕ, x < N → f x = spliceShift (fun y => g (y + (s - t))) t x := by
  intro x hx
  rw [hiddenSubstring_agree h x hx]
  simp only [spliceShift]
  congr 1
  omega

/-- For a candidate shift `t < M`, some pattern position mismatches exactly when `t` differs
from the hidden shift. -/
theorem hiddenSubstring_mismatch_iff {S : Type} {N M : ℕ} {f g : ℕ → S} {s t : ℕ}
    (h : HiddenSubstring N M f g s) (ht : t < M) :
    (∃ x : ℕ, x < N ∧ f x ≠ g (x + t)) ↔ t ≠ s := by
  constructor
  · rintro ⟨x, hx, hne⟩ rfl
    exact hne (hiddenSubstring_agree h x hx)
  · intro hne
    by_contra hnone
    have hmatch : ∀ x : ℕ, x < N → f x = g (x + t) := by
      intro x hx
      by_contra hne2
      exact hnone ⟨x, hx, hne2⟩
    exact hne ((hiddenSubstring_match_iff h ht).mp hmatch)

end Qatlib.Concepts.HspRecovery.OpenSieve.Cor72
