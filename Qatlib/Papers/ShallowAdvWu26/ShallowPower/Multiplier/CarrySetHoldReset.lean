/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Order

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 9: the set-hold-reset carry bit

Fixed version: arXiv:2608.15545v1 (2026-08-16), Lemma 9, p.20, Eqs. (I20)-(I24)
in Appendix I.3.

The block-carry recurrence is `D_b = α_{b-1} + E_b`, where `E_b` is the extra
carry produced by block `b-1`, and `D_{b+1} = ⌊(A_b + D_b)/W⌋`.  With
`X_b = ρ_b + α_{b-1}`, `S_b = 1[X_b ≥ W]`, `H_b = 1[X_b = W - 1]`, the carry
satisfies

```
E_{b+1} = 1,          if S_b = 1,
        = E_b,        if H_b = 1,
        = 0,          otherwise;            (I23)
E_{b+1} = ⋁_{ℓ ≤ b} (S_ℓ ∧ ⋀_{t = ℓ+1}^{b} H_t).   (I24)
```

Both identities are pure `ℕ` arithmetic and are proved below without `sorry`:

* `carry_set_hold_reset` is Eq. (I23) with `W`, `X = ρ_b + α_{b-1}` and
  `E = E_b` (the only hypothesis is `E ≤ 1`, the carry being a bit);
* `prefix_formula` is Eq. (I24), by induction on the block index.
-/

set_option autoImplicit false

namespace Qatlib.Papers.ShallowAdvWu26.ShallowPower.Multiplier

/-- Indicator of a decidable proposition as a natural number. -/
def ind (P : Prop) [Decidable P] : ℕ := if P then 1 else 0

/-- The indicator of a true proposition is `1`. -/
theorem ind_true (P : Prop) [Decidable P] (h : P) : ind P = 1 := by
  simp [ind, h]

/-- The indicator of a false proposition is `0`. -/
theorem ind_false (P : Prop) [Decidable P] (h : ¬P) : ind P = 0 := by
  simp [ind, h]

/-- The indicator equals one exactly on true propositions. -/
theorem ind_eq_one_iff (P : Prop) [Decidable P] : ind P = 1 ↔ P := by
  by_cases h : P <;> simp [ind, h]

/-- Carry into the next block, `1[W ≤ X + E]` (from Eq. (I25)). -/
def nextCarry (W X E : ℕ) : ℕ := ind (W ≤ X + E)

/-- Set bit `S = 1[X ≥ W]`. -/
def setBit (W X : ℕ) : ℕ := ind (W ≤ X)

/-- Hold bit `H = 1[X = W - 1]`. -/
def holdBit (W X : ℕ) : ℕ := ind (X = W - 1)

/-- The right-hand side of the set-hold-reset rule (Eq. (I23)). -/
def resetValue (W X E : ℕ) : ℕ :=
  if setBit W X = 1 then 1 else if holdBit W X = 1 then E else 0

/-- **Lemma 9, Eq. (I23).**  For a carry bit `E ≤ 1` and any `W`, `X`,
`1[W ≤ X + E]` is `1` when `X ≥ W`, is `E` when `X = W - 1`, and is `0`
otherwise. -/
theorem carry_set_hold_reset (W X E : ℕ) (hE : E ≤ 1) :
    nextCarry W X E = resetValue W X E := by
  unfold nextCarry resetValue setBit holdBit
  have hE01 : E = 0 ∨ E = 1 := by omega
  rcases hE01 with rfl | rfl
  · by_cases hWX : W ≤ X
    · have hsum : W ≤ X + 0 := by omega
      simp [ind, hWX, hsum]
    · by_cases hX : X = W - 1
      · have hsum : ¬ W ≤ X + 0 := by omega
        simp [ind, hWX, hX, hsum]
      · have hsum : ¬ W ≤ X + 0 := by omega
        simp [ind, hWX, hX, hsum]
  · by_cases hWX : W ≤ X
    · have hsum : W ≤ X + 1 := by omega
      simp [ind, hWX, hsum]
    · by_cases hX : X = W - 1
      · have hWne : W ≠ 0 := by omega
        have hsub : W - 1 + 1 = W := Nat.sub_one_add_one hWne
        simp [ind, hWX, hX, hsub]
      · have hsum : ¬ W ≤ X + 1 := by omega
        simp [ind, hWX, hX, hsum]

/-- **Lemma 9, Eq. (I23) in block form.**  Substituting `D_b = α_{b-1} + E_b`
into `E_{b+1} = 1[ρ_b + D_b ≥ W]` gives the set-hold-reset rule with
`X_b = ρ_b + α_{b-1}`. -/
theorem carry_step (W : ℕ) (α ρ E : ℕ → ℕ) (hE : ∀ b, E b ≤ 1) (b : ℕ) :
    ind (W ≤ ρ b + α b + E b) =
      (if W ≤ ρ b + α b then 1
        else if ρ b + α b = W - 1 then E b else 0) := by
  have h := carry_set_hold_reset W (ρ b + α b) (E b) (hE b)
  unfold nextCarry resetValue setBit holdBit at h
  simp only [ind_eq_one_iff] at h
  exact h

/-- Parallel-prefix carry register driven by set bit `S b` and hold bit `H b`:
`E_0 = 0` and `E_{b+1} = if S_b then 1 else if H_b then E_b else 0`. -/
def prefixCarry (S H : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | b + 1 => if S b then 1 else if H b then prefixCarry S H b else 0

/-- The Boolean parallel-prefix witness of Eq. (I24):
`⋁_{ℓ ≤ b} (S_ℓ ∧ ⋀_{t = ℓ+1}^{b} H_t)`, computed right to left. -/
def prefixWitnessB (S H : ℕ → Bool) : ℕ → Bool
  | 0 => S 0
  | b + 1 => S (b + 1) || (H (b + 1) && prefixWitnessB S H b)

/-- **Lemma 9, Eq. (I24).**  The iterated set-hold-reset recurrence equals the
parallel-prefix formula `⋁_{ℓ ≤ b} (S_ℓ ∧ ⋀_{t=ℓ+1}^{b} H_t)`. -/
theorem prefix_formula (S H : ℕ → Bool) :
    ∀ b, prefixCarry S H (b + 1) = if prefixWitnessB S H b then 1 else 0 := by
  intro b
  induction b with
  | zero =>
    cases hS : S 0 <;> cases hH : H 0 <;>
      simp [prefixCarry, prefixWitnessB, hS, hH]
  | succ b ih =>
    change (if S (b + 1) then 1
        else if H (b + 1) then prefixCarry S H (b + 1) else 0) =
      if prefixWitnessB S H (b + 1) then 1 else 0
    cases hS : S (b + 1) <;> cases hH : H (b + 1) <;>
      simp [prefixWitnessB, hS, hH, ih]

end Qatlib.Papers.ShallowAdvWu26.ShallowPower.Multiplier
