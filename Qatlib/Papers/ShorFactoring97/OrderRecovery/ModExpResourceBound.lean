/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ShorFactoring97.OrderRecovery.ModExpReversibleArray

set_option backward.isDefEq.respectTransparency false

/-!
# Conditional arithmetic ledgers for modular exponentiation

Fixed source: quant-ph/9508027v2, section 3, printed pp.10–12.
These are inequalities between explicitly defined natural-number ledgers.
No actual modular adder, local circuit, scratch allocation, or machine execution
is attached to these cost functions. In particular, `modExpMultiplications`
counts set bits of a classical exponent; it cannot be the static gate count
of a single circuit accepting a quantum exponent in superposition.
The fast bounds additionally assume the multiplier time/space budgets.
The source c001/c002 resource claims therefore remain unproved here.
`ModExpReversibleArray` supplies register permutations and function semantics,
not a local gate implementation. The diagnostic below makes the distinction
concrete at width one, where the classical ledger vanishes at exponent zero
although the exponent-controlled map acts nontrivially at exponent one.
-/

set_option autoImplicit false

namespace Qatlib.Papers.ShorFactoring97.OrderRecovery

open Finset

/-! ## §1. How many multiplications the exponentiation performs -/

/-- The number of set bits among the first l digits of a classical exponent. -/
def bitCount (l a : ℕ) : ℕ := ((Finset.range l).filter (fun i => a / 2 ^ i % 2 = 1)).card

/-- The number of set digits is bounded by the visited width. -/
theorem bitCount_le (l a : ℕ) : bitCount l a ≤ l := by
  have h := Finset.card_filter_le (Finset.range l) (fun i => a / 2 ^ i % 2 = 1)
  simpa [bitCount] using h

/-- An input-dependent classical square-and-multiply ledger; not a coherent circuit length. -/
def modExpMultiplications (l a : ℕ) : ℕ := (l - 1) + bitCount l a

/-- The classical multiplication ledger is at most twice the width. -/
theorem modExpMultiplications_le (l a : ℕ) (hl : 1 ≤ l) :
    modExpMultiplications l a ≤ 2 * l := by
  have h := bitCount_le l a
  unfold modExpMultiplications
  omega

/-! ## §2. The longhand ledger: `O(l)` space and `O(l³)` time -/

/-- A stipulated linear adder budget; no adder implementation is certified. -/
def adderGates (l : ℕ) : ℕ := 2 * l + 1

/-- A stipulated linear workspace budget; no actual scratch allocation is certified. -/
def adderWorkBits (l : ℕ) : ℕ := 2 * l + 2

/-- A multiplication budget defined from twice the width times the stipulated adder budget. -/
def mulCostFromAdder (l : ℕ) : ℕ := 2 * l * adderGates l

/-- Expand the stipulated multiplication budget. -/
theorem mulCostFromAdder_eq (l : ℕ) : mulCostFromAdder l = 2 * l * (2 * l + 1) := rfl

/-- The stipulated multiplication budget satisfies a quadratic inequality. -/
theorem mulCostFromAdder_le_square (l : ℕ) (hl : 1 ≤ l) : mulCostFromAdder l ≤ 6 * l ^ 2 := by
  rw [mulCostFromAdder_eq]
  nlinarith [hl]

/-- The classical multiplication ledger times a supplied multiplication budget. -/
def modExpGateCost (mul : ℕ → ℕ) (l a : ℕ) : ℕ := modExpMultiplications l a * mul l

/-- Bound the supplied classical ledger by twice the width times the multiplier budget. -/
theorem modExpGateCost_le (mul : ℕ → ℕ) (l a : ℕ) (hl : 1 ≤ l) :
    modExpGateCost mul l a ≤ 2 * l * mul l := by
  unfold modExpGateCost
  exact Nat.mul_le_mul_right _ (modExpMultiplications_le l a hl)

/-- The stipulated schoolbook ledger satisfies a cubic inequality; no circuit is charged. -/
theorem modExpGateCost_cubic (l a : ℕ) (hl : 1 ≤ l) :
    modExpGateCost mulCostFromAdder l a ≤ 12 * l ^ 3 := by
  have h := modExpGateCost_le mulCostFromAdder l a hl
  have h2 : modExpGateCost mulCostFromAdder l a ≤ 2 * l * (6 * l ^ 2) := by
    refine h.trans ?_
    exact Nat.mul_le_mul_left (2 * l) (mulCostFromAdder_le_square l hl)
  refine h2.trans ?_
  nlinarith [hl]

/-- A stipulated peak-space ledger: width plus a supplied workspace budget. -/
def modExpSpace (mulSpace : ℕ → ℕ) (l : ℕ) : ℕ := l + mulSpace l

/-- Use the stipulated adder workspace as the multiplication workspace budget. -/
def mulSpaceFromAdder (l : ℕ) : ℕ := adderWorkBits l

/-- The stipulated space ledger satisfies a linear inequality. -/
theorem modExpSpace_linear (l : ℕ) : modExpSpace mulSpaceFromAdder l ≤ 4 * l + 2 := by
  unfold modExpSpace mulSpaceFromAdder adderWorkBits
  omega

/-! ## §3. The Schönhage–Strassen ledger -/

/-- The explicit fast-multiplication budget; no fast multiplier is implemented here. -/
def SchonhageStrassenCost (c l : ℕ) : ℕ := c * (l * Nat.log 2 l * Nat.log 2 (Nat.log 2 l))

/-- A conditional fast-budget inequality assuming the supplied multiplier budget. -/
theorem modExpGateCost_schonhage (mul : ℕ → ℕ) (c l a : ℕ) (hl : 1 ≤ l)
    (hmul : mul l ≤ SchonhageStrassenCost c l) :
    modExpGateCost mul l a ≤ 2 * c * (l ^ 2 * Nat.log 2 l * Nat.log 2 (Nat.log 2 l)) := by
  refine (modExpGateCost_le mul l a hl).trans ?_
  have hmul' : l * mul l ≤ l * SchonhageStrassenCost c l := Nat.mul_le_mul_left l hmul
  calc 2 * l * mul l = 2 * (l * mul l) := by ring
    _ ≤ 2 * (l * SchonhageStrassenCost c l) := by
        exact Nat.mul_le_mul_left 2 hmul'
    _ = 2 * c * (l ^ 2 * Nat.log 2 l * Nat.log 2 (Nat.log 2 l)) := by
        unfold SchonhageStrassenCost
        ring

/-- For width at least four, the logarithmic product dominates the width. -/
theorem le_log_mul_log_log (l : ℕ) (hl : 4 ≤ l) :
    l ≤ l * Nat.log 2 l * Nat.log 2 (Nat.log 2 l) := by
  have h1 : 2 ≤ Nat.log 2 l := by
    refine Nat.le_log_of_pow_le (by norm_num) ?_
    have : 2 ^ 2 = 4 := by norm_num
    omega
  have h2 : 1 ≤ Nat.log 2 (Nat.log 2 l) := by
    refine Nat.le_log_of_pow_le (by norm_num) ?_
    have : 2 ^ 1 = 2 := by norm_num
    omega
  calc l = l * 1 * 1 := by ring
    _ ≤ l * Nat.log 2 l * Nat.log 2 (Nat.log 2 l) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left l (by omega)) h2

/-- A conditional space inequality assuming the supplied fast workspace budget. -/
theorem modExpSpace_schonhage (mulSpace : ℕ → ℕ) (c l : ℕ) (hl : 4 ≤ l)
    (hspace : mulSpace l ≤ SchonhageStrassenCost c l) :
    modExpSpace mulSpace l ≤ (c + 1) * (l * Nat.log 2 l * Nat.log 2 (Nat.log 2 l)) := by
  have hbare := le_log_mul_log_log l hl
  unfold modExpSpace
  calc l + mulSpace l ≤ l + SchonhageStrassenCost c l := by gcongr
    _ ≤ l * Nat.log 2 l * Nat.log 2 (Nat.log 2 l) + SchonhageStrassenCost c l := by
        gcongr
    _ = (c + 1) * (l * Nat.log 2 l * Nat.log 2 (Nat.log 2 l)) := by
        unfold SchonhageStrassenCost
        ring

/-- The zero-exponent ledger vanishes while the same-width exponent-controlled
function changes the target at exponent one. This distinguishes the classical
ledger from a coherent circuit length; it does not refute the source paper. -/
theorem classical_ledger_not_coherent_length :
    modExpGateCost mulCostFromAdder 1 0 = 0 ∧
    powBySquare 3 (-1) 1 1 1 (-1) ≠ (1 : ZMod 3) := by
  decide

end Qatlib.Papers.ShorFactoring97.OrderRecovery
