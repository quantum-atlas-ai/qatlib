/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset

namespace Qatlib.Papers.GridWalk16.MainResults

/-- The uniform probability of a decidable event `E` on a finite type `α`:
`|E| / |α|`. -/
def uniformProb {α : Type*} [Fintype α] (E : α → Prop) [DecidablePred E] : ℝ :=
  ((Finset.univ.filter E).card : ℝ) / (Fintype.card α : ℝ)

/-- A `T`-step line walk: the outcome of each of the `T` fair coin flips. -/
abbrev LineWalk (T : ℕ) := Fin T → Bool

/-- A `T`-step grid walk: two independent line walks (row and column coordinates). -/
abbrev GridWalk (T : ℕ) := LineWalk T × LineWalk T

/-- A single `±1` step: `false ↦ −1`, `true ↦ +1`. -/
def lineStep (b : Bool) : ℤ := if b then 1 else -1

/-- The position after `t` steps of a `T`-step line walk, as a genuine finite sum of the
first `t` increments. -/
def linePos {T : ℕ} (ω : LineWalk T) (t : ℕ) : ℤ :=
  ∑ i : Fin T, if (i : ℕ) < t then lineStep (ω i) else 0

/-- A line walk is localized at radius `k` when every prefix position has `|pos| ≤ k`. -/
abbrev lineLocalized (T : ℕ) (k : ℤ) (ω : LineWalk T) : Prop :=
  ∀ t ∈ Finset.range (T + 1), |linePos ω t| ≤ k

/-- A grid walk is localized at radius `k` when both coordinate walks are. -/
abbrev gridLocalized (T : ℕ) (k : ℤ) (ω : GridWalk T) : Prop :=
  lineLocalized T k ω.1 ∧ lineLocalized T k ω.2

/-- Decidability of the line-localization predicate, needed for `uniformProb`. -/
instance instDecidablePredLineLocalized (T : ℕ) (k : ℤ) :
    DecidablePred (fun ω : LineWalk T => lineLocalized T k ω) :=
  fun ω => by unfold lineLocalized; infer_instance

/-- Decidability of the grid-localization predicate, needed for `uniformProb`. -/
instance instDecidablePredGridLocalized (T : ℕ) (k : ℤ) :
    DecidablePred (fun ω : GridWalk T => gridLocalized T k ω) :=
  fun ω => by unfold gridLocalized lineLocalized; infer_instance

/-- Numeric end-point of the proof of Lemma 9 (paper p. 9: "`4e^{−8}` is less than
`1/745`"): `4·exp(−8) < 1/745`, equivalent to `2980 < e⁸`. -/
lemma exp_eight_gt_two_nine_eight_zero : (2980 : ℝ) < Real.exp 8 := by
  have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h2 : (2.7182818283 : ℝ) ^ 8 < (Real.exp 1) ^ 8 :=
    pow_lt_pow_left₀ h1 (by norm_num) (by norm_num)
  have h3 : (2980 : ℝ) < (2.7182818283 : ℝ) ^ 8 := by norm_num
  have h4 : (Real.exp 1) ^ 8 = Real.exp 8 := by
    have := Real.exp_nat_mul (1 : ℝ) 8
    simpa using this
  linarith

/-- `4·exp(−8) < 1/745` (paper p. 9, last line of the proof of Lemma 9). -/
lemma four_exp_neg_eight_lt_inv_745 : 4 * Real.exp (-8) < 1 / 745 := by
  have hp : (0 : ℝ) < Real.exp 8 := Real.exp_pos 8
  have h8 : (2980 : ℝ) < Real.exp 8 := exp_eight_gt_two_nine_eight_zero
  rw [Real.exp_neg]
  calc
    4 * (Real.exp 8)⁻¹ < 4 * (2980 : ℝ)⁻¹ :=
      mul_lt_mul_of_pos_left ((inv_lt_inv₀ hp (by norm_num : (0:ℝ) < 2980)).2 h8) (by norm_num)
    _ = 1 / 745 := by norm_num

/-- Exact product formula for the uniform measure on a product of nonempty finite types:
`Pr[A × B] = Pr[A]·Pr[B]`.  This is the "Cartesian graph product" independence step
(paper p. 10) computing `pG` from the two line probabilities. -/
lemma uniformProb_prod {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (A : α → Prop) (B : β → Prop) [DecidablePred A] [DecidablePred B] :
    uniformProb (fun p : α × β => A p.1 ∧ B p.2) = uniformProb A * uniformProb B := by
  unfold uniformProb
  have hfilter : (Finset.univ.filter (fun p : α × β => A p.1 ∧ B p.2))
      = (Finset.univ.filter A) ×ˢ (Finset.univ.filter B) := by
    ext p
    obtain ⟨a, b⟩ := p
    simp [Finset.mem_product]
  rw [hfilter, Finset.card_product, Fintype.card_prod]
  push_cast
  have hα : (Fintype.card α : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card α ≠ 0)
  have hβ : (Fintype.card β : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card β ≠ 0)
  field_simp
  try ring

end Qatlib.Papers.GridWalk16.MainResults
