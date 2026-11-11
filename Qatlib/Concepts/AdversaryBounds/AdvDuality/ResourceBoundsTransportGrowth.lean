/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsTransportDefs

/-!
# Asymptotic transport and search resource growth

This module proves elementary rules for the resource-bound predicates `BigO`, `BigOmega`, and
`BigTheta`, and transfers explicit polylogarithmic gate budgets to asymptotic precision bounds.
Polylogarithmic synthesis costs are discussed by [Dawson and Nielsen, 2006][DawsonNielsen2006].

For the singleton-search construction of [Grover1996], it identifies the query and macro-gate
ledgers and proves matching upper and lower growth estimates along the input-size filter.

## Main statements

* `gate_budget_bigTheta`: Matching explicit precision bounds yield a polylogarithmic growth
  equivalence.
* `search_iterations_lower`: Search iterations are at least one quarter of the square root of
  the search-space size for `n ≥ 4`.
* `search_query_bigTheta_size`: Search queries have square-root growth in the search-space size.
* `search_gates_bigTheta_size`: Search macro gates have the same growth order.

## References

* [Grover, 1996][Grover1996]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib
open Qatlib
open scoped ENNReal

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.ResourceBounds.AsymBounds
open Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsDefs
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
set_option warningAsError false

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality
noncomputable section

/-- Every real-valued function is bounded in `BigO` by itself along any filter. -/
theorem bigO_refl {α : Type*} (F : Filter α) (f : α → ℝ) : BigO F f f := by
  refine ⟨1, by norm_num, ?_⟩
  refine Filter.Eventually.of_forall ?_
  intro x
  simp only [one_mul]
  exact le_refl _
end
noncomputable section

/-- A `BigOWith` bound remains valid when its constant is replaced by its absolute value. -/
theorem bigOWith_abs {α : Type*} (c : ℝ) (F : Filter α) (f g : α → ℝ)
    (h : BigOWith c F f g) : BigOWith |c| F f g := by
  refine h.mono ?_
  intro x hx
  exact le_trans hx (mul_le_mul_of_nonneg_right (le_abs_self c) (abs_nonneg _))
end
noncomputable section

/-- The `BigO` relation is transitive along a fixed filter. -/
theorem bigO_trans {α : Type*} (F : Filter α) (f g h : α → ℝ)
    (hfg : BigO F f g) (hgh : BigO F g h) : BigO F f h := by
  obtain ⟨c1, hc1, h1⟩ := hfg
  obtain ⟨c2, hc2, h2⟩ := hgh
  refine ⟨c1 * c2, mul_nonneg hc1 hc2, ?_⟩
  filter_upwards [h1, h2] with x hx1 hx2
  calc |f x| ≤ c1 * |g x| := hx1
    _ ≤ c1 * (c2 * |h x|) := by gcongr
    _ = c1 * c2 * |h x| := by ring
end
noncomputable section

/-- Multiplying a function by a nonnegative constant preserves its `BigO` bound. -/
theorem bigO_smul {α : Type*} (c : ℝ) (F : Filter α) (f g : α → ℝ)
    (hc : 0 ≤ c) (h : BigO F f g) : BigO F (fun x => c * f x) g := by
  obtain ⟨c1, hc1, h1⟩ := h
  refine ⟨c * c1, mul_nonneg hc hc1, ?_⟩
  filter_upwards [h1] with x hx
  calc |c * f x| = c * |f x| := by rw [abs_mul, abs_of_nonneg hc]
    _ ≤ c * (c1 * |g x|) := by gcongr
    _ = c * c1 * |g x| := by ring
end
noncomputable section

/-- A `BigTheta` relation is equivalent to the two opposite `BigO` bounds. -/
theorem bigTheta_iff {α : Type*} (F : Filter α) (f g : α → ℝ) :
    BigTheta F f g ↔ (BigO F f g ∧ BigO F g f) := Iff.rfl
end
noncomputable section

/-- The `k`th polylogarithm is bounded in `BigO` by the next polylogarithm along the precision
filter. -/
theorem polylog_bigO (k : ℕ) : BigO precFilter (polylog k) (polylog (k + 1)) := by
  refine ⟨1, by norm_num, ?_⟩
  have hev : Filter.Eventually (fun E : ℝ => Real.exp 1 ≤ E) (Filter.atTop : Filter ℝ) :=
    (Filter.eventually_atTop (p := fun E : ℝ => Real.exp 1 ≤ E)).mpr ⟨Real.exp 1, fun b hb => hb⟩
  filter_upwards [hev] with E hE
  have hlog : 1 ≤ Real.log E := by
    have h1 : Real.log (Real.exp 1) ≤ Real.log E := Real.log_le_log (Real.exp_pos 1) hE
    rw [Real.log_exp] at h1
    exact h1
  have habs : 1 ≤ |Real.log E| := le_trans hlog (le_abs_self (Real.log E))
  calc |polylog k E| = |Real.log E| ^ k := by simp [polylog, abs_pow]
    _ = |Real.log E| ^ k * 1 := by rw [mul_one]
    _ ≤ |Real.log E| ^ k * |Real.log E| :=
      mul_le_mul_of_nonneg_left habs (pow_nonneg (abs_nonneg _) k)
    _ = 1 * |polylog (k + 1) E| := by rw [one_mul]; simp [polylog, abs_pow, pow_succ]
end
noncomputable section

/-- A nonnegative gate budget with the stated uniform polylogarithmic upper bound and legal
synthesis witnesses satisfies the corresponding `BigO` bound. -/
theorem gate_budget_bigO (k c : ℕ) (n : ℕ) (wordLen : GateBudget)
    (hcert : ∀ E : ℝ, 1 ≤ E → ∃ s : SynthCertificate n,
      0 ≤ wordLen n E ∧ wordLen n E ≤ c * polylog k E ∧ finiteWordLegal n s.word = true) :
    BigO precFilter (fun E => wordLen n E) (polylog k) := by
  refine ⟨c, by positivity, ?_⟩
  have hev : Filter.Eventually (fun E : ℝ => 1 ≤ E) (Filter.atTop : Filter ℝ) :=
    (Filter.eventually_atTop (p := fun E : ℝ => 1 ≤ E)).mpr ⟨1, by norm_num⟩
  filter_upwards [hev] with E hE
  obtain ⟨s, h0, h1, _⟩ := hcert E hE
  have hlog : 0 ≤ Real.log E := Real.log_nonneg hE
  have hpow : 0 ≤ polylog k E := by unfold polylog; positivity
  calc |wordLen n E| = wordLen n E := abs_of_nonneg h0
    _ ≤ c * polylog k E := h1
    _ = c * |polylog k E| := by rw [abs_of_nonneg hpow]
end
noncomputable section

/-- Multiplying a uniformly polylogarithmically bounded word length by a fixed natural bit cost
preserves its polylogarithmic `BigO` bound. -/
theorem bit_time_bigO (k c bitCost n : ℕ) (wordLen : GateBudget)
    (hbound : ∀ E : ℝ, 1 ≤ E → |wordLen n E| ≤ c * polylog k E) :
    BigO precFilter (fun E => (bitCost : ℝ) * wordLen n E) (polylog k) := by
  refine ⟨(c : ℝ) * bitCost, by positivity, ?_⟩
  have hev : Filter.Eventually (fun E : ℝ => 1 ≤ E) (Filter.atTop : Filter ℝ) :=
    (Filter.eventually_atTop (p := fun E : ℝ => 1 ≤ E)).mpr ⟨1, by norm_num⟩
  filter_upwards [hev] with E hE
  have hlog : 0 ≤ Real.log E := Real.log_nonneg hE
  have hpow : 0 ≤ polylog k E := by unfold polylog; positivity
  calc |(bitCost : ℝ) * wordLen n E| = (bitCost : ℝ) * |wordLen n E| := by
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg bitCost)]
    _ ≤ (bitCost : ℝ) * (c * polylog k E) := by
        gcongr
        exact hbound E hE
    _ = ((c : ℝ) * bitCost) * |polylog k E| := by rw [abs_of_nonneg hpow]; ring
end
noncomputable section

/-- Representation bits, work-tape size, and auxiliary bits can be packaged as the corresponding
fields of `LowerPremises`. -/
theorem lower_premises_explicit (repr work aux : ℕ) :
    ∃ p : LowerPremises, p.reprBits = repr ∧ p.workTape = work ∧ p.auxBits = aux := by
  exact ⟨⟨repr, work, aux⟩, rfl, rfl, rfl⟩
end
noncomputable section

/-- Multiplication by a natural bit cost of at least one preserves the polylogarithmic
`BigTheta` class. -/
theorem bit_time_bigTheta (k bitCost : ℕ) (hbit : 1 ≤ bitCost) :
    BigTheta precFilter (fun E => (bitCost : ℝ) * polylog k E) (polylog k) := by
  refine ⟨?_, ?_⟩
  · refine ⟨bitCost, by positivity, Filter.Eventually.of_forall ?_⟩
    intro E
    have habs : |(bitCost : ℝ) * polylog k E| = bitCost * |polylog k E| := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg bitCost)]
    rw [habs]
  · refine ⟨1, by norm_num, Filter.Eventually.of_forall ?_⟩
    intro E
    have habs : |(bitCost : ℝ) * polylog k E| = bitCost * |polylog k E| := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg bitCost)]
    calc |polylog k E| = |polylog k E| * 1 := by rw [mul_one]
      _ ≤ |polylog k E| * bitCost :=
        mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ (bitCost : ℝ) by exact_mod_cast hbit) (abs_nonneg _)
      _ = 1 * |(bitCost : ℝ) * polylog k E| := by rw [habs]; ring
end
noncomputable section

/-- Every real-valued function is bounded in `BigOmega` by itself along any filter. -/
theorem bigOmega_refl {α : Type*} (F : Filter α) (f : α → ℝ) : BigOmega F f f :=
  bigO_refl F f
end
noncomputable section

/-- The `BigOmega` relation is transitive along a fixed filter. -/
theorem bigOmega_trans {α : Type*} (F : Filter α) (f g h : α → ℝ)
    (hfg : BigOmega F f g) (hgh : BigOmega F g h) : BigOmega F f h :=
  bigO_trans F h g f hgh hfg
end
noncomputable section

/-- A gate budget with the stated uniform polylogarithmic lower bound, coefficient at least one,
and legal synthesis witnesses satisfies the corresponding `BigOmega` bound. -/
theorem gate_budget_bigOmega (k c : ℕ) (n : ℕ) (wordLen : GateBudget) (hc : 1 ≤ c)
    (hcert : ∀ E : ℝ, 1 ≤ E → ∃ s : SynthCertificate n,
      c * polylog k E ≤ wordLen n E ∧ finiteWordLegal n s.word = true) :
    BigOmega precFilter (fun E => wordLen n E) (polylog k) := by
  refine ⟨1, by norm_num, ?_⟩
  have hev : Filter.Eventually (fun E : ℝ => 1 ≤ E) (Filter.atTop : Filter ℝ) :=
    (Filter.eventually_atTop (p := fun E : ℝ => 1 ≤ E)).mpr ⟨1, by norm_num⟩
  filter_upwards [hev] with E hE
  have hlog : 0 ≤ Real.log E := Real.log_nonneg hE
  have hpow : 0 ≤ polylog k E := by unfold polylog; positivity
  obtain ⟨s, h1, _⟩ := hcert E hE
  have hcR : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have hle : polylog k E ≤ wordLen n E := by
    have hmul := mul_le_mul_of_nonneg_right hcR hpow
    calc polylog k E = 1 * polylog k E := by rw [one_mul]
      _ ≤ c * polylog k E := by simpa using! hmul
      _ ≤ wordLen n E := h1
  calc |polylog k E| = polylog k E := abs_of_nonneg hpow
    _ ≤ wordLen n E := hle
    _ = |wordLen n E| := (abs_of_nonneg (le_trans hpow hle)).symm
    _ = 1 * |wordLen n E| := (one_mul _).symm
end
noncomputable section

/-- Matching uniform upper and lower polylogarithmic gate-budget bounds with the stated legal
synthesis witnesses give the corresponding `BigTheta` relation. -/
theorem gate_budget_bigTheta (k c : ℕ) (n : ℕ) (wordLen : GateBudget) (hc : 1 ≤ c)
    (hup : ∀ E : ℝ, 1 ≤ E → ∃ s : SynthCertificate n,
      0 ≤ wordLen n E ∧ wordLen n E ≤ c * polylog k E ∧ finiteWordLegal n s.word = true)
    (hlow : ∀ E : ℝ, 1 ≤ E → ∃ s : SynthCertificate n,
      c * polylog k E ≤ wordLen n E ∧ finiteWordLegal n s.word = true) :
    BigTheta precFilter (fun E => wordLen n E) (polylog k) :=
  ⟨gate_budget_bigO k c n wordLen hup, gate_budget_bigOmega k c n wordLen hc hlow⟩
end
noncomputable section

/-- The sum of the representation-bit, work-tape, and auxiliary-bit fields of lower-bound
premises. -/
def lowerCost (p : LowerPremises) : ℕ :=
  p.reprBits + p.workTape + p.auxBits
end
noncomputable section

/-- Specifying the three fields of lower-bound premises identifies `lowerCost` with their sum. -/
theorem lower_premises_same_cost_unit (repr work aux : ℕ) (p : LowerPremises)
    (h : p.reprBits = repr ∧ p.workTape = work ∧ p.auxBits = aux) :
    lowerCost p = repr + work + aux := by
  simp [lowerCost, h.1, h.2.1, h.2.2]
end
noncomputable section

/-- Multiplication by a fixed natural bit count preserves a first-order polylogarithmic `BigO`
bound. -/
theorem lower_cost_transport (bits : ℕ) (F : Filter ℝ) (f : ℝ → ℝ)
    (h : BigO F f (polylog 1)) :
    BigO F (fun E => (bits : ℝ) * f E) (polylog 1) := by
  obtain ⟨c, hc, h1⟩ := h
  refine ⟨(bits : ℝ) * c, by positivity, ?_⟩
  filter_upwards [h1] with E hx
  calc |(bits : ℝ) * f E| = (bits : ℝ) * |f E| := by
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg bits)]
    _ ≤ (bits : ℝ) * (c * |polylog 1 E|) := by gcongr
    _ = ((bits : ℝ) * c) * |polylog 1 E| := by ring
end
noncomputable section

/-- The forward-query field of the search account equals the singleton-search iteration count. -/
theorem search_account_queries (n : ℕ) :
    (searchAccount n).queries = singletonSearchIterations n := by
  obtain ⟨_, hQ, _, _⟩ :=
    workspace_grover_bit_semantics_and_cost n (singletonSearchIterations n) () (fun _ => false)
  simpa [searchAccount, Account.ofCircuit] using! hQ
end
noncomputable section

/-- The search account uses three macro gates per singleton-search iteration and three
additional macro gates. -/
theorem search_account_gates (n : ℕ) :
    (searchAccount n).macroGates = 3 * singletonSearchIterations n + 3 := by
  obtain ⟨_, _, hG, _⟩ :=
    workspace_grover_bit_semantics_and_cost n (singletonSearchIterations n) () (fun _ => false)
  simpa [searchAccount, Account.ofCircuit] using! hG
end
noncomputable section

/-- For positive `n`, the singleton-search angle is at most pi divided by twice the square root
of the search-space size. -/
theorem search_angle_bound (n : ℕ) (hn : 1 ≤ n) :
    singletonSearchAngle n ≤ Real.pi / (2 * Real.sqrt (searchSpace n)) := by
  have hcard : (Fintype.card (Reg n) : ℝ) = searchSpace n := by
    rw [card_reg]; simp [searchSpace]
  have hNpos : (0 : ℝ) < searchSpace n := by unfold searchSpace; positivity
  have hN1 : (1 : ℝ) < Real.sqrt (searchSpace n) := by
    have h2 : (2 : ℕ) ≤ 2 ^ n :=
      Nat.pow_le_pow_right (n := 2) (by norm_num) (i := 1) (j := n) hn
    have hlt : (1 : ℝ) < searchSpace n := by
      unfold searchSpace
      have hlt' : (1 : ℕ) < 2 ^ n := by omega
      exact_mod_cast hlt'
    simpa [Real.sqrt_one] using!
      (Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) hlt)
  have hang : singletonSearchAngle n
      = Real.arcsin (1 / Real.sqrt (searchSpace n)) := by
    unfold singletonSearchAngle
    rw [hcard]
    have hsqrtdiv : Real.sqrt (1 / searchSpace n)
        = Real.sqrt 1 / Real.sqrt (searchSpace n) :=
      Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1) (searchSpace n)
    rw [hsqrtdiv, Real.sqrt_one]
  rw [hang]
  have hsqrtpos : (0 : ℝ) < Real.sqrt (searchSpace n) := Real.sqrt_pos.2 hNpos
  have h2sqrtpos : (0 : ℝ) < 2 * Real.sqrt (searchSpace n) := by
    unfold searchSpace; positivity
  have hlt : Real.pi / (2 * Real.sqrt (searchSpace n)) < Real.pi / 2 := by
    have hiff : Real.pi / (2 * Real.sqrt (searchSpace n)) < Real.pi / 2
        ↔ Real.pi < (Real.pi / 2) * (2 * Real.sqrt (searchSpace n)) :=
      (div_lt_iff₀ h2sqrtpos)
    apply hiff.mpr
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    nlinarith
  have hy : Real.pi / (2 * Real.sqrt (searchSpace n))
      ∈ Set.Ico (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor
    · have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
      have hpos : (0 : ℝ) < Real.pi / (2 * Real.sqrt (searchSpace n)) := by positivity
      linarith
    · exact hlt
  rw [(Real.arcsin_le_iff_le_sin' hy)]
  have hxpos : (0 : ℝ) < Real.pi / (2 * Real.sqrt (searchSpace n)) := by positivity
  have hsin : (2 / Real.pi) * (Real.pi / (2 * Real.sqrt (searchSpace n)))
      < Real.sin (Real.pi / (2 * Real.sqrt (searchSpace n))) :=
    Real.mul_lt_sin hxpos hlt
  have hsin' : 1 / Real.sqrt (searchSpace n)
      < Real.sin (Real.pi / (2 * Real.sqrt (searchSpace n))) := by
    have hval : (2 / Real.pi) * (Real.pi / (2 * Real.sqrt (searchSpace n)))
        = 1 / Real.sqrt (searchSpace n) := by
      field_simp
    rw [← hval]
    exact hsin
  exact le_of_lt hsin'
end
noncomputable section

/-- For `n ≥ 4`, the square root of the search-space size is at least four. -/
theorem search_space_sqrt_four (n : ℕ) (hn : 4 ≤ n) :
    (4 : ℝ) ≤ Real.sqrt (searchSpace n) := by
  have h16 : (16 : ℕ) ≤ 2 ^ n := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (n := 2) (by norm_num) (i := 4) (j := n) (by omega)
  have hcast : (16 : ℝ) ≤ searchSpace n := by
    unfold searchSpace; exact_mod_cast h16
  have hsq : Real.sqrt (16 : ℝ) ≤ Real.sqrt (searchSpace n) := Real.sqrt_le_sqrt hcast
  have h16sqrt : Real.sqrt (16 : ℝ) = 4 := by
    have h := Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)
    have h16' : (4 : ℝ) ^ 2 = 16 := by norm_num
    rw [h16'] at h
    exact h
  rw [h16sqrt] at hsq
  exact hsq
end
noncomputable section

/-- For `n ≥ 4`, the singleton-search iteration count is at least one quarter of the square root
of the search-space size. -/
theorem search_iterations_lower (n : ℕ) (hn : 4 ≤ n) :
    (singletonSearchIterations n : ℝ) ≥ Real.sqrt (searchSpace n) / 4 := by
  have h2 : 2 ≤ n := by omega
  obtain ⟨hθ0, _, _, _, _, _⟩ := workspace_singleton_angle_and_rounding n h2
  have hθ : singletonSearchAngle n ≤ Real.pi / (2 * Real.sqrt (searchSpace n)) :=
    search_angle_bound n (by omega)
  have h2sqrtpos : (0 : ℝ) < 2 * Real.sqrt (searchSpace n) := by
    unfold searchSpace; positivity
  have hθsqrt : singletonSearchAngle n * Real.sqrt (searchSpace n) ≤ Real.pi / 2 := by
    have h1 := (le_div_iff₀ h2sqrtpos).mp hθ
    have h2r : (2 : ℝ) * (singletonSearchAngle n * Real.sqrt (searchSpace n))
        = singletonSearchAngle n * (2 * Real.sqrt (searchSpace n)) := by ring
    rw [← h2r] at h1
    linarith
  have h4θpos : (0 : ℝ) < 4 * singletonSearchAngle n := by positivity
  have hmul : Real.sqrt (searchSpace n) / 2 * (4 * singletonSearchAngle n) ≤ Real.pi := by
    have h1 := mul_le_mul_of_nonneg_left hθsqrt (by norm_num : (0 : ℝ) ≤ 2)
    calc Real.sqrt (searchSpace n) / 2 * (4 * singletonSearchAngle n)
        = 2 * (Real.sqrt (searchSpace n) * singletonSearchAngle n) := by ring
      _ = 2 * (singletonSearchAngle n * Real.sqrt (searchSpace n)) := by ring
      _ ≤ 2 * (Real.pi / 2) := h1
      _ = Real.pi := by ring
  have hdiv : Real.sqrt (searchSpace n) / 2 ≤ Real.pi / (4 * singletonSearchAngle n) := by
    have hiff : Real.sqrt (searchSpace n) / 2 ≤ Real.pi / (4 * singletonSearchAngle n)
        ↔ Real.sqrt (searchSpace n) / 2 * (4 * singletonSearchAngle n) ≤ Real.pi :=
      (le_div_iff₀ h4θpos)
    exact hiff.mpr hmul
  have hfloor : Real.pi / (4 * singletonSearchAngle n)
      < (singletonSearchIterations n : ℝ) + 1 := by
    have hnonneg : (0 : ℝ) ≤ Real.pi / (4 * singletonSearchAngle n) := by positivity
    have hA : Nat.floor (Real.pi / (4 * singletonSearchAngle n))
        < singletonSearchIterations n + 1 := by
      show Nat.floor (Real.pi / (4 * singletonSearchAngle n))
        < singletonSearchIterations n + 1
      unfold singletonSearchIterations
      exact Nat.lt_succ_self _
    have h := (Nat.floor_lt (R := ℝ) hnonneg (n := singletonSearchIterations n + 1)).1 hA
    have hcast : (↑(singletonSearchIterations n + 1) : ℝ)
        = (singletonSearchIterations n : ℝ) + 1 := by
      rw [Nat.cast_add, Nat.cast_one]
    rw [hcast] at h
    exact h
  have hsqrt4 : (4 : ℝ) ≤ Real.sqrt (searchSpace n) := search_space_sqrt_four n hn
  linarith
end
noncomputable section

/-- For `n ≥ 4`, the search macro-gate count is at most `3 * (Real.pi + 1) / 4` times the square
root of the search-space size. -/
theorem search_gate_bound (n : ℕ) (hn : 4 ≤ n) :
    (3 * singletonSearchIterations n + 3 : ℝ)
      ≤ (3 * (Real.pi + 1) / 4) * Real.sqrt (searchSpace n) := by
  have h2 : 2 ≤ n := by omega
  obtain ⟨_, _, _, _, hkk, _⟩ := workspace_singleton_angle_and_rounding n h2
  have hcard : (Fintype.card (Reg n) : ℝ) = searchSpace n := by
    rw [card_reg]; simp [searchSpace]
  have hsqrt4 : (4 : ℝ) ≤ Real.sqrt (searchSpace n) := search_space_sqrt_four n hn
  have hkk' : (singletonSearchIterations n : ℝ)
      ≤ Real.pi * Real.sqrt (Fintype.card (Reg n) : ℝ) / 4 := hkk
  rw [hcard] at hkk'
  have h3 : (3 : ℝ) ≤ 3 * Real.sqrt (searchSpace n) / 4 := by linarith
  linarith
end
noncomputable section

/-- For `n ≥ 4`, the square root of the search-space size is at most four thirds of the search
macro-gate count. -/
theorem search_gate_lower (n : ℕ) (hn : 4 ≤ n) :
    Real.sqrt (searchSpace n) ≤ (4 / 3) * (3 * singletonSearchIterations n + 3 : ℝ) := by
  have hlo : (singletonSearchIterations n : ℝ) ≥ Real.sqrt (searchSpace n) / 4 :=
    search_iterations_lower n hn
  linarith
end
noncomputable section

/-- The search account's query count has a square-root `BigO` bound along the input-size filter,
as expected for Grover search [Grover1996]. -/
theorem search_query_bigO_size :
    BigO sizeFilter (fun n => (searchAccount n).queries) searchSizeCost := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  refine ⟨Real.pi / 4, by positivity, ?_⟩
  have hev : Filter.Eventually (fun n : ℕ => 2 ≤ n) (sizeFilter : Filter ℕ) := by
    show Filter.Eventually (fun n : ℕ => 2 ≤ n) (Filter.atTop : Filter ℕ)
    exact (Filter.eventually_atTop (p := fun n : ℕ => 2 ≤ n)).mpr ⟨2, fun b hb => hb⟩
  filter_upwards [hev] with n hn
  have hq : (searchAccount n).queries = singletonSearchIterations n := search_account_queries n
  obtain ⟨_, _, _, _, hkk, _⟩ := workspace_singleton_angle_and_rounding n hn
  have hcard : (Fintype.card (Reg n) : ℝ) = searchSpace n := by
    rw [card_reg]; simp [searchSpace]
  calc |((searchAccount n).queries : ℝ)| = (singletonSearchIterations n : ℝ) := by
        rw [hq, abs_of_nonneg (by positivity)]
    _ ≤ Real.pi * Real.sqrt (Fintype.card (Reg n) : ℝ) / 4 := hkk
    _ = (Real.pi / 4) * |searchSizeCost n| := by
        simp only [searchSizeCost]
        rw [← hcard, abs_of_nonneg (Real.sqrt_nonneg _)]
        ring
end
noncomputable section

/-- The search account's query count has a square-root `BigOmega` bound along the input-size
filter. -/
theorem search_query_bigOmega_size :
    BigOmega sizeFilter (fun n => (searchAccount n).queries) searchSizeCost := by
  refine ⟨4, by norm_num, ?_⟩
  have hev : Filter.Eventually (fun n : ℕ => 4 ≤ n) (sizeFilter : Filter ℕ) := by
    show Filter.Eventually (fun n : ℕ => 4 ≤ n) (Filter.atTop : Filter ℕ)
    exact (Filter.eventually_atTop (p := fun n : ℕ => 4 ≤ n)).mpr ⟨4, fun b hb => hb⟩
  filter_upwards [hev] with n hn
  have hq : (searchAccount n).queries = singletonSearchIterations n := search_account_queries n
  have hlo : (singletonSearchIterations n : ℝ) ≥ Real.sqrt (searchSpace n) / 4 :=
    search_iterations_lower n hn
  calc |searchSizeCost n| = Real.sqrt (searchSpace n) := abs_of_nonneg (Real.sqrt_nonneg _)
    _ ≤ 4 * (singletonSearchIterations n : ℝ) := by linarith
    _ = 4 * |((searchAccount n).queries : ℝ)| := by
        rw [hq, abs_of_nonneg (by positivity)]
end
noncomputable section

/-- The search account's query count has square-root `BigTheta` growth along the input-size
filter [Grover1996]. -/
theorem search_query_bigTheta_size :
    BigTheta sizeFilter (fun n => (searchAccount n).queries) searchSizeCost :=
  ⟨search_query_bigO_size, search_query_bigOmega_size⟩
end
noncomputable section

/-- The search account's macro-gate count has square-root `BigTheta` growth along the input-size
filter [Grover1996]. -/
theorem search_gates_bigTheta_size :
    BigTheta sizeFilter (fun n => (searchAccount n).macroGates) searchSizeCost := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  refine ⟨?_, ?_⟩
  · refine ⟨3 * (Real.pi + 1) / 4, by positivity, ?_⟩
    have hev : Filter.Eventually (fun n : ℕ => 4 ≤ n) (sizeFilter : Filter ℕ) := by
      show Filter.Eventually (fun n : ℕ => 4 ≤ n) (Filter.atTop : Filter ℕ)
      exact (Filter.eventually_atTop (p := fun n : ℕ => 4 ≤ n)).mpr ⟨4, fun b hb => hb⟩
    filter_upwards [hev] with n hn
    have hg : (searchAccount n).macroGates = 3 * singletonSearchIterations n + 3 :=
      search_account_gates n
    have hb : (3 * singletonSearchIterations n + 3 : ℝ)
        ≤ (3 * (Real.pi + 1) / 4) * Real.sqrt (searchSpace n) := search_gate_bound n hn
    calc |((searchAccount n).macroGates : ℝ)| = (3 * singletonSearchIterations n + 3 : ℝ) := by
          rw [hg, abs_of_nonneg (by positivity)]
          norm_num [Nat.cast_add, Nat.cast_mul]
      _ ≤ (3 * (Real.pi + 1) / 4) * Real.sqrt (searchSpace n) := hb
      _ = (3 * (Real.pi + 1) / 4) * |searchSizeCost n| := by
          simp only [searchSizeCost]
          rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  · refine ⟨4 / 3, by positivity, ?_⟩
    have hev : Filter.Eventually (fun n : ℕ => 4 ≤ n) (sizeFilter : Filter ℕ) := by
      show Filter.Eventually (fun n : ℕ => 4 ≤ n) (Filter.atTop : Filter ℕ)
      exact (Filter.eventually_atTop (p := fun n : ℕ => 4 ≤ n)).mpr ⟨4, fun b hb => hb⟩
    filter_upwards [hev] with n hn
    have hg : (searchAccount n).macroGates = 3 * singletonSearchIterations n + 3 :=
      search_account_gates n
    have hb : Real.sqrt (searchSpace n) ≤ (4 / 3) * (3 * singletonSearchIterations n + 3 : ℝ) :=
      search_gate_lower n hn
    calc |searchSizeCost n| = Real.sqrt (searchSpace n) := abs_of_nonneg (Real.sqrt_nonneg _)
      _ ≤ (4 / 3) * (3 * singletonSearchIterations n + 3 : ℝ) := hb
      _ = (4 / 3) * |((searchAccount n).macroGates : ℝ)| := by
          rw [hg, abs_of_nonneg (by positivity)]
          norm_num [Nat.cast_add, Nat.cast_mul]
end
end Qatlib.Concepts.AdversaryBounds.AdvDuality
