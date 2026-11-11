/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Shifted Legendre states and their correlations

The shifted quadratic character defines `legendreMatrix` and a family of states `slsState` with
one additional coordinate. The character correlation identity gives their normalization and
orthogonality, which are packaged with a two-call count in `SLSProcedure`.

This development forms part of the formalization of [VanDam2002].

## Main statements

* `fact5_nearOrthogonality`: In characteristic different from two, the correlation of two
  shifted quadratic characters is `card F - 1` for equal shifts and minus one otherwise.
* `source_theorem2_twoQuerySLS`: There exists an `SLSProcedure` with call count two whose states
  are `slsState` and whose state pairings equal the Kronecker delta.

## References

* [van Dam, 2002][VanDam2002]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.WeighMatrix00.MainResults

open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The integer-valued quadratic character of the finite field. -/
def legendreSymbol (x : F) : ℤ := quadraticChar F x

/-- The quadratic character evaluated at `i + s`, with shift `s`. -/
def shiftedLegendre (s i : F) : ℤ := quadraticChar F (i + s)

/-- The matrix whose entry at `(i, j)` is the quadratic character of `i + j`. -/
def legendreMatrix : Matrix F F ℤ := fun i j => quadraticChar F (i + j)

/-- The quadratic character vanishes at zero. -/
theorem legendreSymbol_zero : legendreSymbol (F := F) 0 = 0 := by
  simpa [legendreSymbol] using quadraticChar_zero (F := F)

/-- The quadratic character vanishes exactly at zero. -/
theorem legendreSymbol_eq_zero_iff (x : F) : legendreSymbol x = 0 ↔ x = 0 :=
  quadraticChar_eq_zero_iff

/-- The quadratic character is multiplicative. -/
theorem legendreSymbol_mul (x y : F) : legendreSymbol (x * y) = legendreSymbol x * legendreSymbol y := by
  simpa [legendreSymbol] using map_mul (quadraticChar F) x y

/-- The square of the quadratic character of a nonzero element is one. -/
theorem legendreSymbol_sq_one {x : F} (hx : x ≠ 0) : legendreSymbol x ^ 2 = 1 := by
  simpa [legendreSymbol] using quadraticChar_sq_one hx

/-- The quadratic character takes the value one at one. -/
theorem legendreSymbol_one : legendreSymbol (F := F) 1 = 1 := by
  simpa [legendreSymbol] using map_one (quadraticChar F)

/-- The sum of squares of a shifted quadratic character is `card F - 1`. -/
theorem fact5_diagonal (s : F) :
    ∑ i : F, quadraticChar F (i + s) * quadraticChar F (i + s) =
      (Fintype.card F : ℤ) - 1 := by
  have hterm : ∀ i : F, quadraticChar F (i + s) * quadraticChar F (i + s) =
      if i + s = 0 then (0 : ℤ) else 1 := by
    intro i
    by_cases hi : i + s = 0
    · simp [hi]
    · rw [if_neg hi, ← pow_two]
      exact quadraticChar_sq_one hi
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  have hshift : (∑ i : F, (if i + s = 0 then (0 : ℤ) else 1)) =
      ∑ i : F, (if i = -s then (0 : ℤ) else 1) := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : i = -s
    · have hz : i + s = 0 := by rw [h]; abel
      simp [h, hz]
    · have hz : i + s ≠ 0 := by
        intro hc
        exact h (add_eq_zero_iff_eq_neg.mp hc)
      simp [h, hz]
  rw [hshift]
  have hsingle : (∑ i : F, (if i = -s then (1 : ℤ) else 0)) = 1 := by
    rw [Finset.sum_ite_eq']
    simp
  calc (∑ i : F, (if i = -s then (0 : ℤ) else 1))
      = ∑ i : F, ((1 : ℤ) - if i = -s then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases h : i = -s <;> simp [h]
    _ = (∑ i : F, (1 : ℤ)) - ∑ i : F, (if i = -s then (1 : ℤ) else 0) := by
        rw [Finset.sum_sub_distrib]
    _ = (Fintype.card F : ℤ) - 1 := by
        rw [hsingle, Finset.sum_const, Finset.card_univ]
        simp

/-- In characteristic different from two, the correlation of two shifted quadratic characters is
`card F - 1` for equal shifts and minus one otherwise. See [VanDam2002]. -/
theorem fact5_nearOrthogonality (hF : ringChar F ≠ 2) (s r : F) :
    ∑ i : F, quadraticChar F (i + r) * quadraticChar F (i + s) =
      if s = r then (Fintype.card F : ℤ) - 1 else -1 := by
  by_cases hsr : s = r
  · subst hsr
    rw [if_pos rfl]
    exact fact5_diagonal s
  · rw [if_neg hsr]
    set d : F := r - s with hddef
    have hd : d ≠ 0 := by
      simp only [hddef, sub_ne_zero]
      exact Ne.symm hsr
    have hshift : (∑ i : F, quadraticChar F (i + r) * quadraticChar F (i + s)) =
        ∑ j : F, quadraticChar F (j + d) * quadraticChar F j := by
      have h := Equiv.sum_comp (Equiv.addRight s)
        (fun j : F => quadraticChar F (j + d) * quadraticChar F j)
      calc (∑ i : F, quadraticChar F (i + r) * quadraticChar F (i + s))
          = ∑ i : F, quadraticChar F ((i + s) + d) * quadraticChar F (i + s) := by
            apply Finset.sum_congr rfl
            intro i _
            have h' : i + r = (i + s) + d := by rw [hddef]; ring
            rw [h']
        _ = ∑ j : F, quadraticChar F (j + d) * quadraticChar F j := h
    rw [hshift]
    have hfilter : (∑ j : F, quadraticChar F (j + d) * quadraticChar F j) =
        (Finset.univ.filter (fun j : F => j ≠ 0 ∧ j ≠ -d)).sum
          (fun j => quadraticChar F (j + d) * quadraticChar F j) := by
      symm
      apply Finset.sum_filter_of_ne
      intro j _ hj
      constructor
      · intro hj0
        exact hj (by simp [hj0])
      · intro hjd
        have hz : j + d = 0 := by rw [hjd]; abel
        exact hj (by simp [hz])
    rw [hfilter]
    have hterm : ∀ j ∈ Finset.univ.filter (fun j : F => j ≠ 0 ∧ j ≠ -d),
        quadraticChar F (j + d) * quadraticChar F j = quadraticChar F (1 + d / j) := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      obtain ⟨hj0, _⟩ := hj
      have hmul : quadraticChar F (1 + d / j) * quadraticChar F j =
          quadraticChar F (j + d) := by
        rw [← map_mul]
        rw [show (1 + d / j) * j = j + d by field_simp [hj0]]
      rw [← hmul, mul_assoc, ← pow_two, quadraticChar_sq_one hj0, mul_one]
    rw [Finset.sum_congr rfl hterm]
    have hbij :
        (Finset.univ.filter (fun j : F => j ≠ 0 ∧ j ≠ -d)).sum
          (fun j => quadraticChar F (1 + d / j)) =
        (Finset.univ.filter (fun u : F => u ≠ 0 ∧ u ≠ 1)).sum
          (fun u => quadraticChar F u) := by
      refine Finset.sum_bij (i := fun j _ => 1 + d / j) ?_ ?_ ?_ ?_
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
        obtain ⟨hj0, hjd⟩ := hj
        constructor
        · intro hzero
          have h1 : d / j = -1 := by
            have := congrArg (fun x : F => x - 1) hzero
            simpa using this
          have hdj : d = -j := by
            have h2 := h1
            field_simp [hj0] at h2
            rw [h2]
          exact hjd (by rw [hdj]; ring)
        · intro hone
          have h1 : d / j = 0 := by
            have := congrArg (fun x : F => x - 1) hone
            simpa using this
          exact hd ((div_eq_zero_iff.mp h1).resolve_right hj0)
      · intro a ha b hb hab
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
        have h1 : d / a = d / b := add_left_cancel hab
        have h2 : d * b = d * a := (div_eq_div_iff ha.1 hb.1).mp h1
        exact (mul_left_cancel₀ hd h2).symm
      · intro b hb
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
        obtain ⟨hb0, hb1⟩ := hb
        have hb1' : b - 1 ≠ 0 := sub_ne_zero.mpr hb1
        refine ⟨d / (b - 1), ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · exact div_ne_zero hd hb1'
          · intro hcon
            have h1 : d = -d * (b - 1) := by
              have h := congrArg (fun x : F => x * (b - 1)) hcon
              try simp only at h
              rw [div_mul_cancel₀ d hb1'] at h
              exact h
            have h2 : d * 1 = d * (-(b - 1)) := by
              rw [mul_one]
              calc d = -d * (b - 1) := h1
                _ = d * (-(b - 1)) := by ring
            have h3 : (1 : F) = -(b - 1) := mul_left_cancel₀ hd h2
            have h4 : b - 1 = -1 := by
              have h := congrArg (fun x : F => -x) h3
              simpa using h.symm
            have h5 : b = 0 := by
              have h := congrArg (fun x : F => x + 1) h4
              simpa using h
            exact hb0 h5
        · field_simp [hd, hb1']
          ring
      · intro a ha
        rfl
    rw [hbij]
    have hfinal : ((Finset.univ.filter (fun u : F => u ≠ 0 ∧ u ≠ 1)).sum
        (fun u => quadraticChar F u)) = -1 := by
      have hset : Finset.univ.filter (fun u : F => u ≠ 0 ∧ u ≠ 1) =
          Finset.univ \ ({0, 1} : Finset F) := by
        ext u
        simp [and_comm]
      rw [hset]
      have hsub : ({0, 1} : Finset F) ⊆ Finset.univ := by simp
      have hsd := Finset.sum_sdiff hsub (f := fun u : F => quadraticChar F u)
      have hpair : (∑ x ∈ ({0, 1} : Finset F), quadraticChar F x) = 1 := by
        rw [Finset.sum_insert (by simp), Finset.sum_singleton]
        simp [quadraticChar_zero]
      rw [quadraticChar_sum_zero hF, hpair] at hsd
      linarith
    rw [hfinal]

/-- The column Gram sum of the Legendre matrix is `card F - 1` on the diagonal and minus one off
the diagonal. -/
theorem legendreMatrix_gram (hF : ringChar F ≠ 2) (a b : F) :
    ∑ i : F, legendreMatrix (F := F) i a * legendreMatrix (F := F) i b =
      if a = b then (Fintype.card F : ℤ) - 1 else -1 := by
  simpa [legendreMatrix, eq_comm] using fact5_nearOrthogonality hF b a

/-- The shifted quadratic-character vector augmented by a constant coordinate and scaled by the
square root of the field cardinality. -/
def slsState (s : F) : F ⊕ Unit → ℂ :=
  fun x =>
    match x with
    | Sum.inl i => (quadraticChar F (i + s) : ℂ) / (Real.sqrt (Fintype.card F : ℝ) : ℂ)
    | Sum.inr _ => 1 / (Real.sqrt (Fintype.card F : ℝ) : ℂ)

/-- The sum of the squared amplitudes of `slsState s` is one under the stated field hypotheses. -/
theorem slsState_norm (hF : ringChar F ≠ 2) (hq : 1 < Fintype.card F) (s : F) :
    ∑ x : F ⊕ Unit, slsState s x * slsState s x = 1 := by
  have hq0 : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hq)
  have hqc : ((Real.sqrt (Fintype.card F : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr hq0))
  have hsq : ((Real.sqrt (Fintype.card F : ℝ) : ℂ)) ^ 2 = (Fintype.card F : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hq0.le]
    simp
  have hdiag := fact5_diagonal (F := F) s
  have hdiagC : (∑ i : F, ((quadraticChar F (i + s) : ℂ) * (quadraticChar F (i + s) : ℂ))) =
      (Fintype.card F : ℂ) - 1 := by
    have hcast := congrArg (fun z : ℤ => (z : ℂ)) hdiag
    push_cast at hcast
    simpa using hcast
  rw [Fintype.sum_sum_type]
  simp only [slsState]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_unit, one_smul]
  have hleft : ∀ i : F,
      (quadraticChar F (i + s) : ℂ) / (Real.sqrt (Fintype.card F : ℝ) : ℂ) *
        ((quadraticChar F (i + s) : ℂ) / (Real.sqrt (Fintype.card F : ℝ) : ℂ)) =
      ((quadraticChar F (i + s) : ℂ) * (quadraticChar F (i + s) : ℂ)) /
        ((Real.sqrt (Fintype.card F : ℝ) : ℂ)) ^ 2 := by
    intro i
    field_simp
  simp_rw [hleft]
  have hright : (1 : ℂ) / (Real.sqrt (Fintype.card F : ℝ) : ℂ) *
      (1 / (Real.sqrt (Fintype.card F : ℝ) : ℂ)) =
      1 / ((Real.sqrt (Fintype.card F : ℝ) : ℂ)) ^ 2 := by
    field_simp
  rw [hright, ← Finset.sum_div, ← add_div, hdiagC]
  rw [show ((Fintype.card F : ℂ) - 1 + 1) = (Fintype.card F : ℂ) by ring, hsq]
  exact div_self (by exact_mod_cast (ne_of_gt hq0))

/-- Distinct shifted Legendre states have zero bilinear amplitude pairing under the stated field
hypotheses. -/
theorem slsState_orthogonal (hF : ringChar F ≠ 2) (hq : 1 < Fintype.card F)
    {s r : F} (hsr : s ≠ r) :
    ∑ x : F ⊕ Unit, slsState s x * slsState r x = 0 := by
  have hq0 : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hq)
  have hsq : ((Real.sqrt (Fintype.card F : ℝ) : ℂ)) ^ 2 = (Fintype.card F : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hq0.le]
    simp
  have hoff := fact5_nearOrthogonality (F := F) hF s r
  rw [if_neg hsr] at hoff
  have hoffC : (∑ i : F, ((quadraticChar F (i + r) : ℂ) * (quadraticChar F (i + s) : ℂ))) = -1 := by
    have hcast := congrArg (fun z : ℤ => (z : ℂ)) hoff
    push_cast at hcast
    simpa using hcast
  rw [Fintype.sum_sum_type]
  simp only [slsState]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_unit, one_smul]
  have hleft : ∀ i : F,
      (quadraticChar F (i + s) : ℂ) / (Real.sqrt (Fintype.card F : ℝ) : ℂ) *
        ((quadraticChar F (i + r) : ℂ) / (Real.sqrt (Fintype.card F : ℝ) : ℂ)) =
      ((quadraticChar F (i + r) : ℂ) * (quadraticChar F (i + s) : ℂ)) /
        ((Real.sqrt (Fintype.card F : ℝ) : ℂ)) ^ 2 := by
    intro i
    field_simp
  simp_rw [hleft]
  have hright : (1 : ℂ) / (Real.sqrt (Fintype.card F : ℝ) : ℂ) *
      (1 / (Real.sqrt (Fintype.card F : ℝ) : ℂ)) =
      1 / ((Real.sqrt (Fintype.card F : ℝ) : ℂ)) ^ 2 := by
    field_simp
  rw [hright, ← Finset.sum_div, ← add_div, hoffC]
  norm_num

/-- A record of an oracle-call count and a family of states with unit self-pairing and zero
pairing for distinct shifts. -/
structure SLSProcedure (F : Type*) [Field F] [Fintype F] where

  oracleCalls : ℕ

  state : F → (F ⊕ Unit → ℂ)

  norm : ∀ s, ∑ x, state s x * state s x = 1

  orthogonal : ∀ s r, s ≠ r → ∑ x, state s x * state r x = 0

/-- There exists an `SLSProcedure` with call count two whose states are `slsState` and whose
state pairings equal the Kronecker delta. See [VanDam2002]. -/
theorem source_theorem2_twoQuerySLS (hF : ringChar F ≠ 2) (hq : 1 < Fintype.card F) :
    ∃ P : SLSProcedure F,
      P.oracleCalls = 2 ∧
      (∀ s, P.state s = slsState (F := F) s) ∧
      (∀ s r : F, (∑ x, slsState (F := F) s x * slsState (F := F) r x) =
        if s = r then 1 else 0) := by
  refine ⟨{ oracleCalls := 2
            state := slsState
            norm := fun s => slsState_norm hF hq s
            orthogonal := fun s r hsr => slsState_orthogonal hF hq hsr }, rfl, fun _ => rfl, ?_⟩
  intro s r
  by_cases hsr : s = r
  · subst hsr
    rw [if_pos rfl]
    exact slsState_norm hF hq s
  · rw [if_neg hsr]
    exact slsState_orthogonal hF hq hsr

end Qatlib.Papers.WeighMatrix00.MainResults
