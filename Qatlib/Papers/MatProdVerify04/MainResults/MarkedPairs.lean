/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MatProdVerify04.MainResults.MarkedFraction
import Qatlib.Papers.MatProdVerify04.MainResults.RevealingProbability
import Qatlib.Papers.MatProdVerify04.MainResults.TailMass
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Uniform marked subsets and windows

`uniformOn`, `uniformSubset`, and `uniformWindow` describe uniform sampling from finite sets and
rectangular windows. Exact counts for avoiding a fixed set lead to `fixed_window_hit` and the
averaged marked window estimate `lemma8_average`. The paper context is [BuhrmanSpalek2006].

## Main statements

* `uniformSubset_avoid_mass`: exact avoidance probability as a binomial ratio.
* `lemma8_average`: average lower bound for a uniform error set of fixed size.

## References

* [Buhrman and Špalek, 2006][BuhrmanSpalek2006]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.MatProdVerify04.MainResults

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.ProbabilityCore.Concentration

/-- The uniform distribution on the nonempty finite set `S`, with zero mass outside `S`. -/
def uniformOn {α : Type*} [Fintype α] [DecidableEq α] (S : Finset α)
    (hS : S.Nonempty) : FinDist α where
  prob a := if a ∈ S then ((S.card : ℝ))⁻¹ else 0
  nonneg a := by
    by_cases h : a ∈ S
    · rw [if_pos h]; positivity
    · rw [if_neg h]
  sum_one := by
    classical
    have hcard : (0 : ℝ) < (S.card : ℝ) := by
      have : 0 < S.card := Finset.card_pos.mpr hS
      exact_mod_cast this
    have hsum : (∑ a : α, (if a ∈ S then ((S.card : ℝ))⁻¹ else 0))
        = ∑ _a ∈ S, ((S.card : ℝ))⁻¹ := by
      rw [← Finset.sum_filter]
      refine Finset.sum_congr ?_ (fun a _ => rfl)
      ext a
      simp
    rw [hsum, Finset.sum_const, nsmul_eq_mul]
    exact mul_inv_cancel₀ hcard.ne'

/-- The mass of an event under `uniformOn S hS` is the fraction of elements of `S` satisfying
it. -/
theorem uniformOn_eventMass {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) (hS : S.Nonempty) (E : α → Prop) [DecidablePred E] :
    eventMass (uniformOn S hS) E = ((S.filter E).card : ℝ) / (S.card : ℝ) := by
  classical
  have hcard : (0 : ℝ) < (S.card : ℝ) := by
    have : 0 < S.card := Finset.card_pos.mpr hS
    exact_mod_cast this
  unfold eventMass uniformOn
  rw [Finset.sum_filter]
  have hcombine : ∀ a : α,
      (if E a then (if a ∈ S then ((S.card : ℝ))⁻¹ else 0) else 0)
        = (if (a ∈ S ∧ E a) then ((S.card : ℝ))⁻¹ else 0) := by
    intro a
    by_cases hE : E a <;> by_cases hS' : a ∈ S <;> simp [hE, hS']
  simp only [hcombine]
  rw [← Finset.sum_filter]
  have hfilter : (Finset.univ.filter (fun a => a ∈ S ∧ E a)) = S.filter E := by
    ext a
    simp [and_comm]
  rw [hfilter, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

/-- An element outside `S` has zero probability under the uniform distribution on `S`. -/
theorem uniformOn_prob_notMem {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) (hS : S.Nonempty) {a : α} (ha : a ∉ S) :
    (uniformOn S hS).prob a = 0 := by
  simp only [uniformOn]
  rw [if_neg ha]

/-- The uniform distribution on all `t`-element subsets of the finite type `V`. -/
def uniformSubset {V : Type*} [Fintype V] [DecidableEq V] (t : ℕ)
    (ht : t ≤ Fintype.card V) : FinDist (Finset V) :=
  uniformOn ((Finset.univ : Finset V).powersetCard t)
    (Finset.powersetCard_nonempty.mpr (by simpa using! ht))

/-- The uniform distribution on pairs consisting of an `r`-element row subset and an `s`-element
column subset. -/
def uniformWindow {Row Col : Type*} [Fintype Row] [DecidableEq Row]
    [Fintype Col] [DecidableEq Col] (r s : ℕ)
    (hr : r ≤ Fintype.card Row) (hs : s ≤ Fintype.card Col) :
    FinDist (Finset Row × Finset Col) :=
  uniformOn (((Finset.univ : Finset Row).powersetCard r).product
      ((Finset.univ : Finset Col).powersetCard s))
    ((Finset.powersetCard_nonempty.mpr (by simpa using! hr)).product
      (Finset.powersetCard_nonempty.mpr (by simpa using! hs)))

/-- The set of positions in the rectangular window determined by a row subset and a column
subset. -/
def windowCells {Row Col : Type*} (RS : Finset Row × Finset Col) : Finset (Row × Col) :=
  RS.1 ×ˢ RS.2

/-- The `t`-element subsets disjoint from `B` are precisely the `t`-element subsets of its
complement. -/
theorem powersetCard_filter_disjoint {V : Type*} [Fintype V] [DecidableEq V]
    (B : Finset V) (t : ℕ) :
    ((Finset.univ : Finset V).powersetCard t).filter (fun W => Disjoint W B)
      = (Finset.univ \ B).powersetCard t := by
  classical
  ext W
  simp only [Finset.mem_filter, Finset.mem_powersetCard]
  constructor
  · rintro ⟨⟨-, hc⟩, hd⟩
    refine ⟨?_, hc⟩
    intro x hx
    rw [Finset.mem_sdiff]
    exact ⟨Finset.mem_univ x, (Finset.disjoint_left.mp hd) hx⟩
  · rintro ⟨hsub, hc⟩
    refine ⟨⟨hsub.trans (Finset.sdiff_subset : (Finset.univ \ B) ⊆ Finset.univ), hc⟩, ?_⟩
    rw [Finset.disjoint_left]
    intro x hx hxB
    have hmem := hsub hx
    rw [Finset.mem_sdiff] at hmem
    exact hmem.2 hxB

/-- There are `choose (Fintype.card V - B.card) t` subsets of size `t` disjoint from `B`. -/
theorem card_powersetCard_filter_disjoint {V : Type*} [Fintype V] [DecidableEq V]
    (B : Finset V) (t : ℕ) :
    (((Finset.univ : Finset V).powersetCard t).filter (fun W => Disjoint W B)).card
      = (Fintype.card V - B.card).choose t := by
  classical
  rw [powersetCard_filter_disjoint, Finset.card_powersetCard]
  congr 1
  rw [Finset.card_sdiff]
  simp

/-- The probability that a uniform `t`-element subset avoids `B` is the ratio `choose
(Fintype.card V - B.card) t / choose (Fintype.card V) t`. See [BuhrmanSpalek2006]. -/
theorem uniformSubset_avoid_mass {V : Type*} [Fintype V] [DecidableEq V]
    (t : ℕ) (ht : t ≤ Fintype.card V) (B : Finset V) :
    eventMass (uniformSubset (V := V) t ht) (fun W => Disjoint W B)
      = (((Fintype.card V - B.card).choose t : ℝ)) / ((Fintype.card V).choose t : ℝ) := by
  classical
  unfold uniformSubset
  rw [uniformOn_eventMass,
    card_powersetCard_filter_disjoint B t, Finset.card_powersetCard,
    Finset.card_univ]

/-- For positive `N` and `m ≤ N`, bounds the binomial avoidance ratio by `(1 - m / N) ^ t`. See
[BuhrmanSpalek2006]. -/
theorem choose_ratio_le_pow (N m t : ℕ) (hN : 0 < N) (hm : m ≤ N) :
    ((N - m).choose t : ℝ) / (N.choose t : ℝ) ≤ (1 - (m : ℝ) / N) ^ t := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hmR : (m : ℝ) ≤ (N : ℝ) := by exact_mod_cast hm
  have hbase : (0 : ℝ) ≤ 1 - (m : ℝ) / N := by
    rw [sub_nonneg, div_le_one hNpos]; exact hmR
  rcases lt_or_ge (N - m) t with hlt | hge
  · have h0 : (N - m).choose t = 0 := Nat.choose_eq_zero_of_lt hlt
    rw [h0]
    simp only [Nat.cast_zero, zero_div]
    exact pow_nonneg hbase t
  · have htN : t ≤ N := le_trans hge (Nat.sub_le N m)
    have htfact : (t.factorial : ℝ) ≠ 0 := by exact_mod_cast t.factorial_ne_zero
    have hratio : ∀ (M : ℕ), t ≤ M → (M.choose t : ℝ)
        = (∏ i ∈ Finset.range t, ((M : ℝ) - (i : ℝ))) / (t.factorial : ℝ) := by
      intro M hM
      have hnat : M.descFactorial t = t.factorial * M.choose t :=
        Nat.descFactorial_eq_factorial_mul_choose M t
      have hprod : (M.descFactorial t : ℝ)
          = ∏ i ∈ Finset.range t, ((M : ℝ) - (i : ℝ)) := by
        rw [Nat.descFactorial_eq_prod_range]
        push_cast
        refine Finset.prod_congr rfl (fun i hi => ?_)
        have hi' : i < t := Finset.mem_range.mp hi
        rw [Nat.cast_sub (le_trans (le_of_lt hi') hM)]
      have hval : (t.factorial : ℝ) * (M.choose t : ℝ)
          = ∏ i ∈ Finset.range t, ((M : ℝ) - (i : ℝ)) := by
        rw [← hprod]
        exact_mod_cast hnat.symm
      rw [eq_div_iff_mul_eq htfact, mul_comm]
      exact hval
    rw [hratio (N - m) hge, hratio N htN]
    have hNm : ((N - m : ℕ) : ℝ) = (N : ℝ) - (m : ℝ) := by rw [Nat.cast_sub hm]
    simp only [hNm]
    have hcancel : (∏ i ∈ Finset.range t, ((N : ℝ) - (m : ℝ) - (i : ℝ)))
          / (t.factorial : ℝ)
          / ((∏ i ∈ Finset.range t, ((N : ℝ) - (i : ℝ))) / (t.factorial : ℝ))
        = (∏ i ∈ Finset.range t, ((N : ℝ) - (m : ℝ) - (i : ℝ)))
          / (∏ i ∈ Finset.range t, ((N : ℝ) - (i : ℝ))) := by
      rw [div_div_div_cancel_right₀ htfact]
    rw [hcancel, ← Finset.prod_div_distrib]

    have hterm : ∀ i ∈ Finset.range t,
        ((N : ℝ) - (m : ℝ) - (i : ℝ)) / ((N : ℝ) - (i : ℝ))
          ≤ ((N : ℝ) - (m : ℝ)) / (N : ℝ) := by
      intro i hi
      have hi' : i < t := Finset.mem_range.mp hi
      have hlt' : i < N - m := lt_of_lt_of_le hi' hge
      have hile : (i : ℝ) < (N : ℝ) - (m : ℝ) := by
        have h1 : (i : ℝ) < ((N - m : ℕ) : ℝ) := by exact_mod_cast hlt'
        rwa [Nat.cast_sub hm] at h1
      have hden1 : (0 : ℝ) < (N : ℝ) - (i : ℝ) := by
        have hNmle : (N : ℝ) - (m : ℝ) ≤ (N : ℝ) := by linarith
        linarith
      have hden2 : (0 : ℝ) < (N : ℝ) := hNpos
      rw [div_le_div_iff₀ hden1 hden2]
      have hmi : (0 : ℝ) ≤ (m : ℝ) * (i : ℝ) :=
        mul_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg i)
      nlinarith [hmi]
    have hnonneg : ∀ i ∈ Finset.range t,
        (0 : ℝ) ≤ ((N : ℝ) - (m : ℝ) - (i : ℝ)) / ((N : ℝ) - (i : ℝ)) := by
      intro i hi
      apply div_nonneg
      · have hi' : i < t := Finset.mem_range.mp hi
        have hlt' : i < N - m := lt_of_lt_of_le hi' hge
        have hile : (i : ℝ) < (N : ℝ) - (m : ℝ) := by
          have h1 : (i : ℝ) < ((N - m : ℕ) : ℝ) := by exact_mod_cast hlt'
          rwa [Nat.cast_sub hm] at h1
        linarith
      · have hi' : i < t := Finset.mem_range.mp hi
        have hlt' : i < N - m := lt_of_lt_of_le hi' hge
        have hile : (i : ℝ) < (N : ℝ) - (m : ℝ) := by
          have h1 : (i : ℝ) < ((N - m : ℕ) : ℝ) := by exact_mod_cast hlt'
          rwa [Nat.cast_sub hm] at h1
        have hNmle : (N : ℝ) - (m : ℝ) ≤ (N : ℝ) := by linarith
        linarith
    calc (∏ i ∈ Finset.range t, ((N : ℝ) - (m : ℝ) - (i : ℝ)) / ((N : ℝ) - (i : ℝ)))
        ≤ ∏ _i ∈ Finset.range t, ((N : ℝ) - (m : ℝ)) / (N : ℝ) := by
          refine Finset.prod_le_prod₀ hnonneg (fun i hi => hterm i hi)
      _ = (((N : ℝ) - (m : ℝ)) / (N : ℝ)) ^ t := by
          rw [Finset.prod_const, Finset.card_range]
      _ = (1 - (m : ℝ) / N) ^ t := by
          congr 1
          field_simp

/-- If `t * B.card ≤ Fintype.card V` in a nonempty universe, a uniform `t`-element subset meets
`B` with probability at least `t * B.card / (2 * Fintype.card V)`. See [BuhrmanSpalek2006]. -/
theorem fixed_window_hit {V : Type*} [Fintype V] [DecidableEq V]
    (t : ℕ) (ht : t ≤ Fintype.card V) (B : Finset V) (hB : B.card ≤ Fintype.card V)
    (hN : 0 < Fintype.card V)
    (hsmall : (t : ℝ) * (B.card : ℝ) ≤ (Fintype.card V : ℝ)) :
    (1 / 2) * (t : ℝ) * (B.card : ℝ) / (Fintype.card V : ℝ)
      ≤ eventMass (uniformSubset (V := V) t ht) (fun W => ¬ Disjoint W B) := by
  classical
  have hNpos : (0 : ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast hN
  have hcomp : eventMass (uniformSubset (V := V) t ht) (fun W => ¬ Disjoint W B)
      = 1 - eventMass (uniformSubset (V := V) t ht) (fun W => Disjoint W B) := by
    have h := eventMass_compl (uniformSubset (V := V) t ht) (fun W => Disjoint W B)
    linarith
  rw [hcomp, uniformSubset_avoid_mass t ht B]
  have hratio := choose_ratio_le_pow (Fintype.card V) B.card t hN hB
  have hx0 : (0 : ℝ) ≤ (B.card : ℝ) / (Fintype.card V : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) hNpos.le
  have hx1 : (B.card : ℝ) / (Fintype.card V : ℝ) ≤ 1 := by
    rw [div_le_one hNpos]; exact_mod_cast hB
  have htx : (t : ℝ) * ((B.card : ℝ) / (Fintype.card V : ℝ)) ≤ 1 := by
    rw [mul_div_assoc', div_le_one hNpos]; exact hsmall
  have hgeo := geometric_hit_bound hx0 hx1 t htx
  have hrewrite : (1 / 2) * (t : ℝ) * (B.card : ℝ) / (Fintype.card V : ℝ)
      = (t : ℝ) * ((B.card : ℝ) / (Fintype.card V : ℝ)) / 2 := by ring
  rw [hrewrite]
  linarith [hratio, hgeo]

/-- When `t * r * s` is at most the number of matrix positions, the expected mass of windows
meeting a uniform `t`-element error set is at least `t * r * s` divided by twice the number
of positions. See [BuhrmanSpalek2006]. -/
theorem lemma8_average {Row Col : Type*} [Fintype Row] [DecidableEq Row]
    [Fintype Col] [DecidableEq Col] (r s t : ℕ)
    (hr : r ≤ Fintype.card Row) (hs : s ≤ Fintype.card Col)
    (ht : t ≤ Fintype.card (Row × Col))
    (hN : 0 < Fintype.card (Row × Col))
    (hsmall : (t : ℝ) * (r : ℝ) * (s : ℝ)
      ≤ (Fintype.card Row : ℝ) * (Fintype.card Col : ℝ)) :
    (1 / 2) * (t : ℝ) * (r : ℝ) * (s : ℝ)
        / ((Fintype.card Row : ℝ) * (Fintype.card Col : ℝ))
      ≤ (uniformSubset (V := Row × Col) t ht).expect
          (fun W => eventMass (uniformWindow r s hr hs)
            (fun RS => ¬ Disjoint W (windowCells RS))) := by
  classical
  set N : ℝ := (Fintype.card Row : ℝ) * (Fintype.card Col : ℝ) with hNdef
  set Nc : ℝ := (Fintype.card (Row × Col) : ℝ) with hNcdef
  have hNc : Nc = N := by
    rw [hNcdef, hNdef, Fintype.card_prod]; push_cast; ring
  have hprod : (0 : ℕ) < Fintype.card Row * Fintype.card Col := by
    rw [← Fintype.card_prod]; exact hN
  have hNpos : (0 : ℝ) < N := by rw [hNdef]; exact_mod_cast hprod
  set C : ℝ := (1 / 2) * (t : ℝ) * (r : ℝ) * (s : ℝ) / N with hC

  have hwinCard : ∀ RS : Finset Row × Finset Col,
      RS ∈ ((Finset.univ : Finset Row).powersetCard r).product
          ((Finset.univ : Finset Col).powersetCard s) →
      (windowCells RS).card = r * s := by
    intro RS hRS
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hRS
    rw [windowCells, Finset.card_product,
      (Finset.mem_powersetCard.mp h1).2, (Finset.mem_powersetCard.mp h2).2]
  have hperWindow : ∀ RS : Finset Row × Finset Col,
      RS ∈ ((Finset.univ : Finset Row).powersetCard r).product
          ((Finset.univ : Finset Col).powersetCard s) →
      C ≤ eventMass (uniformSubset (V := Row × Col) t ht)
            (fun W => ¬ Disjoint W (windowCells RS)) := by
    intro RS hRS
    have hcardB : (windowCells RS).card ≤ Fintype.card (Row × Col) := by
      rw [hwinCard RS hRS, Fintype.card_prod]
      exact Nat.mul_le_mul hr hs
    have hsmallB : (t : ℝ) * ((windowCells RS).card : ℝ) ≤ (Fintype.card (Row × Col) : ℝ) := by
      have hcast : ((windowCells RS).card : ℝ) = (r : ℝ) * (s : ℝ) := by
        rw [hwinCard RS hRS]; push_cast; ring
      rw [hcast, Fintype.card_prod]
      push_cast
      nlinarith [hsmall]
    have h1 := fixed_window_hit t ht (windowCells RS) hcardB hN hsmallB
    have hce : C = (1 / 2) * (t : ℝ) * ((windowCells RS).card : ℝ) / Nc := by
      rw [hC]
      have hcast : ((windowCells RS).card : ℝ) = (r : ℝ) * (s : ℝ) := by
        rw [hwinCard RS hRS]; push_cast; ring
      rw [hcast, hNc]
      ring
    rw [hce]
    exact h1

  rw [FinDist.expect]
  have hexpand : (∑ W, (uniformSubset (V := Row × Col) t ht).prob W *
        eventMass (uniformWindow r s hr hs) (fun RS => ¬ Disjoint W (windowCells RS)))
      = ∑ W, (uniformSubset (V := Row × Col) t ht).prob W *
          ∑ RS, (uniformWindow r s hr hs).prob RS *
            (if ¬ Disjoint W (windowCells RS) then (1 : ℝ) else 0) := by
    refine Finset.sum_congr rfl (fun W _ => ?_)
    congr 1
    exact eventMass_ite (uniformWindow r s hr hs) (fun RS => ¬ Disjoint W (windowCells RS))
  rw [hexpand]
  have hswap : (∑ W, (uniformSubset (V := Row × Col) t ht).prob W *
          ∑ RS, (uniformWindow r s hr hs).prob RS *
            (if ¬ Disjoint W (windowCells RS) then (1 : ℝ) else 0))
      = ∑ RS, (uniformWindow r s hr hs).prob RS *
          ∑ W, (uniformSubset (V := Row × Col) t ht).prob W *
            (if ¬ Disjoint W (windowCells RS) then (1 : ℝ) else 0) := by
    calc (∑ W, (uniformSubset (V := Row × Col) t ht).prob W *
            ∑ RS, (uniformWindow r s hr hs).prob RS *
              (if ¬ Disjoint W (windowCells RS) then (1 : ℝ) else 0))
        = ∑ W, ∑ RS, (uniformSubset (V := Row × Col) t ht).prob W *
              ((uniformWindow r s hr hs).prob RS *
                (if ¬ Disjoint W (windowCells RS) then (1 : ℝ) else 0)) := by
            refine Finset.sum_congr rfl (fun W _ => ?_)
            rw [Finset.mul_sum]
      _ = ∑ RS, ∑ W, (uniformSubset (V := Row × Col) t ht).prob W *
              ((uniformWindow r s hr hs).prob RS *
                (if ¬ Disjoint W (windowCells RS) then (1 : ℝ) else 0)) :=
            Finset.sum_comm
      _ = ∑ RS, (uniformWindow r s hr hs).prob RS *
              ∑ W, (uniformSubset (V := Row × Col) t ht).prob W *
                (if ¬ Disjoint W (windowCells RS) then (1 : ℝ) else 0) := by
            refine Finset.sum_congr rfl (fun RS _ => ?_)
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun W _ => by ring)
  rw [hswap]

  have hkey : ∀ RS, (uniformWindow r s hr hs).prob RS * C
      ≤ (uniformWindow r s hr hs).prob RS *
          ∑ W, (uniformSubset (V := Row × Col) t ht).prob W *
            (if ¬ Disjoint W (windowCells RS) then (1 : ℝ) else 0) := by
    intro RS
    by_cases hRS : RS ∈ ((Finset.univ : Finset Row).powersetCard r).product
        ((Finset.univ : Finset Col).powersetCard s)
    · have hb := hperWindow RS hRS
      have hrewrite : ∑ W, (uniformSubset (V := Row × Col) t ht).prob W *
            (if ¬ Disjoint W (windowCells RS) then (1 : ℝ) else 0)
          = eventMass (uniformSubset (V := Row × Col) t ht)
              (fun W => ¬ Disjoint W (windowCells RS)) := by
        rw [eventMass_ite]
      rw [hrewrite]
      exact mul_le_mul_of_nonneg_left hb ((uniformWindow r s hr hs).nonneg RS)
    · have hzero : (uniformWindow r s hr hs).prob RS = 0 := by
        show (uniformOn (((Finset.univ : Finset Row).powersetCard r).product
          ((Finset.univ : Finset Col).powersetCard s)) _).prob RS = 0
        exact uniformOn_prob_notMem _ _ hRS
      simp [hzero]
  have hsum : ∑ RS, (uniformWindow r s hr hs).prob RS * C = C := by
    rw [← Finset.sum_mul, (uniformWindow r s hr hs).sum_one, one_mul]
  calc C = ∑ RS, (uniformWindow r s hr hs).prob RS * C := hsum.symm
    _ ≤ ∑ RS, (uniformWindow r s hr hs).prob RS *
          ∑ W, (uniformSubset (V := Row × Col) t ht).prob W *
            (if ¬ Disjoint W (windowCells RS) then (1 : ℝ) else 0) :=
          Finset.sum_le_sum (fun RS _ => hkey RS)

end Qatlib.Papers.MatProdVerify04.MainResults
