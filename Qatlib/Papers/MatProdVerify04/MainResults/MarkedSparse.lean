/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MatProdVerify04.MainResults.MarkedPairs
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.MatProdVerify04.MainResults

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.ProbabilityCore.Concentration
set_option warningAsError false

theorem eventMass_congr' {X : Type*} [Fintype X] (p : FinDist X)
    {E F : X → Prop} [DecidablePred E] [DecidablePred F]
    (h : ∀ x, E x ↔ F x) : eventMass p E = eventMass p F := by
  classical
  unfold eventMass
  exact Finset.sum_congr (Finset.filter_congr (fun x _ => h x)) (fun _ _ => rfl)

def rowCols {Row Col : Type*} [DecidableEq Row] [DecidableEq Col]
    (W : Finset (Row × Col)) (i : Row) : Finset Col :=
  (W.filter (fun c => c.1 = i)).image (fun c => c.2)

theorem mem_rowCols {Row Col : Type*} [DecidableEq Row] [DecidableEq Col]
    (W : Finset (Row × Col)) (i : Row) (j : Col) :
    j ∈ rowCols W i ↔ (i, j) ∈ W := by
  classical
  unfold rowCols
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨c, ⟨hcW, hc1⟩, hc2⟩
    have hceq : c = (i, j) := by
      rcases c with ⟨a, b⟩
      simp_all
    simpa [hceq] using! hcW
  · intro h
    exact ⟨(i, j), ⟨h, rfl⟩, rfl⟩

theorem sum_rowCols_card {Row Col : Type*} [Fintype Row] [DecidableEq Row]
    [DecidableEq Col] (W : Finset (Row × Col)) :
    (∑ i, (rowCols W i).card) = W.card := by
  classical
  have hfiber : W.card = ∑ i, (W.filter (fun c => c.1 = i)).card := by
    have h := Finset.card_eq_sum_card_fiberwise (s := W)
      (t := (Finset.univ : Finset Row)) (f := Prod.fst)
      (fun a _ => Finset.mem_univ _)
    simpa using! h
  rw [hfiber]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [rowCols]
  exact Finset.card_image_of_injOn
    (s := W.filter (fun c => c.1 = i)) (f := fun c : Row × Col => c.2) (by
      intro a ha b hb h
      rw [Finset.mem_coe, Finset.mem_filter] at ha hb
      exact Prod.ext (ha.2.trans hb.2.symm) h)

def maxRowW {Row Col : Type*} [Fintype Row] [DecidableEq Row] [DecidableEq Col]
    (W : Finset (Row × Col)) : ℕ :=
  Finset.univ.sup (fun i => (rowCols W i).card)

def nzRows {Row Col : Type*} [Fintype Row] [DecidableEq Row] [DecidableEq Col]
    (W : Finset (Row × Col)) : Finset Row :=
  Finset.univ.filter (fun i => (rowCols W i).Nonempty)

def markRows {Row Col : Type*} [Fintype Row] [DecidableEq Row] [DecidableEq Col]
    (W : Finset (Row × Col)) (S : Finset Col) : Finset Row :=
  Finset.univ.filter (fun i => ¬ Disjoint (rowCols W i) S)

theorem markRows_subset_nzRows {Row Col : Type*} [Fintype Row] [DecidableEq Row]
    [DecidableEq Col] (W : Finset (Row × Col)) (S : Finset Col) :
    markRows W S ⊆ nzRows W := by
  classical
  intro i hi
  rw [markRows, Finset.mem_filter] at hi
  rw [nzRows, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [Finset.not_disjoint_iff] at hi
  obtain ⟨j, hjN, -⟩ := hi.2
  exact ⟨j, hjN⟩

theorem nzRows_card_pos {Row Col : Type*} [Fintype Row] [DecidableEq Row]
    [DecidableEq Col] (W : Finset (Row × Col)) (hW : W.Nonempty) :
    0 < (nzRows W).card := by
  classical
  obtain ⟨⟨i, j⟩, hp⟩ := hW
  rw [Finset.card_pos]
  refine ⟨i, ?_⟩
  rw [nzRows, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, ⟨j, (mem_rowCols W i j).mpr hp⟩⟩

theorem maxRowW_pos {Row Col : Type*} [Fintype Row] [DecidableEq Row]
    [DecidableEq Col] (W : Finset (Row × Col)) (hW : W.Nonempty) :
    0 < maxRowW W := by
  classical
  obtain ⟨⟨i, j⟩, hp⟩ := hW
  have h1 : 0 < (rowCols W i).card :=
    Finset.card_pos.mpr ⟨j, (mem_rowCols W i j).mpr hp⟩
  have h2 : (rowCols W i).card ≤ maxRowW W := by
    rw [maxRowW]
    exact Finset.le_sup (f := fun j => (rowCols W j).card) (Finset.mem_univ i)
  omega

theorem rowCols_card_le_maxRowW {Row Col : Type*} [Fintype Row] [DecidableEq Row]
    [DecidableEq Col] (W : Finset (Row × Col)) (i : Row) :
    (rowCols W i).card ≤ maxRowW W := by
  rw [maxRowW]
  exact Finset.le_sup (f := fun j => (rowCols W j).card) (Finset.mem_univ i)

theorem not_disjoint_window_iff {Row Col : Type*} [Fintype Row] [DecidableEq Row]
    [DecidableEq Col] (W : Finset (Row × Col)) (RS : Finset Row × Finset Col) :
    ¬ Disjoint W (windowCells RS) ↔ ¬ Disjoint RS.1 (markRows W RS.2) := by
  classical
  rw [Finset.not_disjoint_iff, Finset.not_disjoint_iff]
  constructor
  · rintro ⟨p, hpW, hpRS⟩
    obtain ⟨hpR, hpS⟩ := Finset.mem_product.mp hpRS
    refine ⟨p.1, hpR, ?_⟩
    rw [markRows, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [Finset.not_disjoint_iff]
    exact ⟨p.2, (mem_rowCols W p.1 p.2).mpr hpW, hpS⟩
  · rintro ⟨i, hiR, hiMark⟩
    rw [markRows, Finset.mem_filter] at hiMark
    rw [Finset.not_disjoint_iff] at hiMark
    obtain ⟨j, hjN, hjS⟩ := hiMark.2
    refine ⟨(i, j), ?_, ?_⟩
    · exact (mem_rowCols W i j).mp hjN
    · exact Finset.mem_product.mpr ⟨hiR, hjS⟩

theorem window_prob_factor {Row Col : Type*} [Fintype Row] [DecidableEq Row]
    [Fintype Col] [DecidableEq Col] (r s : ℕ) (hr : r ≤ Fintype.card Row)
    (hs : s ≤ Fintype.card Col) (RS : Finset Row × Finset Col) :
    (uniformWindow r s hr hs).prob RS
      = (uniformSubset (V := Row) r hr).prob RS.1
        * (uniformSubset (V := Col) s hs).prob RS.2 := by
  classical
  unfold uniformWindow uniformSubset uniformOn
  simp only
  by_cases h1 : RS.1 ∈ (Finset.univ : Finset Row).powersetCard r
  · by_cases h2 : RS.2 ∈ (Finset.univ : Finset Col).powersetCard s
    · have hmem : RS ∈ ((Finset.univ : Finset Row).powersetCard r).product
          ((Finset.univ : Finset Col).powersetCard s) :=
        Finset.mem_product.mpr ⟨h1, h2⟩
      have hcard : (((Finset.univ : Finset Row).powersetCard r).product
            ((Finset.univ : Finset Col).powersetCard s)).card
          = ((Finset.univ : Finset Row).powersetCard r).card
            * ((Finset.univ : Finset Col).powersetCard s).card :=
        Finset.card_product _ _
      rw [if_pos hmem, if_pos h1, if_pos h2, hcard]
      push_cast
      rw [mul_inv]
    · have hmem : RS ∉ ((Finset.univ : Finset Row).powersetCard r).product
          ((Finset.univ : Finset Col).powersetCard s) := by
        intro h
        exact h2 (Finset.mem_product.mp h).2
      rw [if_neg hmem, if_pos h1, if_neg h2, mul_zero]
  · have hmem : RS ∉ ((Finset.univ : Finset Row).powersetCard r).product
        ((Finset.univ : Finset Col).powersetCard s) := by
      intro h
      exact h1 (Finset.mem_product.mp h).1
    rw [if_neg hmem, if_neg h1, zero_mul]

theorem eventMass_window_eq {Row Col : Type*} [Fintype Row] [DecidableEq Row]
    [Fintype Col] [DecidableEq Col] (r s : ℕ) (hr : r ≤ Fintype.card Row)
    (hs : s ≤ Fintype.card Col) (P : Finset Row → Finset Col → Prop)
    [DecidableRel P] :
    eventMass (uniformWindow r s hr hs) (fun RS => P RS.1 RS.2)
      = ∑ S, (uniformSubset (V := Col) s hs).prob S *
          eventMass (uniformSubset (V := Row) r hr) (fun R => P R S) := by
  classical
  have hrew : eventMass (uniformWindow r s hr hs) (fun RS => P RS.1 RS.2)
      = ∑ RS, (uniformWindow r s hr hs).prob RS
          * (if P RS.1 RS.2 then (1 : ℝ) else 0) :=
    eventMass_ite (uniformWindow r s hr hs) (fun RS => P RS.1 RS.2)
  rw [hrew]
  simp only [eventMass_ite]
  have hL : (∑ RS : Finset Row × Finset Col, (uniformWindow r s hr hs).prob RS
        * (if P RS.1 RS.2 then (1 : ℝ) else 0))
      = ∑ RS : Finset Row × Finset Col, ((uniformSubset (V := Row) r hr).prob RS.1
          * (uniformSubset (V := Col) s hs).prob RS.2)
          * (if P RS.1 RS.2 then (1 : ℝ) else 0) :=
    Finset.sum_congr rfl (fun (RS : Finset Row × Finset Col) _ => by
      rw [window_prob_factor r s hr hs RS])
  rw [hL]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun R _ => ?_)
  ring

theorem markRows_expect_eq {Row Col : Type*} [Fintype Row] [DecidableEq Row]
    [Fintype Col] [DecidableEq Col] (W : Finset (Row × Col)) (s : ℕ)
    (hs : s ≤ Fintype.card Col) :
    (∑ S, (uniformSubset (V := Col) s hs).prob S * ((markRows W S).card : ℝ))
      = ∑ i, eventMass (uniformSubset (V := Col) s hs)
          (fun S => i ∈ markRows W S) := by
  classical
  have hexp : ∀ S, ((markRows W S).card : ℝ)
      = ∑ i, (if i ∈ markRows W S then (1 : ℝ) else 0) := by
    intro S
    have h := Finset.sum_boole (fun i => i ∈ markRows W S) (Finset.univ) (R := ℝ)
    rw [h]
    simp
  simp only [hexp, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [eventMass_ite]

theorem lemma9_bound {Row Col : Type*} [Fintype Row] [DecidableEq Row]
    [Fintype Col] [DecidableEq Col] (W : Finset (Row × Col)) (r s : ℕ)
    (hRow : 0 < Fintype.card Row) (hCol : 0 < Fintype.card Col)
    (hr : r ≤ Fintype.card Row) (hs : s ≤ Fintype.card Col)
    (hrw : r ≤ Fintype.card Row / (nzRows W).card)
    (hsw : s ≤ Fintype.card Col / maxRowW W) :
    (1 / 4) * (W.card : ℝ) * (r : ℝ) * (s : ℝ)
        / ((Fintype.card Row : ℝ) * (Fintype.card Col : ℝ))
      ≤ eventMass (uniformWindow r s hr hs)
          (fun RS => ¬ Disjoint W (windowCells RS)) := by
  classical
  rcases W.eq_empty_or_nonempty with hW | hW
  · subst hW
    simp only [Finset.card_empty, Nat.cast_zero, mul_zero, zero_mul, zero_div]
    exact Finset.sum_nonneg (fun x _ => (uniformWindow r s hr hs).nonneg x)
  · set nR : ℝ := (Fintype.card Row : ℝ) with hRn
    set nC : ℝ := (Fintype.card Col : ℝ) with hCn
    have hnR : 0 < nR := by rw [hRn]; exact_mod_cast hRow
    have hnC : 0 < nC := by rw [hCn]; exact_mod_cast hCol
    have hwpos : 0 < (nzRows W).card := nzRows_card_pos W hW
    have hmaxpos : 0 < maxRowW W := maxRowW_pos W hW

    have hrw' : r * (nzRows W).card ≤ Fintype.card Row := by
      have := (Nat.le_div_iff_mul_le hwpos).mp hrw
      simpa [mul_comm] using! this
    have hsw' : s * maxRowW W ≤ Fintype.card Col := by
      have := (Nat.le_div_iff_mul_le hmaxpos).mp hsw
      simpa [mul_comm] using! this

    have hperS : ∀ S : Finset Col,
        (1 / 2) * (r : ℝ) * ((markRows W S).card : ℝ) / nR
          ≤ eventMass (uniformSubset (V := Row) r hr)
              (fun R => ¬ Disjoint R (markRows W S)) := by
      intro S
      have hBS : (markRows W S).card ≤ Fintype.card Row :=
        le_trans (Finset.card_le_card (markRows_subset_nzRows W S))
          (by simpa using! Finset.card_le_univ (nzRows W))
      have hcS : ((markRows W S).card : ℝ) ≤ ((nzRows W).card : ℝ) := by
        exact_mod_cast Finset.card_le_card (markRows_subset_nzRows W S)
      have hsmall : (r : ℝ) * ((markRows W S).card : ℝ) ≤ (Fintype.card Row : ℝ) := by
        have hrle : (r : ℝ) * ((markRows W S).card : ℝ)
            ≤ (r : ℝ) * ((nzRows W).card : ℝ) := by
          exact mul_le_mul_of_nonneg_left hcS (Nat.cast_nonneg r)
        have hrw'' : (r : ℝ) * ((nzRows W).card : ℝ) ≤ (Fintype.card Row : ℝ) := by
          exact_mod_cast hrw'
        exact le_trans hrle hrw''
      have h := fixed_window_hit r hr (markRows W S) hBS hRow hsmall
      rwa [hRn]

    have hperRow : ∀ i : Row,
        (1 / 2) * (s : ℝ) * ((rowCols W i).card : ℝ) / nC
          ≤ eventMass (uniformSubset (V := Col) s hs)
              (fun S => i ∈ markRows W S) := by
      intro i
      have hB : (rowCols W i).card ≤ Fintype.card Col :=
        Finset.card_le_univ (rowCols W i)
      have hsmall : (s : ℝ) * ((rowCols W i).card : ℝ) ≤ (Fintype.card Col : ℝ) := by
        have hcle : ((rowCols W i).card : ℝ) ≤ (maxRowW W : ℝ) := by
          exact_mod_cast rowCols_card_le_maxRowW W i
        have hle1 : (s : ℝ) * ((rowCols W i).card : ℝ)
            ≤ (s : ℝ) * (maxRowW W : ℝ) :=
          mul_le_mul_of_nonneg_left hcle (Nat.cast_nonneg s)
        have hle2 : (s : ℝ) * (maxRowW W : ℝ) ≤ (Fintype.card Col : ℝ) := by
          exact_mod_cast hsw'
        exact le_trans hle1 hle2
      have h := fixed_window_hit s hs (rowCols W i) hB hCol hsmall

      have hev : eventMass (uniformSubset (V := Col) s hs)
            (fun S => ¬ Disjoint S (rowCols W i))
          = eventMass (uniformSubset (V := Col) s hs)
            (fun S => i ∈ markRows W S) := by
        refine eventMass_congr' (uniformSubset (V := Col) s hs) (fun S => ?_)
        rw [markRows, Finset.mem_filter]
        have hcomm : ¬ Disjoint S (rowCols W i) ↔ ¬ Disjoint (rowCols W i) S :=
          not_congr disjoint_comm
        exact ⟨fun hh => ⟨Finset.mem_univ _, hcomm.mp hh⟩,
          fun hh => hcomm.mpr hh.2⟩
      rw [← hev, hCn]
      exact h

    have hwin_eq : eventMass (uniformWindow r s hr hs)
          (fun RS => ¬ Disjoint W (windowCells RS))
        = ∑ S, (uniformSubset (V := Col) s hs).prob S *
            eventMass (uniformSubset (V := Row) r hr)
              (fun R => ¬ Disjoint R (markRows W S)) := by
      have hev : eventMass (uniformWindow r s hr hs)
            (fun RS => ¬ Disjoint W (windowCells RS))
          = eventMass (uniformWindow r s hr hs)
            (fun RS => ¬ Disjoint RS.1 (markRows W RS.2)) := by
        refine eventMass_congr' (uniformWindow r s hr hs) (fun RS => ?_)
        exact not_disjoint_window_iff W RS
      rw [hev]
      exact eventMass_window_eq r s hr hs (fun R S => ¬ Disjoint R (markRows W S))

    have hstep1 : (∑ S, (uniformSubset (V := Col) s hs).prob S *
          ((1 / 2) * (r : ℝ) * ((markRows W S).card : ℝ) / nR))
        ≤ ∑ S, (uniformSubset (V := Col) s hs).prob S *
            eventMass (uniformSubset (V := Row) r hr)
              (fun R => ¬ Disjoint R (markRows W S)) := by
      refine Finset.sum_le_sum (fun S _ => ?_)
      exact mul_le_mul_of_nonneg_left (hperS S) ((uniformSubset (V := Col) s hs).nonneg S)

    have hstep1' : (∑ S, (uniformSubset (V := Col) s hs).prob S *
          ((1 / 2) * (r : ℝ) * ((markRows W S).card : ℝ) / nR))
        = (1 / 2) * (r : ℝ) / nR *
          ∑ S, (uniformSubset (V := Col) s hs).prob S * ((markRows W S).card : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun S _ => ?_)
      ring

    have hstep2 : (1 / 2) * (s : ℝ) / nC * (W.card : ℝ)
        ≤ ∑ S, (uniformSubset (V := Col) s hs).prob S * ((markRows W S).card : ℝ) := by
      rw [markRows_expect_eq W s hs]
      have hper : ∀ i : Row,
          (1 / 2) * (s : ℝ) * ((rowCols W i).card : ℝ) / nC
            ≤ eventMass (uniformSubset (V := Col) s hs) (fun S => i ∈ markRows W S) :=
        hperRow
      have hsum : (∑ i, (1 / 2) * (s : ℝ) * ((rowCols W i).card : ℝ) / nC)
          ≤ ∑ i, eventMass (uniformSubset (V := Col) s hs) (fun S => i ∈ markRows W S) :=
        Finset.sum_le_sum (fun i _ => hper i)
      have hleft : (∑ i, (1 / 2) * (s : ℝ) * ((rowCols W i).card : ℝ) / nC)
          = (1 / 2) * (s : ℝ) / nC * (W.card : ℝ) := by
        rw [← Finset.sum_div, ← Finset.mul_sum, ← Nat.cast_sum, sum_rowCols_card]
        ring
      rw [← hleft]
      exact hsum

    have harith : (1 / 4) * (W.card : ℝ) * (r : ℝ) * (s : ℝ) / (nR * nC)
        = (1 / 2) * (r : ℝ) / nR * ((1 / 2) * (s : ℝ) / nC * (W.card : ℝ)) := by
      field_simp
      ring
    rw [hwin_eq, harith]
    calc (1 / 2) * (r : ℝ) / nR * ((1 / 2) * (s : ℝ) / nC * (W.card : ℝ))
        ≤ (1 / 2) * (r : ℝ) / nR
            * ∑ S, (uniformSubset (V := Col) s hs).prob S * ((markRows W S).card : ℝ) := by
          apply mul_le_mul_of_nonneg_left hstep2
          exact div_nonneg (by positivity) hnR.le
      _ = (∑ S, (uniformSubset (V := Col) s hs).prob S *
            ((1 / 2) * (r : ℝ) * ((markRows W S).card : ℝ) / nR)) := hstep1'.symm
      _ ≤ ∑ S, (uniformSubset (V := Col) s hs).prob S *
            eventMass (uniformSubset (V := Row) r hr)
              (fun R => ¬ Disjoint R (markRows W S)) := hstep1

end Qatlib.Papers.MatProdVerify04.MainResults
