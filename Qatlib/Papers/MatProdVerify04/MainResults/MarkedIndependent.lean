/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MatProdVerify04.MainResults.MarkedSparse
import Qatlib.Papers.MatProdVerify04.MainResults.TailMass
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-!
# Marked windows for independent error sets

`IsIndependent` expresses that a finite set of matrix positions has at most one position in each
row and column. The module computes inclusion probabilities for uniform subsets and the expected
number of columns reached by sampled rows, yielding `lemma10_bound` under the stated window size
condition. The paper context is [BuhrmanSpalek2006].

## Main statements

* `hitCols_expect`: expected number of columns reached by sampled rows.
* `lemma10_bound`: lower bound on the mass of windows meeting an independent error set.

## References

* [Buhrman and Špalek, 2006][BuhrmanSpalek2006]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.MatProdVerify04.MainResults

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.ProbabilityCore.Concentration

/-- The rows containing an element of `W` in column `j`. -/
def colRows {Row Col : Type*} [DecidableEq Row] [DecidableEq Col]
    (W : Finset (Row × Col)) (j : Col) : Finset Row :=
  (W.filter (fun c => c.2 = j)).image (fun c => c.1)

/-- A row belongs to `colRows W j` exactly when its position in column `j` belongs to `W`. -/
theorem mem_colRows {Row Col : Type*} [DecidableEq Row] [DecidableEq Col]
    (W : Finset (Row × Col)) (i : Row) (j : Col) :
    i ∈ colRows W j ↔ (i, j) ∈ W := by
  classical
  unfold colRows
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨c, ⟨hcW, hc2⟩, hc1⟩
    have hceq : c = (i, j) := by
      rcases c with ⟨a, b⟩
      simp_all
    simpa [hceq] using! hcW
  · intro h
    exact ⟨(i, j), ⟨h, rfl⟩, rfl⟩

/-- The condition that `W` contains at most one position in every row and every column. -/
def IsIndependent {Row Col : Type*} [Fintype Row] [DecidableEq Row]
    [DecidableEq Col] (W : Finset (Row × Col)) : Prop :=
  (∀ i, (rowCols W i).card ≤ 1) ∧ (∀ j, (colRows W j).card ≤ 1)

/-- If each row contains at most one position of `W`, then the number of positions equals the
number of nonempty rows. -/
theorem card_eq_nzRows_card {Row Col : Type*} [Fintype Row] [DecidableEq Row]
    [DecidableEq Col] (W : Finset (Row × Col))
    (hind : ∀ i, (rowCols W i).card ≤ 1) :
    W.card = (nzRows W).card := by
  classical
  rw [← sum_rowCols_card W]
  have hnz : (nzRows W).card
      = ∑ i, (if (rowCols W i).Nonempty then (1 : ℕ) else 0) := by
    rw [nzRows, Finset.card_filter]
  rw [hnz]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases h : (rowCols W i).Nonempty
  · have h1 : 0 < (rowCols W i).card := Finset.card_pos.mpr h
    have h2 := hind i
    rw [if_pos h]
    omega
  · have h0 : (rowCols W i).card = 0 :=
      Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp h)
    rw [if_neg h, h0]

/-- For positive `N` and `r ≤ N`, the ratio of the binomial coefficients `choose (N - 1) r` and
`choose N r` is `(N - r) / N`. -/
theorem choose_pred_ratio {N r : ℕ} (hN : 0 < N) (hr : r ≤ N) :
    ((N - 1).choose r : ℝ) / (N.choose r : ℝ) = ((N - r : ℕ) : ℝ) / (N : ℝ) := by
  have hpred : N = (N - 1) + 1 := (Nat.succ_pred_eq_of_pos hN).symm
  have hid : N * (N - 1).choose r = N.choose r * (N - r) := by
    have h1 := Nat.add_one_mul_choose_eq (N - 1) r
    rw [← hpred] at h1
    rw [Nat.choose_succ_right_eq N r] at h1
    exact h1
  have hchooseN : (N.choose r : ℝ) ≠ 0 := by
    have hpos : 0 < N.choose r := Nat.choose_pos hr
    exact_mod_cast hpos.ne'
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [div_eq_div_iff hchooseN hNR]
  have hidR : (N : ℝ) * ((N - 1).choose r : ℝ)
      = (N.choose r : ℝ) * ((N - r : ℕ) : ℝ) := by
    exact_mod_cast hid
  linarith

/-- A fixed element of a nonempty finite type belongs to a uniform `r`-element subset with
probability `r / Fintype.card V`. See [BuhrmanSpalek2006]. -/
theorem uniformSubset_mem_mass {V : Type*} [Fintype V] [DecidableEq V]
    (r : ℕ) (hr : r ≤ Fintype.card V) (hV : 0 < Fintype.card V) (i : V) :
    eventMass (uniformSubset (V := V) r hr) (fun R => i ∈ R)
      = (r : ℝ) / (Fintype.card V : ℝ) := by
  classical
  have hiff : ∀ R : Finset V, (i ∈ R) ↔ ¬ Disjoint R ({i} : Finset V) := by
    intro R
    rw [Finset.disjoint_singleton_right]
    exact not_not.symm
  have hcompl : eventMass (uniformSubset (V := V) r hr) (fun R => i ∈ R)
      = 1 - eventMass (uniformSubset (V := V) r hr) (fun R => Disjoint R {i}) := by
    have h := eventMass_compl (uniformSubset (V := V) r hr) (fun R => Disjoint R {i})
    have hcongr : eventMass (uniformSubset (V := V) r hr) (fun R => ¬ Disjoint R ({i} : Finset V))
        = eventMass (uniformSubset (V := V) r hr) (fun R => i ∈ R) := by
      refine eventMass_congr' (uniformSubset (V := V) r hr) (fun R => ?_)
      exact (hiff R).symm
    rw [hcongr] at h
    linarith
  rw [hcompl, uniformSubset_avoid_mass r hr {i}]
  have hcard : ({i} : Finset V).card = 1 := by simp
  rw [hcard, choose_pred_ratio hV hr]
  have hsub : ((Fintype.card V - r : ℕ) : ℝ)
      = (Fintype.card V : ℝ) - (r : ℝ) := by
    rw [Nat.cast_sub hr]
  have hNR : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast hV.ne'
  rw [hsub]
  field_simp
  ring

/-- The expected size of the intersection of `A` with a uniform `r`-element subset is `A.card *
r / Fintype.card V`. -/
theorem uniformSubset_expect_card_inter {V : Type*} [Fintype V] [DecidableEq V]
    (A : Finset V) (r : ℕ) (hr : r ≤ Fintype.card V) (hV : 0 < Fintype.card V) :
    (uniformSubset (V := V) r hr).expect (fun R => ((A ∩ R).card : ℝ))
      = (A.card : ℝ) * (r : ℝ) / (Fintype.card V : ℝ) := by
  classical
  have hcard : ∀ R : Finset V,
      ((A ∩ R).card : ℝ) = ∑ i ∈ A, (if i ∈ R then (1 : ℝ) else 0) := by
    intro R
    have hset : A ∩ R = A.filter (fun i => i ∈ R) := by
      ext i; simp
    rw [hset, Finset.card_eq_sum_ones]
    push_cast
    rw [Finset.sum_filter]
  rw [FinDist.expect]
  calc (∑ R : Finset V, (uniformSubset (V := V) r hr).prob R * ((A ∩ R).card : ℝ))
      = ∑ R : Finset V, (uniformSubset (V := V) r hr).prob R
          * ∑ i ∈ A, (if i ∈ R then (1 : ℝ) else 0) :=
        Finset.sum_congr rfl (fun R _ => by rw [hcard R])
    _ = ∑ i ∈ A, ∑ R : Finset V, (uniformSubset (V := V) r hr).prob R
          * (if i ∈ R then (1 : ℝ) else 0) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
    _ = ∑ i ∈ A, (r : ℝ) / (Fintype.card V : ℝ) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [← eventMass_ite]
        exact uniformSubset_mem_mass r hr hV i
    _ = (A.card : ℝ) * (r : ℝ) / (Fintype.card V : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring

/-- The columns containing a position of `W` whose row belongs to `R`. -/
def hitCols {Row Col : Type*} [DecidableEq Row] [DecidableEq Col]
    (W : Finset (Row × Col)) (R : Finset Row) : Finset Col :=
  (W.filter (fun c => c.1 ∈ R)).image (fun c => c.2)

/-- A window `R × S` meets `W` exactly when `S` meets the columns reached from `R`. -/
theorem not_disjoint_windowCells_iff {Row Col : Type*} [DecidableEq Row]
    [DecidableEq Col] (W : Finset (Row × Col)) (R : Finset Row) (S : Finset Col) :
    ¬ Disjoint W (windowCells (R, S)) ↔ ¬ Disjoint S (hitCols W R) := by
  classical
  rw [Finset.not_disjoint_iff, Finset.not_disjoint_iff]
  constructor
  · rintro ⟨p, hpW, hpRS⟩
    obtain ⟨hpR, hpS⟩ := Finset.mem_product.mp hpRS
    exact ⟨p.2, hpS, Finset.mem_image.mpr
      ⟨p, Finset.mem_filter.mpr ⟨hpW, hpR⟩, rfl⟩⟩
  · rintro ⟨j, hjS, hj⟩
    obtain ⟨c, hc, hc2⟩ := Finset.mem_image.mp hj
    obtain ⟨hcW, hcR⟩ := Finset.mem_filter.mp hc
    refine ⟨c, hcW, ?_⟩
    rw [windowCells, Finset.mem_product]
    exact ⟨hcR, by rw [hc2]; exact hjS⟩

/-- For an independent error set, the number of columns reached from `R` equals the number of
nonempty rows of `W` in `R`. See [BuhrmanSpalek2006]. -/
theorem hitCols_card {Row Col : Type*} [Fintype Row] [DecidableEq Row]
    [DecidableEq Col] (W : Finset (Row × Col)) (R : Finset Row)
    (hind : IsIndependent W) :
    (hitCols W R).card = (nzRows W ∩ R).card := by
  classical
  have hsndInj : Set.InjOn (fun c : Row × Col => c.2) ↑(W.filter (fun c => c.1 ∈ R)) := by
    intro a ha b hb h
    simp only [Finset.mem_coe, Finset.mem_filter] at ha hb
    rcases a with ⟨ia, ja⟩
    rcases b with ⟨ib, jb⟩
    simp only at h
    have hcolA : ia ∈ colRows W ja := (mem_colRows W ia ja).mpr ha.1
    have hcolB : ib ∈ colRows W ja := by
      rw [h]
      exact (mem_colRows W ib jb).mpr hb.1
    have hi : ia = ib := Finset.card_le_one.mp (hind.2 ja) ia hcolA ib hcolB
    exact Prod.ext hi h
  have hfstInj : Set.InjOn (fun c : Row × Col => c.1) ↑(W.filter (fun c => c.1 ∈ R)) := by
    intro a ha b hb h
    simp only [Finset.mem_coe, Finset.mem_filter] at ha hb
    rcases a with ⟨ia, ja⟩
    rcases b with ⟨ib, jb⟩
    simp only at h
    have hcolA : ja ∈ rowCols W ia := (mem_rowCols W ia ja).mpr ha.1
    have hcolB : jb ∈ rowCols W ia := by
      rw [h]
      exact (mem_rowCols W ib jb).mpr hb.1
    have hj : ja = jb := Finset.card_le_one.mp (hind.1 ia) ja hcolA jb hcolB
    exact Prod.ext h hj
  have himg : (W.filter (fun c => c.1 ∈ R)).image (fun c : Row × Col => c.1) = nzRows W ∩ R := by
    ext i
    constructor
    · intro hi
      obtain ⟨c, hc, hci⟩ := Finset.mem_image.mp hi
      obtain ⟨hcW, hcR⟩ := Finset.mem_filter.mp hc
      rw [hci] at hcR
      refine Finset.mem_inter.mpr ⟨?_, hcR⟩
      rw [nzRows, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, ⟨c.2, by
        rw [mem_rowCols, ← hci]
        exact hcW⟩⟩
    · intro hi
      obtain ⟨hne, hR⟩ := Finset.mem_inter.mp hi
      rw [nzRows, Finset.mem_filter] at hne
      obtain ⟨j, hj⟩ := hne.2
      exact Finset.mem_image.mpr
        ⟨(i, j), Finset.mem_filter.mpr ⟨(mem_rowCols W i j).mp hj, hR⟩, rfl⟩
  rw [hitCols, Finset.card_image_of_injOn hsndInj]
  rw [← himg, Finset.card_image_of_injOn hfstInj]

/-- A subset with nonzero probability under `uniformSubset r hr` has cardinality `r`. -/
theorem uniformSubset_prob_ne_zero_card {V : Type*} [Fintype V] [DecidableEq V]
    (r : ℕ) (hr : r ≤ Fintype.card V) {R : Finset V}
    (h : (uniformSubset (V := V) r hr).prob R ≠ 0) : R.card = r := by
  classical
  simp only [uniformSubset, uniformOn] at h
  by_cases hmem : R ∈ (Finset.univ : Finset V).powersetCard r
  · exact (Finset.mem_powersetCard.mp hmem).2
  · rw [if_neg hmem] at h
    exact absurd rfl h

/-- Computes a uniform window event by first averaging over the sampled rows and then over the
sampled columns. See [BuhrmanSpalek2006]. -/
theorem eventMass_window_eq_rowFirst {Row Col : Type*} [Fintype Row] [DecidableEq Row]
    [Fintype Col] [DecidableEq Col] (r s : ℕ) (hr : r ≤ Fintype.card Row)
    (hs : s ≤ Fintype.card Col) (P : Finset Row → Finset Col → Prop)
    [DecidableRel P] :
    eventMass (uniformWindow r s hr hs) (fun RS => P RS.1 RS.2)
      = ∑ R, (uniformSubset (V := Row) r hr).prob R *
          eventMass (uniformSubset (V := Col) s hs) (fun S => P R S) := by
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
  refine Finset.sum_congr rfl (fun R _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  ring

/-- For independent `W`, the expected number of columns reached by a uniform `r`-element row
subset is `W.card * r / Fintype.card Row`. See [BuhrmanSpalek2006]. -/
theorem hitCols_expect {Row Col : Type*} [Fintype Row] [DecidableEq Row]
    [DecidableEq Col] (W : Finset (Row × Col)) (r : ℕ)
    (hr : r ≤ Fintype.card Row) (hRow : 0 < Fintype.card Row)
    (hind : IsIndependent W) :
    (∑ R, (uniformSubset (V := Row) r hr).prob R * ((hitCols W R).card : ℝ))
      = (W.card : ℝ) * (r : ℝ) / (Fintype.card Row : ℝ) := by
  classical
  have h1 : ∀ R, ((hitCols W R).card : ℝ) = ((nzRows W ∩ R).card : ℝ) := by
    intro R
    rw [hitCols_card W R hind]
  simp only [h1]
  rw [← FinDist.expect]
  rw [uniformSubset_expect_card_inter (nzRows W) r hr hRow]
  rw [← card_eq_nzRows_card W hind.1]

/-- For independent `W` and `s * r ≤ Fintype.card Col`, a uniform `r` by `s` window meets `W`
with probability at least `W.card * r * s / (2 * Fintype.card Row * Fintype.card Col)`. See
[BuhrmanSpalek2006]. -/
theorem lemma10_bound {Row Col : Type*} [Fintype Row] [DecidableEq Row]
    [Fintype Col] [DecidableEq Col] (W : Finset (Row × Col)) (r s : ℕ)
    (hRow : 0 < Fintype.card Row) (hCol : 0 < Fintype.card Col)
    (hr : r ≤ Fintype.card Row) (hs : s ≤ Fintype.card Col)
    (hind : IsIndependent W)
    (hsmall : (s : ℝ) * (r : ℝ) ≤ (Fintype.card Col : ℝ)) :
    (1 / 2) * (W.card : ℝ) * (r : ℝ) * (s : ℝ)
        / ((Fintype.card Row : ℝ) * (Fintype.card Col : ℝ))
      ≤ eventMass (uniformWindow r s hr hs)
          (fun RS => ¬ Disjoint W (windowCells RS)) := by
  classical
  have hnR : (Fintype.card Row : ℝ) ≠ 0 := by exact_mod_cast hRow.ne'
  have hnC : (Fintype.card Col : ℝ) ≠ 0 := by exact_mod_cast hCol.ne'

  have hperR : ∀ R : Finset Row,
      (uniformSubset (V := Row) r hr).prob R
          * ((1 / 2) * (s : ℝ) * ((hitCols W R).card : ℝ) / (Fintype.card Col : ℝ))
        ≤ (uniformSubset (V := Row) r hr).prob R
          * eventMass (uniformSubset (V := Col) s hs)
              (fun S => ¬ Disjoint W (windowCells (R, S))) := by
    intro R
    by_cases h0 : (uniformSubset (V := Row) r hr).prob R = 0
    · rw [h0, zero_mul, zero_mul]
    · have hRcard : R.card = r := uniformSubset_prob_ne_zero_card r hr h0
      have hBle : (hitCols W R).card ≤ r := by
        rw [hitCols_card W R hind]
        have hle : (nzRows W ∩ R).card ≤ R.card :=
          Finset.card_le_card Finset.inter_subset_right
        omega
      have hBcard : (hitCols W R).card ≤ Fintype.card Col := Finset.card_le_univ _
      have hsmallR : (s : ℝ) * ((hitCols W R).card : ℝ) ≤ (Fintype.card Col : ℝ) := by
        have h1 : ((hitCols W R).card : ℝ) ≤ (r : ℝ) := by exact_mod_cast hBle
        have h2 : (s : ℝ) * ((hitCols W R).card : ℝ) ≤ (s : ℝ) * (r : ℝ) :=
          mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg s)
        linarith
      have hfit := fixed_window_hit s hs (hitCols W R) hBcard hCol hsmallR
      have hev : eventMass (uniformSubset (V := Col) s hs)
            (fun S => ¬ Disjoint S (hitCols W R))
          = eventMass (uniformSubset (V := Col) s hs)
            (fun S => ¬ Disjoint W (windowCells (R, S))) := by
        refine eventMass_congr' _ (fun S => ?_)
        exact (not_disjoint_windowCells_iff W R S).symm
      rw [← hev]
      exact mul_le_mul_of_nonneg_left hfit ((uniformSubset (V := Row) r hr).nonneg R)
  rw [eventMass_window_eq_rowFirst r s hr hs
    (fun R S => ¬ Disjoint W (windowCells (R, S)))]
  calc (1 / 2) * (W.card : ℝ) * (r : ℝ) * (s : ℝ)
        / ((Fintype.card Row : ℝ) * (Fintype.card Col : ℝ))
      = (1 / 2) * (s : ℝ) / (Fintype.card Col : ℝ)
          * ((W.card : ℝ) * (r : ℝ) / (Fintype.card Row : ℝ)) := by
        field_simp
    _ = (1 / 2) * (s : ℝ) / (Fintype.card Col : ℝ)
          * ∑ R, (uniformSubset (V := Row) r hr).prob R
              * ((hitCols W R).card : ℝ) := by
        rw [hitCols_expect W r hr hRow hind]
    _ = ∑ R, (uniformSubset (V := Row) r hr).prob R
          * ((1 / 2) * (s : ℝ) * ((hitCols W R).card : ℝ)
              / (Fintype.card Col : ℝ)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun R _ => ?_)
        ring
    _ ≤ ∑ R, (uniformSubset (V := Row) r hr).prob R
          * eventMass (uniformSubset (V := Col) s hs)
              (fun S => ¬ Disjoint W (windowCells (R, S))) :=
        Finset.sum_le_sum (fun R _ => hperR R)

end Qatlib.Papers.MatProdVerify04.MainResults
