/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.CBMDCompat

import Mathlib.Data.Fintype.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith

/-!
# Finite partitions and interval induction

Constructs an open interval avoiding a finite family of real points and proves
`Icc_induction_of_disjoint_Ioo`. The induction principle reduces an interval property to pieces
avoiding a finite set and a gluing rule.

These finite-partition tools support piecewise contour arguments associated with [WangEtAl2026].

## Main statements

* `exists_Ioo_disjoint_range_of_finite`: A finite family of real numbers is disjoint from some
  nonempty open interval.
* `Icc_induction_of_disjoint_Ioo`: Proves a property of a closed interval by establishing it on
  subintervals whose interiors avoid a fixed finite set and gluing across intermediate points.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Residue

section

open Set

namespace TauCeti

/-- A finite family of real numbers is disjoint from some nonempty open interval. -/
theorem exists_Ioo_disjoint_range_of_finite {ι : Type*} [Finite ι] (a : ι → ℝ) :
    ∃ p q x : ℝ, (∀ i, a i ∉ Ioo p q) ∧ x ∈ Ioo p q := by
  obtain ⟨S, hbound⟩ := Finite.exists_le a
  let p := S + 1
  let x := p + 1
  let q := p + 2
  have ha : ∀ i, a i ∉ Ioo p q := by
    intro i hi
    have := hbound i
    dsimp [p] at hi
    exact (not_lt.mpr (by linarith : a i ≤ S + 1)) hi.1
  have hx : x ∈ Ioo p q := by dsimp [x, q]; constructor <;> linarith
  exact ⟨p, q, x, ha, hx⟩

/-- Proves a property of a closed interval by establishing it on subintervals whose interiors
avoid a fixed finite set and gluing across intermediate points. -/
theorem Icc_induction_of_disjoint_Ioo {α : Type*} [LinearOrder α] {p : Finset α} {s : Set α}
    {Q : α → α → Prop}
    (hbase : ∀ c d : α, c ≤ d → Icc c d ⊆ s → Disjoint (↑p : Set α) (Ioo c d) → Q c d)
    (hglue : ∀ c m d : α, c ≤ m → m ≤ d → Q c m → Q m d → Q c d) {c d : α} (hcd : c ≤ d)
    (hs : Icc c d ⊆ s) : Q c d := by
  have hdisj : ∀ {c d : α}, p.filter (· ∈ Ioo c d) = ∅ → Disjoint (↑p : Set α) (Ioo c d) :=
    fun he => disjoint_left.mpr fun _ hxp hx => Finset.filter_eq_empty_iff.mp he hxp hx

  suffices h : ∀ n, ∀ c d : α, (p.filter (· ∈ Ioo c d)).card ≤ n → c ≤ d → Icc c d ⊆ s →
      Q c d from h _ c d le_rfl hcd hs
  intro n
  induction n with
  | zero =>
    intro c d hcard hcd hs
    exact hbase c d hcd hs (hdisj (Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)))
  | succ n ih =>
    intro c d hcard hcd hs
    rcases (p.filter (· ∈ Ioo c d)).eq_empty_or_nonempty with he | hne
    · exact hbase c d hcd hs (hdisj he)

    set m := (p.filter (· ∈ Ioo c d)).max' hne
    obtain ⟨hmp, hm⟩ := Finset.mem_filter.mp ((p.filter (· ∈ Ioo c d)).max'_mem hne)
    have hssub : p.filter (· ∈ Ioo c m) ⊂ p.filter (· ∈ Ioo c d) :=
      (Finset.ssubset_iff_of_subset (Finset.monotone_filter_right _ fun x _ hx =>
          ⟨hx.1, hx.2.trans hm.2⟩)).mpr
        ⟨m, Finset.mem_filter.mpr ⟨hmp, hm⟩, fun hmem =>
          (Finset.mem_filter.mp hmem).2.2.false⟩
    have h₁ : Q c m :=
      ih c m (Nat.le_of_lt_succ ((Finset.card_lt_card hssub).trans_le hcard)) hm.1.le
        ((Icc_subset_Icc le_rfl hm.2.le).trans hs)
    have h₂ : Q m d :=
      hbase m d hm.2.le ((Icc_subset_Icc hm.1.le le_rfl).trans hs) <|
        disjoint_left.mpr fun x hxp hx => ((p.filter (· ∈ Ioo c d)).le_max' x
          (Finset.mem_filter.mpr ⟨hxp, hm.1.trans hx.1, hx.2⟩)).not_gt hx.1
    exact hglue c m d hm.1.le hm.2.le h₁ h₂

end TauCeti

end
end Qatlib.Foundations.CbmdAnalysis.Residue
