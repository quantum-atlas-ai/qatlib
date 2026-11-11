/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.MomentSdp.GramFactor
import Mathlib.Data.Sym.Card
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Counting moment labels and symmetric variables

This module describes the independent coordinates of a real symmetric matrix using `Sym2`. It
counts the X/Y completion variables and the identity, one-site, and two-site Pauli labels of
`LevelTwoLabel`, then bounds their symmetric moment-variable counts by explicit quadratic and
quartic polynomials.

These results support the development of [CrostaSaubanereHuber2026].

## Main statements

* `completion_card`: gives the exact count `2*n^2 + n`.
* `levelTwo_card`: counts the full operator labels.
* `fullVariable_quartic`: supplies an explicit quartic upper bound.

## References

* [Crosta et al., 2026][CrostaSaubanereHuber2026]
-/

set_option warningAsError false
set_option autoImplicit false
open scoped Classical
namespace Qatlib.Papers.RydbergMaxCut26.Resources.Counts
open Qatlib.Papers.RydbergMaxCut26.MomentSdp.Gram

/-- The unordered pairs, including repeated indices, of the X/Y moment index type, indexing
independent symmetric completion entries. -/
abbrev CompletionVariable (n : ℕ) := Sym2 (MomentIndex n)

/-- The equivalence between symmetric real matrices on `I` and real-valued functions on
unordered pairs `Sym2 I`. -/
def symmetricCoordinates (I : Type*) :
    {A : Matrix I I ℝ // ∀ i j,A i j=A j i} ≃ (Sym2 I → ℝ) := Sym2.lift

/-- The vertex-axis moment index type has cardinality `2*n`. -/
theorem moment_slots (n : ℕ) : Fintype.card (MomentIndex n)=2*n := by
  simp only [MomentIndex,Fintype.card_prod,Fintype.card_fin]
  omega

/-- The real symmetric X/Y completion has exactly `2*n^2 + n` coordinate slots before
constraints, giving the variable count used in [CrostaSaubanereHuber2026]. -/
theorem completion_card (n : ℕ) : Fintype.card (CompletionVariable n)=2*n^2+n := by
  change Fintype.card (Sym2 (MomentIndex n))=_
  rw [Sym2.card,moment_slots,Nat.choose_two_right]
  simp only [Nat.add_sub_cancel]
  have he : (2*n+1)*(2*n)=2*(2*n^2+n) := by ring
  rw [he,Nat.mul_div_right]
  norm_num

/-- The type of unordered pairs of distinct sites in `Fin n`. -/
abbrev SitePair (n : ℕ) := {s : Sym2 (Fin n) // ¬s.IsDiag}

/-- The type of unordered distinct-site pairs equipped with a choice of one of three Pauli axes
at each endpoint. -/
abbrev DoubleLabel (n : ℕ) := Σ s : SitePair n, (s.1.toFinset → Fin 3)

/-- The disjoint union of the identity label, single-site Pauli labels, and two-site Pauli
labels. -/
abbrev LevelTwoLabel (n : ℕ) := PUnit ⊕ ((Fin n×Fin 3) ⊕ DoubleLabel n)

/-- The number of unordered distinct-site pairs is `n.choose 2`. -/
theorem sitePair_card (n : ℕ) : Fintype.card (SitePair n)=n.choose 2 := by
  simpa only [SitePair,Fintype.card_fin] using (Sym2.card_subtype_not_diag (α:=Fin n))

/-- A fixed distinct-site pair has exactly nine assignments of Pauli axes to its two endpoints. -/
theorem pair_axis_card {n : ℕ} (s : SitePair n) : Fintype.card (s.1.toFinset → Fin 3)=9 := by
  rw [Fintype.card_fun,Fintype.card_fin,Fintype.card_coe,Sym2.card_toFinset_of_not_isDiag _ s.2]
  norm_num

/-- The number of two-site Pauli labels is `9 * n.choose 2`. -/
theorem doubleLabel_card (n : ℕ) : Fintype.card (DoubleLabel n)=9*n.choose 2 := by
  change Fintype.card (Σ s : SitePair n, (s.1.toFinset → Fin 3))=_
  rw [Fintype.card_sigma]
  simp only [pair_axis_card,Finset.sum_const,Finset.card_univ,smul_eq_mul,sitePair_card]
  omega

/-- The number of identity, single-site, and two-site Pauli labels is `1 + 3*n + 9*n.choose 2`. -/
theorem levelTwo_card (n : ℕ) : Fintype.card (LevelTwoLabel n)=1+3*n+9*n.choose 2 := by
  simp only [LevelTwoLabel,Fintype.card_sum,Fintype.card_punit,Fintype.card_prod,
    Fintype.card_fin,doubleLabel_card]
  omega

/-- The sitewise Pauli word associated with an identity, single-site, or two-site label, using
`none` for identity factors. -/
noncomputable def labelWord {n : ℕ} : LevelTwoLabel n → Fin n → Option (Fin 3)
  | Sum.inl _,_ => none
  | Sum.inr (Sum.inl (i,a)),h => if h=i then some a else none
  | Sum.inr (Sum.inr ⟨s,f⟩),h => if hh : h∈s.1.toFinset then some (f ⟨h,hh⟩) else none

/-- The unordered pairs, including repeated labels, of the full level-two label type, indexing
independent symmetric moment entries. -/
abbrev FullVariable (n : ℕ) := Sym2 (LevelTwoLabel n)

/-- The full symmetric moment matrix has `(1 + 3*n + 9*n.choose 2 + 1).choose 2` independent
coordinate slots. -/
theorem fullVariable_card (n : ℕ) :
    Fintype.card (FullVariable n)=(1+3*n+9*n.choose 2+1).choose 2 := by
  change Fintype.card (Sym2 (LevelTwoLabel n))=_
  rw [Sym2.card,levelTwo_card]

/-- The number of completion variables is at most `3*(n+1)^2`. -/
theorem completion_quadratic (n : ℕ) : Fintype.card (CompletionVariable n) ≤ 3*(n+1)^2 := by
  rw [completion_card]
  nlinarith

/-- The number of full level-two Pauli labels is at most `13*(n+1)^2`. -/
theorem levelTwo_quadratic (n : ℕ) : Fintype.card (LevelTwoLabel n) ≤ 13*(n+1)^2 := by
  rw [levelTwo_card]
  have h := Nat.choose_le_pow n 2
  nlinarith

/-- The number of full symmetric moment variables is at most `196*(n+1)^4`, providing the
quartic variable bound compared with the quadratic completion in [CrostaSaubanereHuber2026]. -/
theorem fullVariable_quartic (n : ℕ) : Fintype.card (FullVariable n) ≤ 196*(n+1)^4 := by
  change Fintype.card (Sym2 (LevelTwoLabel n)) ≤ _
  rw [Sym2.card]
  have h := levelTwo_quadratic n
  have hpos : 1 ≤ (n+1)^2 := by
    have hpow : 0 < (n+1)^2 := pow_pos (Nat.succ_pos n) 2
    omega
  have hplus : Fintype.card (LevelTwoLabel n)+1 ≤ 14*(n+1)^2 := by omega
  calc
    _ ≤ (Fintype.card (LevelTwoLabel n)+1)^2 := Nat.choose_le_pow _ _
    _ ≤ (14*(n+1)^2)^2 := by gcongr
    _ = _ := by ring
end Qatlib.Papers.RydbergMaxCut26.Resources.Counts
