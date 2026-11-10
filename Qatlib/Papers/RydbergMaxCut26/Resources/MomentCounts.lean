/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.MomentSdp.GramFactor
import Mathlib.Data.Sym.Card
import Mathlib.Data.Nat.Choose.Bounds
set_option warningAsError false
set_option autoImplicit false
open scoped Classical
namespace Qatlib.Papers.RydbergMaxCut26.Resources.Counts
open Qatlib.Papers.RydbergMaxCut26.MomentSdp.Gram

abbrev CompletionVariable (n : ℕ) := Sym2 (MomentIndex n)

def symmetricCoordinates (I : Type*) :
    {A : Matrix I I ℝ // ∀ i j,A i j=A j i} ≃ (Sym2 I → ℝ) := Sym2.lift

theorem moment_slots (n : ℕ) : Fintype.card (MomentIndex n)=2*n := by
  simp only [MomentIndex,Fintype.card_prod,Fintype.card_fin]
  omega

theorem completion_card (n : ℕ) : Fintype.card (CompletionVariable n)=2*n^2+n := by
  change Fintype.card (Sym2 (MomentIndex n))=_
  rw [Sym2.card,moment_slots,Nat.choose_two_right]
  simp only [Nat.add_sub_cancel]
  have he : (2*n+1)*(2*n)=2*(2*n^2+n) := by ring
  rw [he,Nat.mul_div_right]
  norm_num

abbrev SitePair (n : ℕ) := {s : Sym2 (Fin n) // ¬s.IsDiag}

abbrev DoubleLabel (n : ℕ) := Σ s : SitePair n, (s.1.toFinset → Fin 3)

abbrev LevelTwoLabel (n : ℕ) := PUnit ⊕ ((Fin n×Fin 3) ⊕ DoubleLabel n)

theorem sitePair_card (n : ℕ) : Fintype.card (SitePair n)=n.choose 2 := by
  simpa only [SitePair,Fintype.card_fin] using (Sym2.card_subtype_not_diag (α:=Fin n))

theorem pair_axis_card {n : ℕ} (s : SitePair n) : Fintype.card (s.1.toFinset → Fin 3)=9 := by
  rw [Fintype.card_fun,Fintype.card_fin,Fintype.card_coe,Sym2.card_toFinset_of_not_isDiag _ s.2]
  norm_num

theorem doubleLabel_card (n : ℕ) : Fintype.card (DoubleLabel n)=9*n.choose 2 := by
  change Fintype.card (Σ s : SitePair n, (s.1.toFinset → Fin 3))=_
  rw [Fintype.card_sigma]
  simp only [pair_axis_card,Finset.sum_const,Finset.card_univ,smul_eq_mul,sitePair_card]
  omega

theorem levelTwo_card (n : ℕ) : Fintype.card (LevelTwoLabel n)=1+3*n+9*n.choose 2 := by
  simp only [LevelTwoLabel,Fintype.card_sum,Fintype.card_punit,Fintype.card_prod,
    Fintype.card_fin,doubleLabel_card]
  omega

noncomputable def labelWord {n : ℕ} : LevelTwoLabel n → Fin n → Option (Fin 3)
  | Sum.inl _,_ => none
  | Sum.inr (Sum.inl (i,a)),h => if h=i then some a else none
  | Sum.inr (Sum.inr ⟨s,f⟩),h => if hh : h∈s.1.toFinset then some (f ⟨h,hh⟩) else none

abbrev FullVariable (n : ℕ) := Sym2 (LevelTwoLabel n)

theorem fullVariable_card (n : ℕ) :
    Fintype.card (FullVariable n)=(1+3*n+9*n.choose 2+1).choose 2 := by
  change Fintype.card (Sym2 (LevelTwoLabel n))=_
  rw [Sym2.card,levelTwo_card]

theorem completion_quadratic (n : ℕ) : Fintype.card (CompletionVariable n) ≤ 3*(n+1)^2 := by
  rw [completion_card]
  nlinarith

theorem levelTwo_quadratic (n : ℕ) : Fintype.card (LevelTwoLabel n) ≤ 13*(n+1)^2 := by
  rw [levelTwo_card]
  have h := Nat.choose_le_pow n 2
  nlinarith

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
