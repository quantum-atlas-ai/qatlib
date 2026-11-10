/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.DecisionTrees97.MainResults

open Matrix

variable {L : ℕ}

abbrev Register (L : ℕ) := Fin L → Bool

def diagBit (j : Fin L) : Matrix (Register L) (Register L) ℂ :=
  fun z w => if z = w then (if z j then 1 else 0) else 0

def flipBit (j : Fin L) : Matrix (Register L) (Register L) ℂ :=
  fun z w => if w = Function.update z j (Bool.not (z j)) then 1 else 0

def NoTransitionsOutside (S : Finset (Fin L)) (A : Matrix (Register L) (Register L) ℂ) : Prop :=
  ∀ z w : Register L, (∃ j : Fin L, j ∉ S ∧ z j ≠ w j) → A z w = 0

theorem any_diagonal_has_empty_transition_support (f : Register L → ℂ) :
    NoTransitionsOutside ∅ (Matrix.diagonal f) := by
  intro z w h
  obtain ⟨j, _, hne⟩ := h
  have hzw : z ≠ w := fun he => hne (congrFun he j)
  simp [hzw]

theorem controlled_phase_weak_support_counterexample :
    let f := fun z : Register 2 => if z 0 && z 1 then (-1 : ℂ) else 1
    NoTransitionsOutside ∅ (Matrix.diagonal f) ∧
      Matrix.diagonal f (fun _ => false) (fun _ => false) = 1 ∧
      Matrix.diagonal f (fun _ => true) (fun _ => true) = -1 := by
  dsimp
  exact ⟨any_diagonal_has_empty_transition_support _, by simp, by simp⟩

theorem noTransitionsOutside_diagBit (j : Fin L) :
    NoTransitionsOutside ({j} : Finset (Fin L)) (diagBit j) := by
  intro z w h
  obtain ⟨j', hj', hne⟩ := h
  simp only [Finset.mem_singleton] at hj'
  have hzw : z ≠ w := fun hEq => hne (by rw [hEq])
  simp [diagBit, hzw]

theorem noTransitionsOutside_flipBit (j : Fin L) :
    NoTransitionsOutside ({j} : Finset (Fin L)) (flipBit j) := by
  intro z w h
  obtain ⟨j', hj', hne⟩ := h
  simp only [Finset.mem_singleton] at hj'
  by_cases hw : w = Function.update z j (Bool.not (z j))
  · have hval : w j' = z j' := by
      rw [hw, Function.update_of_ne hj' (Bool.not (z j)) z]
    exact absurd hval.symm hne
  · simp [flipBit, hw]

namespace NoTransitionsOutside

theorem mono {S T : Finset (Fin L)} {A : Matrix (Register L) (Register L) ℂ}
    (hST : S ⊆ T) (hA : NoTransitionsOutside S A) : NoTransitionsOutside T A := by
  intro z w h
  obtain ⟨j, hj, hne⟩ := h
  exact hA z w ⟨j, fun hmem => hj (hST hmem), hne⟩

theorem add {S T : Finset (Fin L)} {A B : Matrix (Register L) (Register L) ℂ}
    (hA : NoTransitionsOutside S A) (hB : NoTransitionsOutside T B) :
    NoTransitionsOutside (S ∪ T) (A + B) := by
  intro z w h
  obtain ⟨j, hj, hne⟩ := h
  have hjS : j ∉ S := fun hm => hj (Finset.mem_union_left T hm)
  have hjT : j ∉ T := fun hm => hj (Finset.mem_union_right S hm)
  rw [Matrix.add_apply, hA z w ⟨j, hjS, hne⟩, hB z w ⟨j, hjT, hne⟩, add_zero]

theorem neg {S : Finset (Fin L)} {A : Matrix (Register L) (Register L) ℂ}
    (hA : NoTransitionsOutside S A) : NoTransitionsOutside S (-A) := by
  intro z w h
  rw [Matrix.neg_apply, hA z w h, neg_zero]

theorem sub {S T : Finset (Fin L)} {A B : Matrix (Register L) (Register L) ℂ}
    (hA : NoTransitionsOutside S A) (hB : NoTransitionsOutside T B) :
    NoTransitionsOutside (S ∪ T) (A - B) := by
  rw [sub_eq_add_neg]
  exact hA.add hB.neg

theorem smul {S : Finset (Fin L)} {A : Matrix (Register L) (Register L) ℂ} (c : ℂ)
    (hA : NoTransitionsOutside S A) : NoTransitionsOutside S (c • A) := by
  intro z w h
  rw [Matrix.smul_apply, hA z w h, smul_zero]

theorem conjTranspose {S : Finset (Fin L)} {A : Matrix (Register L) (Register L) ℂ}
    (hA : NoTransitionsOutside S A) : NoTransitionsOutside S (Aᴴ) := by
  intro z w h
  obtain ⟨j, hj, hne⟩ := h
  rw [Matrix.conjTranspose_apply, hA w z ⟨j, hj, hne.symm⟩, star_zero]

theorem mul {S T : Finset (Fin L)} {A B : Matrix (Register L) (Register L) ℂ}
    (hA : NoTransitionsOutside S A) (hB : NoTransitionsOutside T B) :
    NoTransitionsOutside (S ∪ T) (A * B) := by
  intro z w h
  obtain ⟨j, hj, hne⟩ := h
  have hjS : j ∉ S := fun h' => hj (Finset.mem_union_left T h')
  have hjT : j ∉ T := fun h' => hj (Finset.mem_union_right S h')
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hzk : z j = k j
  · have hkw : k j ≠ w j := fun hkw => hne (hzk.trans hkw)
    rw [hB k w ⟨j, hjT, hkw⟩, mul_zero]
  · rw [hA z k ⟨j, hjS, hzk⟩, zero_mul]

end NoTransitionsOutside

theorem noTransitionsOutside_one :
    NoTransitionsOutside (∅ : Finset (Fin L)) (1 : Matrix (Register L) (Register L) ℂ) := by
  intro z w h
  obtain ⟨j, -, hne⟩ := h
  have hzw : z ≠ w := fun hEq => hne (by rw [hEq])
  simp [hzw]

def yIndex (n : ℕ) (i : Fin (n + 1)) : Fin (2 * n + 1) :=
  ⟨i.val, by omega⟩

def xIndex (n : ℕ) (i : Fin n) : Fin (2 * n + 1) :=
  ⟨n + 1 + i.val, by omega⟩

def yOp (n : ℕ) (i : Fin (n + 1)) : Matrix (Register (2 * n + 1)) (Register (2 * n + 1)) ℂ :=
  diagBit (yIndex n i)

def xOp (n : ℕ) (i : Fin n) : Matrix (Register (2 * n + 1)) (Register (2 * n + 1)) ℂ :=
  diagBit (xIndex n i)

def proposedRhoFlip (n : ℕ) (i : Fin (n + 1)) :
    Matrix (Register (2 * n + 1)) (Register (2 * n + 1)) ℂ :=
  flipBit (yIndex n i)

def proposedSigmaFlip (n : ℕ) (i : Fin n) :
    Matrix (Register (2 * n + 1)) (Register (2 * n + 1)) ℂ :=
  flipBit (xIndex n i)

def diagTerm (n : ℕ) (i : Fin (n + 1)) :
    Matrix (Register (2 * n + 1)) (Register (2 * n + 1)) ℂ :=
  if i = ⟨0, Nat.succ_pos n⟩ then (2 : ℂ) • yOp n i
    else if i = ⟨n, Nat.lt_succ_self n⟩ then yOp n i else (3 : ℂ) • yOp n i

def hopTerm (n : ℕ) (i : Fin n) (b : Fin 4) :
    Matrix (Register (2 * n + 1)) (Register (2 * n + 1)) ℂ :=
  if b = 0 then -((proposedRhoFlip n i.castSucc)ᴴ * proposedRhoFlip n i.succ * (1 - xOp n i))
  else if b = 1 then -(proposedRhoFlip n i.castSucc * (proposedRhoFlip n i.succ)ᴴ * (1 - xOp n i))
  else if b = 2 then -((proposedRhoFlip n i.castSucc)ᴴ * proposedRhoFlip n i.succ * proposedSigmaFlip n i)
  else -(proposedRhoFlip n i.castSucc * (proposedRhoFlip n i.succ)ᴴ * (proposedSigmaFlip n i)ᴴ)

def diagPart (n : ℕ) : Matrix (Register (2 * n + 1)) (Register (2 * n + 1)) ℂ :=
  ∑ i : Fin (n + 1), diagTerm n i

def hopPartZero (n : ℕ) : Matrix (Register (2 * n + 1)) (Register (2 * n + 1)) ℂ :=
  -∑ i : Fin n, ((proposedRhoFlip n i.castSucc)ᴴ * proposedRhoFlip n i.succ * (1 - xOp n i)
    + proposedRhoFlip n i.castSucc * (proposedRhoFlip n i.succ)ᴴ * (1 - xOp n i))

def hopPartOne (n : ℕ) : Matrix (Register (2 * n + 1)) (Register (2 * n + 1)) ℂ :=
  -∑ i : Fin n, ((proposedRhoFlip n i.castSucc)ᴴ * proposedRhoFlip n i.succ * proposedSigmaFlip n i
    + proposedRhoFlip n i.castSucc * (proposedRhoFlip n i.succ)ᴴ * (proposedSigmaFlip n i)ᴴ)

def flipAnsatzHamiltonian (n : ℕ) : Matrix (Register (2 * n + 1)) (Register (2 * n + 1)) ℂ :=
  diagPart n + hopPartZero n + hopPartOne n

abbrev HamIndex (n : ℕ) := Sum (Fin (n + 1)) (Fin n × Fin 4)

def flipAnsatzTerm (n : ℕ) : HamIndex n → Matrix (Register (2 * n + 1)) (Register (2 * n + 1)) ℂ
  | Sum.inl i => diagTerm n i
  | Sum.inr p => hopTerm n p.1 p.2

def hopSupport (n : ℕ) (i : Fin n) : Finset (Fin (2 * n + 1)) :=
  {yIndex n i.castSucc, yIndex n i.succ, xIndex n i}

theorem diagTerm_transition_support (n : ℕ) (i : Fin (n + 1)) :
    ∃ S : Finset (Fin (2 * n + 1)), S.card ≤ 3 ∧ NoTransitionsOutside S (diagTerm n i) := by
  refine ⟨{yIndex n i}, by simp, ?_⟩
  unfold diagTerm
  split_ifs
  · exact (noTransitionsOutside_diagBit (yIndex n i)).smul 2
  · exact noTransitionsOutside_diagBit (yIndex n i)
  · exact (noTransitionsOutside_diagBit (yIndex n i)).smul 3

private theorem subset_hopSupport (n : ℕ) (i : Fin n) :
    ({yIndex n i.castSucc} ∪ {yIndex n i.succ}) ∪ {xIndex n i} ⊆ hopSupport n i := by
  intro x hx
  simp only [hopSupport, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] at hx ⊢
  tauto

private theorem hopSupport_card (n : ℕ) (i : Fin n) : (hopSupport n i).card ≤ 3 := by
  have h := Finset.card_le_three (a := yIndex n i.castSucc) (b := yIndex n i.succ)
    (c := xIndex n i)
  simpa [hopSupport] using h

theorem hopTerm_transition_support (n : ℕ) (i : Fin n) (b : Fin 4) :
    ∃ S : Finset (Fin (2 * n + 1)), S.card ≤ 3 ∧ NoTransitionsOutside S (hopTerm n i b) := by
  have h0 : NoTransitionsOutside (hopSupport n i)
      (-((proposedRhoFlip n i.castSucc)ᴴ * proposedRhoFlip n i.succ * (1 - xOp n i))) := by
    apply NoTransitionsOutside.neg
    apply NoTransitionsOutside.mono (subset_hopSupport n i)
    refine NoTransitionsOutside.mul (NoTransitionsOutside.mul ?_ ?_) ?_
    · exact (noTransitionsOutside_flipBit _).conjTranspose
    · exact noTransitionsOutside_flipBit _
    · exact NoTransitionsOutside.sub noTransitionsOutside_one (noTransitionsOutside_diagBit _)
  have h1 : NoTransitionsOutside (hopSupport n i)
      (-(proposedRhoFlip n i.castSucc * (proposedRhoFlip n i.succ)ᴴ * (1 - xOp n i))) := by
    apply NoTransitionsOutside.neg
    apply NoTransitionsOutside.mono (subset_hopSupport n i)
    refine NoTransitionsOutside.mul (NoTransitionsOutside.mul ?_ ?_) ?_
    · exact noTransitionsOutside_flipBit _
    · exact (noTransitionsOutside_flipBit _).conjTranspose
    · exact NoTransitionsOutside.sub noTransitionsOutside_one (noTransitionsOutside_diagBit _)
  have h2 : NoTransitionsOutside (hopSupport n i)
      (-((proposedRhoFlip n i.castSucc)ᴴ * proposedRhoFlip n i.succ * proposedSigmaFlip n i)) := by
    apply NoTransitionsOutside.neg
    apply NoTransitionsOutside.mono (subset_hopSupport n i)
    refine NoTransitionsOutside.mul (NoTransitionsOutside.mul ?_ ?_) ?_
    · exact (noTransitionsOutside_flipBit _).conjTranspose
    · exact noTransitionsOutside_flipBit _
    · exact noTransitionsOutside_flipBit _
  have h3 : NoTransitionsOutside (hopSupport n i)
      (-(proposedRhoFlip n i.castSucc * (proposedRhoFlip n i.succ)ᴴ * (proposedSigmaFlip n i)ᴴ)) := by
    apply NoTransitionsOutside.neg
    apply NoTransitionsOutside.mono (subset_hopSupport n i)
    refine NoTransitionsOutside.mul (NoTransitionsOutside.mul ?_ ?_) ?_
    · exact noTransitionsOutside_flipBit _
    · exact (noTransitionsOutside_flipBit _).conjTranspose
    · exact (noTransitionsOutside_flipBit _).conjTranspose
  refine ⟨hopSupport n i, hopSupport_card n i, ?_⟩
  unfold hopTerm
  split_ifs with hb0 hb1 hb2
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem flip_ansatz_transition_support (n : ℕ) :
    flipAnsatzHamiltonian n = ∑ k : HamIndex n, flipAnsatzTerm n k ∧
      ∀ k : HamIndex n,
        ∃ S : Finset (Fin (2 * n + 1)), S.card ≤ 3 ∧ NoTransitionsOutside S (flipAnsatzTerm n k) := by
  constructor
  · unfold flipAnsatzHamiltonian diagPart hopPartZero hopPartOne flipAnsatzTerm
    rw [Fintype.sum_sum_type]
    simp only [Fintype.sum_prod_type, Fin.sum_univ_four]
    simp [hopTerm, Finset.sum_add_distrib, Finset.sum_neg_distrib]
    abel
  · rintro (i | ⟨i, b⟩)
    · exact diagTerm_transition_support n i
    · exact hopTerm_transition_support n i b

end Qatlib.Papers.DecisionTrees97.MainResults
