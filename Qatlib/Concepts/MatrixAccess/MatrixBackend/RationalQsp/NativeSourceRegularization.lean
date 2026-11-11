/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourceBitPrecision
import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourceComplementSquare
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Base.NativeRootCoordinateTruncation
import Mathlib.Data.Nat.Dist
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Public
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Verifier
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeHouseholder
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativePhasePrecision

set_option backward.isDefEq.respectTransparency false

/-! Original-input CFD source bridge: Regularization.
The nonconstant branch uses the computed surviving degree.
This module does not certify spectral completion, deflation, interpreter refinement or fees. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords


open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data

/-- Construction for source Coefficient in the native source regularization model. -/
def sourceCoefficient (cs : List ℚ) (N : ℕ) (E : ℚ) (j : Fin (N+1)) : ℚ :=
  let u := sourceInputU cs N E
  rootGridTruncate ((1-u/8)*cs.getD j.val 0/(if j.val=0 then 1 else 2)) (sourceGrid N u)

/-- The finite construction in `NativeSourceRegularization` satisfies `sourceCoefficient_zero` under the displayed hypotheses. -/
theorem sourceCoefficient_zero (cs : List ℚ) (N : ℕ) (E : ℚ) (j : Fin (N+1))
    (hj : cs.getD j.val 0=0) : sourceCoefficient cs N E j=0 := by
  simp only [sourceCoefficient,hj,mul_zero,zero_div]
  simp [rootGridTruncate]

/-- Construction for degree Fold in the native source regularization model. -/
private def degreeFold {N : ℕ} (a : Fin (N+1) → ℚ) (l : List (Fin (N+1))) (s : ℕ) : ℕ :=
  l.foldl (fun D i => if a i=0 then D else max D i.val) s

/-- Construction for source Array Degree in the native source regularization model. -/
def sourceArrayDegree {N : ℕ} (a : Fin (N+1) → ℚ) : ℕ := degreeFold a (List.finRange (N+1)) 0

/-- Construction for source Degree in the native source regularization model. -/
def sourceDegree (cs : List ℚ) (N : ℕ) (E : ℚ) : ℕ := sourceArrayDegree (sourceCoefficient cs N E)

/-- The estimate `degreeFold_bound` retains the actual parameter, input-error and normalization budgets. -/
private theorem degreeFold_bound {N : ℕ} (a : Fin (N+1) → ℚ)
    (l : List (Fin (N+1))) (s : ℕ) (hs : s ≤ N) : degreeFold a l s ≤ N := by
  unfold degreeFold
  induction l generalizing s with
  | nil => exact hs
  | cons i l ih =>
    rw [List.foldl_cons]
    split_ifs
    · exact ih s hs
    · exact ih (max s i.val) (max_le hs (Nat.le_of_lt_succ i.isLt))

/-- The finite construction in `NativeSourceRegularization` satisfies `degreeFold_ge_seed` under the displayed hypotheses. -/
private theorem degreeFold_ge_seed {N : ℕ} (a : Fin (N+1) → ℚ)
    (l : List (Fin (N+1))) (s : ℕ) : s ≤ degreeFold a l s := by
  unfold degreeFold
  induction l generalizing s with
  | nil => exact le_rfl
  | cons i l ih =>
    rw [List.foldl_cons]
    split_ifs
    · exact ih s
    · exact (Nat.le_max_left s i.val).trans (ih (max s i.val))

/-- The finite construction in `NativeSourceRegularization` satisfies `degreeFold_mem_or_seed` under the displayed hypotheses. -/
private theorem degreeFold_mem_or_seed {N : ℕ} (a : Fin (N+1) → ℚ)
    (l : List (Fin (N+1))) (s : ℕ) :
    degreeFold a l s=s ∨ ∃ i∈l,a i≠0 ∧ degreeFold a l s=i.val := by
  unfold degreeFold
  induction l generalizing s with
  | nil => exact Or.inl rfl
  | cons i l ih =>
    rw [List.foldl_cons]
    by_cases hi : a i=0
    · simp only [ite_eq_left hi]
      rcases ih s with he|⟨j,hj,hn,hv⟩
      · exact Or.inl he
      · exact Or.inr ⟨j,List.mem_cons_of_mem i hj,hn,hv⟩
    · simp only [ite_eq_right hi]
      rcases ih (max s i.val) with he|⟨j,hj,hn,hv⟩
      · by_cases hs : s ≤ i.val
        · exact Or.inr ⟨i,by simp,hi,by simpa only [max_eq_right hs] using he⟩
        · exact Or.inl (by simpa only [max_eq_left (le_of_not_ge hs)] using he)
      · exact Or.inr ⟨j,List.mem_cons_of_mem i hj,hn,hv⟩

/-- The finite construction in `NativeSourceRegularization` satisfies `degreeFold_ge_mem` under the displayed hypotheses. -/
private theorem degreeFold_ge_mem {N : ℕ} (a : Fin (N+1) → ℚ)
    (l : List (Fin (N+1))) (s : ℕ) (i : Fin (N+1)) (hi : i∈l) (hn : a i≠0) :
    i.val ≤ degreeFold a l s := by
  unfold degreeFold
  induction l generalizing s with
  | nil => cases hi
  | cons j l ih =>
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hi with he|he
    · subst i
      rw [ite_eq_right hn]
      exact (Nat.le_max_right s j.val).trans (degreeFold_ge_seed a l (max s j.val))
    · by_cases hz : a j=0
      · rw [ite_eq_left hz]
        exact ih s he
      · rw [ite_eq_right hz]
        exact ih (max s j.val) he

/-- The finite construction in `NativeSourceRegularization` satisfies `sourceArrayDegree_le` under the displayed hypotheses. -/
theorem sourceArrayDegree_le {N : ℕ} (a : Fin (N+1) → ℚ) : sourceArrayDegree a ≤ N :=
  degreeFold_bound a _ 0 (Nat.zero_le N)

/-- The finite construction in `NativeSourceRegularization` satisfies `sourceArrayDegree_leading` under the displayed hypotheses. -/
theorem sourceArrayDegree_leading {N : ℕ} (a : Fin (N+1) → ℚ) (hd : 0<sourceArrayDegree a) :
    ∃ i : Fin (N+1),a i≠0 ∧ sourceArrayDegree a=i.val := by
  rcases degreeFold_mem_or_seed a (List.finRange (N+1)) 0 with he|⟨i,_,hi,hv⟩
  · exact False.elim ((Nat.ne_of_gt hd) he)
  · exact ⟨i,hi,hv⟩

/-- The finite construction in `NativeSourceRegularization` satisfies `sourceArrayDegree_tail_zero` under the displayed hypotheses. -/
theorem sourceArrayDegree_tail_zero {N : ℕ} (a : Fin (N+1) → ℚ)
    (i : Fin (N+1)) (hi : sourceArrayDegree a < i.val) : a i=0 := by
  by_contra hn
  have h := degreeFold_ge_mem a (List.finRange (N+1)) 0 i (by simp) hn
  exact (not_le_of_gt hi) h

/-- The finite construction in `NativeSourceRegularization` satisfies `sourceDegree_le` under the displayed hypotheses. -/
theorem sourceDegree_le (cs : List ℚ) (N : ℕ) (E : ℚ) : sourceDegree cs N E ≤ N :=
  sourceArrayDegree_le _

/-- The surviving degree has original parity from the actual raw check. -/
theorem sourceDegree_parity (cs : List ℚ) (N : ℕ) (E : ℚ)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E) : sourceDegree cs N E%2=N%2 := by
  obtain ⟨j,hj,he⟩ := sourceArrayDegree_leading (sourceCoefficient cs N E) hd
  have hm : j.val%2=N%2 := by
    by_contra hn
    exact hj (sourceCoefficient_zero cs N E j (hparity j hn))
  rw [show sourceDegree cs N E=j.val from he]
  exact hm

/-- Construction for lifted Index in the native source regularization model. -/
private def liftedIndex (N d : ℕ) (hd : d ≤ N) (i : Fin (d+d+1)) : Fin (N+1) :=
  ⟨Nat.dist i.val d,by
    have hi := i.isLt
    simp only [Nat.dist]
    omega⟩

/-- Construction for source Lifted Array in the native source regularization model. -/
def sourceLiftedArray (cs : List ℚ) (N : ℕ) (E : ℚ) :
    Fin (sourceDegree cs N E+sourceDegree cs N E+1) → ℚ :=
  fun i => sourceCoefficient cs N E
    (liftedIndex N (sourceDegree cs N E) (sourceDegree_le cs N E) i)

/-- Parity-zero premise of the square theorem is now derived from raw input,
computed regularization and its ACTUAL surviving degree. -/
theorem sourceLiftedArray_odd_zero (cs : List ℚ) (N : ℕ) (E : ℚ)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E) :
    ∀ i,Odd i.val → sourceLiftedArray cs N E i=0 := by
  intro i hi
  have hm := sourceDegree_parity cs N E hparity hd
  unfold sourceLiftedArray
  apply sourceCoefficient_zero
  apply hparity
  dsimp only [liftedIndex]
  obtain ⟨k,hk⟩ := hi
  by_cases hle : i.val ≤ sourceDegree cs N E
  · rw [Nat.dist_eq_sub_of_le hle]
    omega
  · rw [Nat.dist_eq_sub_of_le_right (le_of_not_ge hle)]
    omega

/-- The rational source complement from original cs/N/E has the ordinary
square identity. No parity-zero array or alternate H identity is supplied. -/
theorem sourceOriginalComplement_polynomial (cs : List ℚ) (N : ℕ) (E : ℚ)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E) :
    let d := sourceDegree cs N E
    Polynomial.ofFn (d+d+1) (sourceComplementCell (sourceLiftedArray cs N E))=
      Polynomial.X^d-(Polynomial.ofFn (d+1) (sourceP (sourceLiftedArray cs N E)))^2 :=
  sourceComplement_polynomial _ (sourceLiftedArray_odd_zero cs N E hparity hd)

end Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
