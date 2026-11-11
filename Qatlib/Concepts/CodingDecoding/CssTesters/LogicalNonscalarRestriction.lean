/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CodingDecoding.CssTesters.CssTester
import Qatlib.Concepts.CodingDecoding.CssTesters.CssCode

/-!
# Scalar and nonscalar Pauli actions on CSS codes

This module characterizes Pauli products acting by a scalar on a CSS codespace through
membership of their labels in the X and Z check row spaces. The proof uses the stabilizer sum
and trace identities from the stabilizer framework of [Gottesman1997].

The theorem `logicalNonscalarRestriction` expresses CSS distance using Pauli operators with
nonscalar action. The one-qubit code with no checks also supplies a counterexample to a distance
formula with a differently scoped negation.

## Main statements

* `scalar_action_iff_mem_rowspace`: scalar action is equivalent to membership in both check row
  spaces.
* `logicalNonscalarRestriction`: logical labels and nonscalar action give the same distance
  characterization.
* `frozenDistance_counterexample`: the alternative formula fails for the one-qubit code with no
  checks.

## References

* [Gottesman, 1997][Gottesman1997]
-/

open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode
open Qatlib.Concepts.CodingDecoding.CssTesters.CssTester

open Qatlib.Concepts.CodingDecoding.CssTesters

namespace Qatlib.Concepts.CodingDecoding.CssTesters.LogicalNonscalarRestriction

open Matrix Filter

open scoped Classical BigOperators ENNReal

variable {ι κX κZ : Type*} [Fintype ι] [Fintype κX] [Fintype κZ]
  [DecidableEq ι] [DecidableEq κX] [DecidableEq κZ]

omit [Fintype κX] [Fintype κZ] [DecidableEq κX] [DecidableEq κZ] in

/-- Membership in the CSS codespace is equivalent to being fixed by every X check and every Z
check. -/
theorem mem_cssCodespace_iff (c : CssData ι κX κZ) (w : (ι → ZMod 2) → ℂ) :
    w ∈ cssCodespace c ↔
      (∀ i : κX, cssPauliX (c.hX i) *ᵥ w = w) ∧
      (∀ j : κZ, cssPauliZ (c.hZ j) *ᵥ w = w) := by
  simp [cssCodespace, cssXStabilized, cssZStabilized, cssXCheckKernel, cssZCheckKernel,
    sub_eq_zero]

/-- The X Pauli operator with zero label fixes every vector. -/
theorem cssPauliX_zero_vec (w : (ι → ZMod 2) → ℂ) :
    cssPauliX (0 : ι → ZMod 2) *ᵥ w = w := by
  rw [cssPauliX_zero, one_mulVec]

/-- The Z Pauli operator with zero label fixes every vector. -/
theorem cssPauliZ_zero_vec (w : (ι → ZMod 2) → ℂ) :
    cssPauliZ (0 : ι → ZMod 2) *ᵥ w = w := by
  rw [cssPauliZ_zero, one_mulVec]

/-- If two X Pauli operators fix a vector, the operator with their sum label also fixes it. -/
theorem cssPauliX_add_vec (f g : ι → ZMod 2) (w : (ι → ZMod 2) → ℂ)
    (hf : cssPauliX f *ᵥ w = w) (hg : cssPauliX g *ᵥ w = w) :
    cssPauliX (f + g) *ᵥ w = w := by
  rw [← cssPauliX_mul, ← Matrix.mulVec_mulVec, hg, hf]

/-- If two Z Pauli operators fix a vector, the operator with their sum label also fixes it. -/
theorem cssPauliZ_add_vec (f g : ι → ZMod 2) (w : (ι → ZMod 2) → ℂ)
    (hf : cssPauliZ f *ᵥ w = w) (hg : cssPauliZ g *ᵥ w = w) :
    cssPauliZ (f + g) *ᵥ w = w := by
  rw [← cssPauliZ_mul, ← Matrix.mulVec_mulVec, hg, hf]

/-- A vector fixed by every X Pauli operator in a finite family is fixed by the operator with
the summed label. -/
theorem cssPauliX_sum_vec {κ : Type*} [Fintype κ] (f : κ → ι → ZMod 2)
    (w : (ι → ZMod 2) → ℂ) (hw : ∀ i, cssPauliX (f i) *ᵥ w = w) :
    cssPauliX (∑ i : κ, f i) *ᵥ w = w := by
  classical
  have h : ∀ s : Finset κ, cssPauliX (∑ i ∈ s, f i) *ᵥ w = w := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact cssPauliX_zero_vec w
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, cssPauliX_add_vec _ _ _ (hw i) ih]
  exact h Finset.univ

/-- A vector fixed by every Z Pauli operator in a finite family is fixed by the operator with
the summed label. -/
theorem cssPauliZ_sum_vec {κ : Type*} [Fintype κ] (f : κ → ι → ZMod 2)
    (w : (ι → ZMod 2) → ℂ) (hw : ∀ i, cssPauliZ (f i) *ᵥ w = w) :
    cssPauliZ (∑ i : κ, f i) *ᵥ w = w := by
  classical
  have h : ∀ s : Finset κ, cssPauliZ (∑ i ∈ s, f i) *ᵥ w = w := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact cssPauliZ_zero_vec w
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, cssPauliZ_add_vec _ _ _ (hw i) ih]
  exact h Finset.univ

/-- Multiplication by the transpose of the X check matrix is the corresponding linear
combination of its rows. -/
private theorem rowX_as_sum (c : CssData ι κX κZ) (u : κX → ZMod 2) :
    c.hXᵀ *ᵥ u = ∑ i : κX, u i • c.hX i := by
  funext p
  have h1 : (c.hXᵀ *ᵥ u) p = ∑ x : κX, c.hX x p * u x := by
    simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  have h2 : (∑ i : κX, u i • c.hX i) p = ∑ i : κX, u i * c.hX i p := by
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl fun x _ => by simp [Pi.smul_apply, smul_eq_mul]
  rw [h1, h2]
  exact Finset.sum_congr rfl fun x _ => mul_comm _ _

/-- Multiplication by the transpose of the Z check matrix is the corresponding linear
combination of its rows. -/
private theorem rowZ_as_sum (c : CssData ι κX κZ) (v : κZ → ZMod 2) :
    c.hZᵀ *ᵥ v = ∑ j : κZ, v j • c.hZ j := by
  funext p
  have h1 : (c.hZᵀ *ᵥ v) p = ∑ x : κZ, c.hZ x p * v x := by
    simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  have h2 : (∑ j : κZ, v j • c.hZ j) p = ∑ j : κZ, v j * c.hZ j p := by
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl fun x _ => by simp [Pi.smul_apply, smul_eq_mul]
  rw [h1, h2]
  exact Finset.sum_congr rfl fun x _ => mul_comm _ _

/-- An X Pauli operator labeled by a vector in the X check row space fixes every code vector. -/
theorem cssPauliX_row_eq_id (c : CssData ι κX κZ) (x : ι → ZMod 2)
    (hx : x ∈ LinearMap.range (Matrix.mulVecLin c.hXᵀ))
    (w : (ι → ZMod 2) → ℂ) (hw : w ∈ cssCodespace c) :
    cssPauliX x *ᵥ w = w := by
  obtain ⟨u, hu⟩ := hx
  have hu' : c.hXᵀ *ᵥ u = x := hu
  rw [← hu', rowX_as_sum]
  have hwX := (mem_cssCodespace_iff c w).mp hw |>.1
  have h : ∀ i : κX, cssPauliX (u i • c.hX i) *ᵥ w = w := by
    intro i
    rcases (by decide : ∀ b : ZMod 2, b = 0 ∨ b = 1) (u i) with h0 | h1
    · rw [h0, zero_smul]
      exact cssPauliX_zero_vec w
    · rw [h1, one_smul]
      exact hwX i
  exact cssPauliX_sum_vec (fun i => u i • c.hX i) w h

/-- A Z Pauli operator labeled by a vector in the Z check row space fixes every code vector. -/
theorem cssPauliZ_row_eq_id (c : CssData ι κX κZ) (z : ι → ZMod 2)
    (hz : z ∈ LinearMap.range (Matrix.mulVecLin c.hZᵀ))
    (w : (ι → ZMod 2) → ℂ) (hw : w ∈ cssCodespace c) :
    cssPauliZ z *ᵥ w = w := by
  obtain ⟨v, hv⟩ := hz
  have hv' : c.hZᵀ *ᵥ v = z := hv
  rw [← hv', rowZ_as_sum]
  have hwZ := (mem_cssCodespace_iff c w).mp hw |>.2
  have h : ∀ j : κZ, cssPauliZ (v j • c.hZ j) *ᵥ w = w := by
    intro j
    rcases (by decide : ∀ b : ZMod 2, b = 0 ∨ b = 1) (v j) with h0 | h1
    · rw [h0, zero_smul]
      exact cssPauliZ_zero_vec w
    · rw [h1, one_smul]
      exact hwZ j
  exact cssPauliZ_sum_vec (fun j => v j • c.hZ j) w h

/-- A Pauli product whose two labels lie in their respective check row spaces fixes every code
vector. -/
theorem stabilizer_label_eq_id (c : CssData ι κX κZ) (x z : ι → ZMod 2)
    (hx : x ∈ LinearMap.range (Matrix.mulVecLin c.hXᵀ))
    (hz : z ∈ LinearMap.range (Matrix.mulVecLin c.hZᵀ))
    (w : (ι → ZMod 2) → ℂ) (hw : w ∈ cssCodespace c) :
    (cssPauliX x * cssPauliZ z) *ᵥ w = w := by
  rw [← Matrix.mulVec_mulVec, cssPauliZ_row_eq_id c z hz w hw,
    cssPauliX_row_eq_id c x hx w hw]

/-- A vector is fixed by a bit projector exactly when the underlying matrix acts with the
selected phase. -/
theorem cssCheckProjector_fixed_iff
    (S : Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ) (b : ZMod 2) (v : (ι → ZMod 2) → ℂ) :
    cssCheckProjector S b *ᵥ v = v ↔ S *ᵥ v = phaseOfBit b • v := by
  have hc : b = 0 ∨ b = 1 := (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) b
  rcases hc with rfl | rfl
  · simp only [cssCheckProjector, phaseOfBit_zero, one_smul,
      Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.one_mulVec]
    constructor
    · intro h
      ext a
      have hh := congrFun h a
      change (2 : ℂ)⁻¹ * (v a + (S *ᵥ v) a) = v a at hh
      linear_combination (2 : ℂ) * hh
    · intro h
      rw [h]
      module
  · simp only [cssCheckProjector, phaseOfBit_zero, phaseOfBit_one, one_smul, neg_one_smul,
      Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.neg_mulVec, Matrix.one_mulVec]
    constructor
    · intro h
      ext a
      have hh := congrFun h a
      change (2 : ℂ)⁻¹ * (v a - (S *ᵥ v) a) = v a at hh
      change (S *ᵥ v) a = -v a
      linear_combination (-2 : ℂ) * hh
    · intro h
      rw [h]
      module

/-- The product of a list of matrices fixes a vector fixed by every matrix in the list. -/
theorem list_prod_fixed
    (l : List (Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ)) (v : (ι → ZMod 2) → ℂ)
    (h : ∀ S ∈ l, S *ᵥ v = v) : l.prod *ᵥ v = v := by
  induction l with
  | nil => simp
  | cons S l ih =>
    rw [List.prod_cons, ← Matrix.mulVec_mulVec,
      ih (fun T hT => h T (List.mem_cons_of_mem _ hT)), h S (by simp)]

/-- A bit projector of an involution is idempotent. -/
theorem cssCheckProjector_idem
    (S : Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ) (hS : S * S = 1) (b : ZMod 2) :
    cssCheckProjector S b * cssCheckProjector S b = cssCheckProjector S b := by
  have hc : b = 0 ∨ b = 1 := (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) b
  rcases hc with rfl | rfl <;>
    simp only [cssCheckProjector, phaseOfBit_zero, phaseOfBit_one, one_smul, neg_one_smul,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, add_mul, mul_add, neg_mul, mul_neg,
      neg_neg, one_mul, mul_one, hS] <;> norm_num <;> module

/-- Any two X Pauli matrices commute. -/
theorem cssPauliX_comm (x y : ι → ZMod 2) :
    cssPauliX x * cssPauliX y = cssPauliX y * cssPauliX x := by
  rw [cssPauliX_mul, cssPauliX_mul, add_comm]

/-- Any two Z Pauli matrices commute. -/
theorem cssPauliZ_comm (x y : ι → ZMod 2) :
    cssPauliZ x * cssPauliZ y = cssPauliZ y * cssPauliZ x := by
  rw [cssPauliZ_mul, cssPauliZ_mul, add_comm]

/-- An X check and a Z check of a CSS code commute. -/
theorem cssCheck_cross_comm (c : CssData ι κX κZ) (i : κX) (j : κZ) :
    cssPauliX (c.hX i) * cssPauliZ (c.hZ j) = cssPauliZ (c.hZ j) * cssPauliX (c.hX i) := by
  have h : bitDot (c.hX i) (c.hZ j) = 0 := by
    simpa [bitDot, dotProduct, Matrix.mul_apply] using congrFun (congrFun c.hcompat i) j
  rw [cssPauliXZ_comm, bitDot_comm, h, phaseOfBit_zero, one_smul]

/-- Any two CSS check matrices commute. -/
theorem cssCheck_commute (c : CssData ι κX κZ) (k k' : κX ⊕ κZ) :
    cssCheck c k * cssCheck c k' = cssCheck c k' * cssCheck c k := by
  cases k with
  | inl i =>
    cases k' with
    | inl i' => exact cssPauliX_comm (c.hX i) (c.hX i')
    | inr j => exact cssCheck_cross_comm c i j
  | inr j =>
    cases k' with
    | inl i => exact (cssCheck_cross_comm c i j).symm
    | inr j' => exact cssPauliZ_comm (c.hZ j) (c.hZ j')

/-- Bit projectors formed from two commuting matrices commute. -/
theorem cssCheckProjector_comm
    (S T : Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ) (b b' : ZMod 2)
    (h : S * T = T * S) :
    cssCheckProjector S b * cssCheckProjector T b' =
      cssCheckProjector T b' * cssCheckProjector S b := by
  simp only [cssCheckProjector, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 1
  rw [add_mul, mul_add, mul_add, one_mul, mul_one, add_mul, mul_add, mul_add, one_mul, mul_one]
  have h1 : (phaseOfBit b • S) * (phaseOfBit b' • T) =
      (phaseOfBit b' • T) * (phaseOfBit b • S) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      h]
    ring
  rw [h1]
  simp only [add_assoc, add_comm, add_left_comm, mul_one, one_mul]

/-- A selected bit projector absorbs a product containing it when its matrix is an involution
commuting with all listed matrices. -/
theorem cssCheckProjector_absorb_list
    (l : List (Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ))
    (f : (Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ) → ZMod 2)
    (S : Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ) (b : ZMod 2)
    (hmem : S ∈ l) (hf : f S = b) (hS : S * S = 1)
    (hcomm : ∀ T ∈ l, T * S = S * T) :
    cssCheckProjector S b * (l.map fun T => cssCheckProjector T (f T)).prod =
      (l.map fun T => cssCheckProjector T (f T)).prod := by
  induction l with
  | nil => simp at hmem
  | cons T l ih =>
    by_cases hST : T = S
    · subst T
      rw [List.map_cons, List.prod_cons, hf]
      rw [← mul_assoc, cssCheckProjector_idem S hS b]
    · rw [List.map_cons, List.prod_cons]
      have hmem' : S ∈ l := by
        cases List.mem_cons.mp hmem with
        | inl h => exact absurd h.symm hST
        | inr h => exact h
      have hcomm' : cssCheckProjector S b * cssCheckProjector T (f T) =
          cssCheckProjector T (f T) * cssCheckProjector S b := by
        apply cssCheckProjector_comm
        exact (hcomm T (by simp)).symm
      calc
        cssCheckProjector S b * (cssCheckProjector T (f T) * (l.map fun T => cssCheckProjector T (f T)).prod)
            = (cssCheckProjector S b * cssCheckProjector T (f T)) * (l.map fun T => cssCheckProjector T (f T)).prod := by
              rw [← mul_assoc]
        _ = (cssCheckProjector T (f T) * cssCheckProjector S b) * (l.map fun T => cssCheckProjector T (f T)).prod := by
              rw [hcomm']
        _ = cssCheckProjector T (f T) * (cssCheckProjector S b * (l.map fun T => cssCheckProjector T (f T)).prod) := by
              rw [mul_assoc]
        _ = cssCheckProjector T (f T) * (l.map fun T => cssCheckProjector T (f T)).prod := by
              rw [ih hmem' (fun U hU => hcomm U (List.mem_cons_of_mem _ hU))]

/-- Each CSS check squares to the identity. -/
theorem cssCheck_square (c : CssData ι κX κZ) (k : κX ⊕ κZ) :
    cssCheck c k * cssCheck c k = 1 := by
  cases k with
  | inl i => exact cssPauliX_self_mul (c.hX i)
  | inr j => exact cssPauliZ_self_mul (c.hZ j)

/-- A bit projector absorbs an indexed product containing it when its underlying matrix is an
involution commuting with every indexed factor. -/
theorem cssCheckProjector_absorb_map
    {κ : Type*} (l : List κ) (g : κ → Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ) (f : κ → ZMod 2)
    (k : κ) (hk : k ∈ l) (hS : g k * g k = 1)
    (hcomm : ∀ j ∈ l, g j * g k = g k * g j) :
    cssCheckProjector (g k) (f k) *
      (l.map fun j => cssCheckProjector (g j) (f j)).prod =
      (l.map fun j => cssCheckProjector (g j) (f j)).prod := by
  induction l with
  | nil => simp at hk
  | cons j l ih =>
    by_cases hjk : j = k
    · subst j
      rw [List.map_cons, List.prod_cons]
      rw [← mul_assoc, cssCheckProjector_idem (g k) hS (f k)]
    · rw [List.map_cons, List.prod_cons]
      have hk' : k ∈ l := by
        cases List.mem_cons.mp hk with
        | inl h => exact absurd h.symm hjk
        | inr h => exact h
      have hcomm' : cssCheckProjector (g k) (f k) * cssCheckProjector (g j) (f j) =
          cssCheckProjector (g j) (f j) * cssCheckProjector (g k) (f k) := by
        apply cssCheckProjector_comm
        exact (hcomm j (by simp)).symm
      calc
        cssCheckProjector (g k) (f k) * (cssCheckProjector (g j) (f j) * (l.map fun j => cssCheckProjector (g j) (f j)).prod)
            = (cssCheckProjector (g k) (f k) * cssCheckProjector (g j) (f j)) * (l.map fun j => cssCheckProjector (g j) (f j)).prod := by
              rw [← mul_assoc]
        _ = (cssCheckProjector (g j) (f j) * cssCheckProjector (g k) (f k)) * (l.map fun j => cssCheckProjector (g j) (f j)).prod := by
              rw [hcomm']
        _ = cssCheckProjector (g j) (f j) * (cssCheckProjector (g k) (f k) * (l.map fun j => cssCheckProjector (g j) (f j)).prod) := by
              rw [mul_assoc]
        _ = cssCheckProjector (g j) (f j) * (l.map fun j => cssCheckProjector (g j) (f j)).prod := by
              rw [ih hk' (fun U hU => hcomm U (List.mem_cons_of_mem _ hU))]

/-- Each check projector selected by a syndrome absorbs that syndrome projector. -/
theorem cssSyndromeProjector_absorb (c : CssData ι κX κZ)
    (η : (κX → ZMod 2) × (κZ → ZMod 2)) (k : κX ⊕ κZ) :
    cssCheckProjector (cssCheck c k) (Sum.elim η.1 η.2 k) * cssSyndromeProjector c η =
      cssSyndromeProjector c η := by
  classical
  unfold cssSyndromeProjector
  apply cssCheckProjector_absorb_map Finset.univ.toList (cssCheck c) (Sum.elim η.1 η.2) k
  · exact Finset.mem_toList.mpr (Finset.mem_univ k)
  · exact cssCheck_square c k
  · intro j _
    exact cssCheck_commute c j k

/-- A Pauli product squares to the identity multiplied by the phase of the binary pairing of its
labels. -/
theorem pauli_square (x z : ι → ZMod 2) :
    (cssPauliX x * cssPauliZ z) * (cssPauliX x * cssPauliZ z) =
      phaseOfBit (bitDot z x) • 1 := by
  rw [cssPauliXZ_mul, binary_add_self, binary_add_self,
    cssPauliX_zero, cssPauliZ_zero, one_mul]

/-- The Hamming weight of a one-bit vector is zero for the zero vector and one otherwise. -/
theorem bitWeight_fin1 (z : Fin 1 → ZMod 2) :
    bitWeight z = if z = 0 then 0 else 1 := by
  classical
  by_cases h : z = 0
  · subst z
    simp [bitWeight]
  · have h0 : z 0 ≠ 0 := by
      intro hh
      apply h
      funext i
      have : i = 0 := by omega
      subst i
      exact hh
    have h1 : z 0 = 1 := by
      rcases (by decide : ∀ b : ZMod 2, b = 0 ∨ b = 1) (z 0) with h0' | h1'
      · exact absurd h0' h0
      · exact h1'
    have hcard : (Finset.univ.filter fun i : Fin 1 => z i ≠ 0).card = 1 := by
      have : (Finset.univ.filter fun i : Fin 1 => z i ≠ 0) = {0} := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro _
          have : i = 0 := by omega
          exact this
        · intro hi
          subst hi
          exact h0
      rw [this]
      simp
    rw [if_neg h, bitWeight, hcard]

/-- The CSS code on one qubit with no X checks and no Z checks. -/
def oneQubitEmptyCss : CssData (Fin 1) (Fin 0) (Fin 0) where
  hX := 0
  hZ := 0
  hcompat := by
    ext
    simp

/-- A nonzero one-bit vector has Hamming weight one. -/
theorem bitWeight_fin1_ne_zero {z : Fin 1 → ZMod 2} (hz : z ≠ 0) :
    bitWeight z = 1 := by
  rw [bitWeight_fin1, if_neg hz]

/-- The linear map from the empty coordinate space into the one-bit space has zero range. -/
theorem range_mulVecLin_emptyZ :
    LinearMap.range (Matrix.mulVecLin (0 : Matrix (Fin 1) (Fin 0) (ZMod 2))) = ⊥ := by
  have h : Matrix.mulVecLin (0 : Matrix (Fin 1) (Fin 0) (ZMod 2)) = 0 := by
    ext v
    simp
  rw [h, LinearMap.range_zero]

/-- The transpose of the empty X check matrix has zero range. -/
theorem range_mulVecLin_emptyX :
    LinearMap.range (Matrix.mulVecLin ((0 : Matrix (Fin 0) (Fin 1) (ZMod 2))ᵀ)) = ⊥ := by
  rw [Matrix.transpose_zero]
  exact range_mulVecLin_emptyZ

/-- The one-qubit CSS code with no checks has distance one. -/
theorem oneQubitEmptyCss_distance :
    cssDistance oneQubitEmptyCss = 1 := by
  classical
  have hX0 : oneQubitEmptyCss.hX = (0 : Matrix (Fin 0) (Fin 1) (ZMod 2)) := rfl
  have hZ0 : oneQubitEmptyCss.hZ = (0 : Matrix (Fin 0) (Fin 1) (ZMod 2)) := rfl
  unfold cssDistance
  rw [hX0, hZ0]
  have hzset : {w : ℕ∞ | ∃ z : Fin 1 → ZMod 2,
      (0 : Matrix (Fin 0) (Fin 1) (ZMod 2)) *ᵥ z = 0 ∧
      z ∉ LinearMap.range (Matrix.mulVecLin ((0 : Matrix (Fin 0) (Fin 1) (ZMod 2))ᵀ)) ∧
      (bitWeight z : ℕ∞) = w} = {(1 : ℕ∞)} := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨z, _, hzout, hw⟩
      have hnz : z ≠ 0 := by
        intro h
        apply hzout
        rw [h, range_mulVecLin_emptyX]
        exact Submodule.zero_mem ⊥
      rw [bitWeight_fin1_ne_zero hnz] at hw
      exact_mod_cast hw.symm
    · intro hw
      refine ⟨fun _ : Fin 1 => (1 : ZMod 2), by simp, ?_, ?_⟩
      · intro hin
        rw [range_mulVecLin_emptyX] at hin
        have hz : (fun _ => (1 : ZMod 2)) = 0 := hin
        have h1 := congrFun hz 0
        norm_num at h1
      · have hbw : bitWeight (fun _ : Fin 1 => (1 : ZMod 2)) = 1 :=
          bitWeight_fin1_ne_zero fun h => absurd (congrFun h 0) (by norm_num)
        rw [hbw]
        exact_mod_cast hw.symm
  rw [hzset]
  simp

/-- If a Pauli weight differs from `w`, no scalar can satisfy the conjunction of scalar action
and equality of that weight to `w` for every code vector. -/
theorem not_exists_scalar_of_weight_ne
    (c : CssData ι κX κZ) (x z : ι → ZMod 2) (w : ℕ∞)
    (hne : (pauliWeight x z : ℕ∞) ≠ w) :
    ¬ ∃ φ : ℂ, ∀ v : cssCodespace c,
      (cssPauliX x * cssPauliZ z) *ᵥ (v : (ι → ZMod 2) → ℂ) =
        φ • (v : (ι → ZMod 2) → ℂ) ∧ (pauliWeight x z : ℕ∞) = w := by
  rintro ⟨φ, hφ⟩
  have h0 : (0 : (ι → ZMod 2) → ℂ) ∈ cssCodespace c := Submodule.zero_mem _
  have := hφ ⟨0, h0⟩
  exact hne this.2

/-- For the one-qubit code with no checks, the infimum in the distance expression with weight
equality inside the negated scalar condition is zero. -/
theorem frozenDistSet_oneQubitEmpty_sInf :
    (sInf {w : ℕ∞ | ∃ (x z : Fin 1 → ZMod 2),
        oneQubitEmptyCss.hX *ᵥ z = 0 ∧ oneQubitEmptyCss.hZ *ᵥ x = 0 ∧
        ¬ ∃ φ : ℂ, ∀ v : cssCodespace oneQubitEmptyCss,
          (cssPauliX x * cssPauliZ z) *ᵥ (v : (Fin 1 → ZMod 2) → ℂ) =
            φ • (v : (Fin 1 → ZMod 2) → ℂ) ∧
        (pauliWeight x z : ℕ∞) = w}) = 0 := by
  have heq : {w : ℕ∞ | ∃ (x z : Fin 1 → ZMod 2),
      oneQubitEmptyCss.hX *ᵥ z = 0 ∧ oneQubitEmptyCss.hZ *ᵥ x = 0 ∧
      ¬ ∃ φ : ℂ, ∀ v : cssCodespace oneQubitEmptyCss,
        (cssPauliX x * cssPauliZ z) *ᵥ (v : (Fin 1 → ZMod 2) → ℂ) =
          φ • (v : (Fin 1 → ZMod 2) → ℂ) ∧
      (pauliWeight x z : ℕ∞) = w} = (Set.univ : Set ℕ∞) := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    by_cases hw : w = 0
    · have hbw : pauliWeight (fun _ : Fin 1 => (1 : ZMod 2)) 0 = 1 := by
        simp [pauliWeight, bitWeight]
      have hcomm : oneQubitEmptyCss.hX *ᵥ (0 : Fin 1 → ZMod 2) = 0 ∧
          oneQubitEmptyCss.hZ *ᵥ (fun _ : Fin 1 => (1 : ZMod 2)) = 0 := by
        simp
      have hneg : ¬ ∃ φ : ℂ, ∀ v : cssCodespace oneQubitEmptyCss,
          (cssPauliX (fun _ : Fin 1 => (1 : ZMod 2)) * cssPauliZ (0 : Fin 1 → ZMod 2)) *ᵥ
              (v : (Fin 1 → ZMod 2) → ℂ) =
            φ • (v : (Fin 1 → ZMod 2) → ℂ) ∧
          (pauliWeight (fun _ : Fin 1 => (1 : ZMod 2)) 0 : ℕ∞) = w := by
        apply not_exists_scalar_of_weight_ne
        rw [hbw]
        intro h
        have h1 : ((1 : ℕ∞) : ℕ∞) = 0 := h.trans hw
        norm_num at h1
      exact ⟨fun _ : Fin 1 => (1 : ZMod 2), 0, hcomm.1, hcomm.2, hneg⟩
    · have hbw : pauliWeight (0 : Fin 1 → ZMod 2) 0 = 0 := by
        simp [pauliWeight]
      have hcomm : oneQubitEmptyCss.hX *ᵥ (0 : Fin 1 → ZMod 2) = 0 ∧
          oneQubitEmptyCss.hZ *ᵥ (0 : Fin 1 → ZMod 2) = 0 := by
        simp
      have hneg : ¬ ∃ φ : ℂ, ∀ v : cssCodespace oneQubitEmptyCss,
          (cssPauliX (0 : Fin 1 → ZMod 2) * cssPauliZ (0 : Fin 1 → ZMod 2)) *ᵥ
              (v : (Fin 1 → ZMod 2) → ℂ) =
            φ • (v : (Fin 1 → ZMod 2) → ℂ) ∧
          (pauliWeight (0 : Fin 1 → ZMod 2) 0 : ℕ∞) = w := by
        apply not_exists_scalar_of_weight_ne
        rw [hbw]
        intro h
        exact hw h.symm
      exact ⟨0, 0, hcomm.1, hcomm.2, hneg⟩
  rw [heq]
  exact sInf_univ

/-- The one-qubit code with no checks has distance different from the infimum defined with
weight equality inside the negated scalar condition. -/
theorem frozenDistance_counterexample :
    cssDistance oneQubitEmptyCss ≠
      sInf {w : ℕ∞ | ∃ (x z : Fin 1 → ZMod 2),
        oneQubitEmptyCss.hX *ᵥ z = 0 ∧ oneQubitEmptyCss.hZ *ᵥ x = 0 ∧
        ¬ ∃ φ : ℂ, ∀ v : cssCodespace oneQubitEmptyCss,
          (cssPauliX x * cssPauliZ z) *ᵥ (v : (Fin 1 → ZMod 2) → ℂ) =
            φ • (v : (Fin 1 → ZMod 2) → ℂ) ∧
        (pauliWeight x z : ℕ∞) = w} := by
  rw [oneQubitEmptyCss_distance, frozenDistSet_oneQubitEmpty_sInf]
  norm_num

/-- A check acts on a syndrome projector by its selected syndrome phase. -/
theorem cssCheck_mul_syndrome (c : CssData ι κX κZ)
    (η : (κX → ZMod 2) × (κZ → ZMod 2)) (k : κX ⊕ κZ) :
    cssCheck c k * cssSyndromeProjector c η =
      phaseOfBit (Sum.elim η.1 η.2 k) • cssSyndromeProjector c η := by
  classical
  set φ : ℂ := phaseOfBit (Sum.elim η.1 η.2 k)
  set S : Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ := cssCheck c k
  set P : Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ := cssSyndromeProjector c η
  have habs : ((2⁻¹ : ℂ) • (1 + φ • S)) * P = P := by
    have := cssSyndromeProjector_absorb c η k
    simpa [S, P, φ, cssCheckProjector] using this
  have hsum : (1 + φ • S) * P = (2 : ℂ) • P := by
    have habs' : (2⁻¹ : ℂ) • ((1 + φ • S) * P) = P := by
      rw [← Matrix.smul_mul]
      exact habs
    have := congrArg (fun M : Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ => (2 : ℂ) • M) habs'
    simp only [smul_smul, mul_inv_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul] at this
    exact this
  have hone : (1 : Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ) * P = P := one_mul _
  have hsplit : P + (φ • S) * P = (2 : ℂ) • P := by
    have := hsum
    rw [add_mul, hone] at this
    exact this
  have hφS : (φ • S) * P = P := by
    have hswap : (φ • S) * P + P = (2 : ℂ) • P := by
      rw [add_comm]
      exact hsplit
    have hsub : ((φ • S) * P + P) - P = ((2 : ℂ) • P) - P :=
      congrArg (fun M : Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ => M - P) hswap
    rw [add_sub_cancel_right] at hsub
    have h2 : (2 : ℂ) • P - P = P := by
      rw [two_smul, add_sub_cancel_right]
    rw [h2] at hsub
    exact hsub
  have hφ : φ * φ = 1 := phaseOfBit_mul_self _
  have h : φ • ((φ • S) * P) = φ • P := congrArg (φ • ·) hφS
  rw [Matrix.smul_mul, smul_smul, hφ, one_smul] at h
  exact h

/-- Every element of `ZMod 2` adds to itself to give zero. -/
theorem zmod2_add_self (b : ZMod 2) : b + b = 0 := by
  have h2 : (2 : ZMod 2) = 0 := by decide
  calc b + b = (2 : ZMod 2) * b := by ring
    _ = 0 * b := by rw [h2]
    _ = 0 := by ring

/-- Two binary elements whose sum is zero are equal. -/
theorem zmod2_eq_of_add_eq_zero {a b : ZMod 2} (h : a + b = 0) : a = b := by
  calc a = a + 0 := by ring
    _ = a + (b + b) := by rw [zmod2_add_self b]
    _ = (a + b) + b := by ring
    _ = 0 + b := by rw [h]
    _ = b := by ring

/-- The product of two Pauli products has zero trace unless both pairs of labels sum to zero. -/
theorem cssPauliXZ_mul_trace (x z u v : ι → ZMod 2)
    (h : ¬(x + u = 0 ∧ z + v = 0)) :
    Matrix.trace ((cssPauliX x * cssPauliZ z) * (cssPauliX u * cssPauliZ v)) = 0 := by
  rw [cssPauliXZ_mul, Matrix.trace_smul, cssPauliXZ_trace, if_neg h, smul_zero]

section StabilizerSum

variable (c : CssData ι κX κZ)

noncomputable local instance : Fintype
    ↥(LinearMap.range (Matrix.mulVecLin c.hXᵀ)) := Fintype.ofFinite _

noncomputable local instance : Fintype
    ↥(LinearMap.range (Matrix.mulVecLin c.hZᵀ)) := Fintype.ofFinite _

/-- A vector in the Z check row space is orthogonal, under `bitDot`, to a vector in the X check
row space. -/
private theorem rows_orthogonal (u : ι → ZMod 2)
    (hu : u ∈ LinearMap.range (Matrix.mulVecLin c.hXᵀ))
    (v : ι → ZMod 2) (hv : v ∈ LinearMap.range (Matrix.mulVecLin c.hZᵀ)) :
    bitDot v u = 0 := by
  classical
  obtain ⟨a, ha⟩ := hu
  obtain ⟨b, hb⟩ := hv
  have hc : c.hZ * c.hXᵀ = 0 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero]
      using congrArg Matrix.transpose c.hcompat
  rw [← ha, ← hb]
  change (c.hZᵀ *ᵥ b) ⬝ᵥ (c.hXᵀ *ᵥ a) = 0
  rw [dotProduct_mulVec, Matrix.mulVec_transpose, Matrix.vecMul_vecMul, hc]
  simp

/-- Multiplying the transposed X check matrix by a coordinate unit vector selects the
corresponding check row. -/
private theorem transpose_mulVec_single (i : κX) :
    c.hXᵀ *ᵥ (Pi.single i (1 : ZMod 2)) = c.hX i := by
  funext p
  simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.single_apply]

/-- Multiplying the transposed Z check matrix by a coordinate unit vector selects the
corresponding check row. -/
private theorem transpose_mulVec_single_Z (j : κZ) :
    c.hZᵀ *ᵥ (Pi.single j (1 : ZMod 2)) = c.hZ j := by
  funext p
  simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.single_apply]

/-- The sum of Pauli products over the X and Z check row spaces. -/
noncomputable def stabilizerSum : Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ :=
  ∑ p : ↥(LinearMap.range (Matrix.mulVecLin c.hXᵀ)) ×
      ↥(LinearMap.range (Matrix.mulVecLin c.hZᵀ)),
    cssPauliX (p.1 : ι → ZMod 2) * cssPauliZ (p.2 : ι → ZMod 2)

/-- Left multiplication by an X check leaves the stabilizer sum unchanged. -/
theorem cssPauliX_row_mul_stabilizerSum (i : κX) :
    cssPauliX (c.hX i) * stabilizerSum c = stabilizerSum c := by
  classical
  set b : ↥(LinearMap.range (Matrix.mulVecLin c.hXᵀ)) ×
      ↥(LinearMap.range (Matrix.mulVecLin c.hZᵀ)) :=
    (⟨c.hX i, ⟨Pi.single i (1 : ZMod 2), transpose_mulVec_single c i⟩⟩,
      ⟨0, ⟨0, Matrix.mulVec_zero _⟩⟩) with hb
  have hbij : Function.Bijective (fun p => b + p) :=
    ⟨fun p q h => add_left_cancel h,
      fun p => ⟨-b + p, by show b + (-b + p) = p; rw [← add_assoc, add_neg_cancel, zero_add]⟩⟩
  rw [stabilizerSum, Matrix.mul_sum]
  refine Fintype.sum_bijective _ hbij _ _ ?_
  intro p
  show cssPauliX (c.hX i) * (cssPauliX (p.1 : ι → ZMod 2) * cssPauliZ (p.2 : ι → ZMod 2)) =
    cssPauliX ((b + p).1 : ι → ZMod 2) * cssPauliZ ((b + p).2 : ι → ZMod 2)
  rw [← mul_assoc, cssPauliX_mul]
  simp only [hb, Prod.fst_add, Prod.snd_add, Submodule.coe_add, zero_add]

/-- Left multiplication by a Z check leaves the stabilizer sum unchanged. -/
theorem cssPauliZ_row_mul_stabilizerSum (j : κZ) :
    cssPauliZ (c.hZ j) * stabilizerSum c = stabilizerSum c := by
  classical
  set b : ↥(LinearMap.range (Matrix.mulVecLin c.hXᵀ)) ×
      ↥(LinearMap.range (Matrix.mulVecLin c.hZᵀ)) :=
    (⟨0, ⟨0, Matrix.mulVec_zero _⟩⟩,
      ⟨c.hZ j, ⟨Pi.single j (1 : ZMod 2), transpose_mulVec_single_Z c j⟩⟩) with hb
  have hbij : Function.Bijective (fun p => p + b) :=
    ⟨fun p q h => add_right_cancel h,
      fun p => ⟨p + -b, by show p + -b + b = p; rw [add_assoc, neg_add_cancel, add_zero]⟩⟩
  rw [stabilizerSum, Matrix.mul_sum]
  refine Fintype.sum_bijective _ hbij _ _ ?_
  intro p
  show cssPauliZ (c.hZ j) * (cssPauliX (p.1 : ι → ZMod 2) * cssPauliZ (p.2 : ι → ZMod 2)) =
    cssPauliX ((p + b).1 : ι → ZMod 2) * cssPauliZ ((p + b).2 : ι → ZMod 2)
  rw [← mul_assoc, cssPauliZX_phase,
    rows_orthogonal c (p.1 : ι → ZMod 2) p.1.property (c.hZ j)
      ⟨Pi.single j (1 : ZMod 2), transpose_mulVec_single_Z c j⟩,
    phaseOfBit_zero, one_smul, mul_assoc, cssPauliZ_mul]
  simp only [hb, Prod.fst_add, Prod.snd_add, Submodule.coe_add, add_zero, add_comm (c.hZ j)]

/-- Applying the stabilizer sum to any vector yields a vector in the CSS codespace. -/
theorem stabilizerSum_mem_codespace (w : (ι → ZMod 2) → ℂ) :
    stabilizerSum c *ᵥ w ∈ cssCodespace c := by
  rw [mem_cssCodespace_iff]
  constructor
  · intro i
    show cssPauliX (c.hX i) *ᵥ (stabilizerSum c *ᵥ w) = _
    rw [Matrix.mulVec_mulVec, cssPauliX_row_mul_stabilizerSum c i]
  · intro j
    show cssPauliZ (c.hZ j) *ᵥ (stabilizerSum c *ᵥ w) = _
    rw [Matrix.mulVec_mulVec, cssPauliZ_row_mul_stabilizerSum c j]

/-- Applying a matrix to a coordinate unit vector selects the corresponding matrix column. -/
private theorem mulVec_single_entry (M : Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ)
    (a b : ι → ZMod 2) :
    (M *ᵥ Pi.single b 1) a = M a b := by
  simp [Matrix.mulVec]

omit [DecidableEq κX] [DecidableEq κZ] in

/-- The stabilizer sum has nonzero trace. -/
theorem stabilizerSum_trace_ne_zero : Matrix.trace (stabilizerSum c) ≠ 0 := by
  classical
  rw [stabilizerSum, Matrix.trace_sum]
  rw [Finset.sum_eq_single (⟨(0 : ι → ZMod 2), ⟨0, Matrix.mulVec_zero _⟩⟩,
    ⟨(0 : ι → ZMod 2), ⟨0, Matrix.mulVec_zero _⟩⟩)]
  · simp only [cssPauliX_zero, cssPauliZ_zero, one_mul, Matrix.trace_one]
    exact_mod_cast (Fintype.card_pos (α := ι → ZMod 2)).ne'
  · intro p _ hp
    rw [cssPauliXZ_trace, if_neg]
    intro hcon
    apply hp
    have h1 : (p.1 : ι → ZMod 2) = 0 := hcon.1
    have h2 : (p.2 : ι → ZMod 2) = 0 := hcon.2
    apply Prod.ext <;> apply Subtype.ext <;> assumption
  · simp

omit [DecidableEq κX] [DecidableEq κZ] in

/-- A Pauli product with X label outside the X check row space has zero trace after
multiplication by the stabilizer sum. -/
theorem pauli_mul_stabilizerSum_trace_left (x z : ι → ZMod 2)
    (hnx : x ∉ LinearMap.range (Matrix.mulVecLin c.hXᵀ)) :
    Matrix.trace ((cssPauliX x * cssPauliZ z) * stabilizerSum c) = 0 := by
  classical
  rw [stabilizerSum, Matrix.mul_sum, Matrix.trace_sum]
  refine Finset.sum_eq_zero fun p _ => cssPauliXZ_mul_trace x z _ _ ?_
  rintro ⟨h1, h2⟩
  apply hnx
  obtain ⟨u, hu⟩ := p.1.property
  refine ⟨u, ?_⟩
  funext i
  have hi := congrFun h1 i
  have hu' := congrFun hu i
  simp only [Pi.add_apply, Pi.zero_apply, Matrix.mulVecLin_apply] at hi hu' ⊢
  rw [hu']
  exact (zmod2_eq_of_add_eq_zero hi).symm

omit [DecidableEq κX] [DecidableEq κZ] in

/-- A Pauli product with Z label outside the Z check row space has zero trace after
multiplication by the stabilizer sum. -/
theorem pauli_mul_stabilizerSum_trace_right (x z : ι → ZMod 2)
    (hnz : z ∉ LinearMap.range (Matrix.mulVecLin c.hZᵀ)) :
    Matrix.trace ((cssPauliX x * cssPauliZ z) * stabilizerSum c) = 0 := by
  classical
  rw [stabilizerSum, Matrix.mul_sum, Matrix.trace_sum]
  refine Finset.sum_eq_zero fun p _ => cssPauliXZ_mul_trace x z _ _ ?_
  rintro ⟨h1, h2⟩
  apply hnz
  obtain ⟨v, hv⟩ := p.2.property
  refine ⟨v, ?_⟩
  funext j
  have hj := congrFun h2 j
  have hv' := congrFun hv j
  simp only [Pi.add_apply, Pi.zero_apply, Matrix.mulVecLin_apply] at hj hv' ⊢
  rw [hv']
  exact (zmod2_eq_of_add_eq_zero hj).symm

/-- If a Pauli product acts by a scalar on every code vector, it multiplies the stabilizer sum
by the same scalar. -/
theorem pauli_mul_stabilizerSum (x z : ι → ZMod 2) (φ : ℂ)
    (hφ : ∀ v : cssCodespace c,
      (cssPauliX x * cssPauliZ z) *ᵥ (v : (ι → ZMod 2) → ℂ) =
        φ • (v : (ι → ZMod 2) → ℂ)) :
    (cssPauliX x * cssPauliZ z) * stabilizerSum c = φ • stabilizerSum c := by
  have hact : ∀ w : (ι → ZMod 2) → ℂ,
      ((cssPauliX x * cssPauliZ z) * stabilizerSum c) *ᵥ w =
        φ • (stabilizerSum c *ᵥ w) := by
    intro w
    rw [← Matrix.mulVec_mulVec]
    exact hφ ⟨stabilizerSum c *ᵥ w, stabilizerSum_mem_codespace c w⟩
  ext a b
  rw [← mulVec_single_entry (cssPauliX x * cssPauliZ z * stabilizerSum c) a b,
    ← mulVec_single_entry (φ • stabilizerSum c) a b,
    hact (Pi.single b 1), Matrix.smul_mulVec]

/-- Scalar action of a Pauli product on the CSS codespace forces both labels to belong to their
corresponding check row spaces. -/
theorem mem_rowspace_of_scalar_action (c : CssData ι κX κZ) (x z : ι → ZMod 2) (φ : ℂ)
    (hφ : ∀ v : cssCodespace c,
      (cssPauliX x * cssPauliZ z) *ᵥ (v : (ι → ZMod 2) → ℂ) =
        φ • (v : (ι → ZMod 2) → ℂ)) :
    x ∈ LinearMap.range (Matrix.mulVecLin c.hXᵀ) ∧
      z ∈ LinearMap.range (Matrix.mulVecLin c.hZᵀ) := by
  classical
  by_contra hcon
  rw [not_and_or] at hcon
  have hTr : Matrix.trace ((cssPauliX x * cssPauliZ z) * stabilizerSum c) = 0 := by
    rcases hcon with hnx | hnz
    · exact pauli_mul_stabilizerSum_trace_left c x z hnx
    · exact pauli_mul_stabilizerSum_trace_right c x z hnz
  have hPS := pauli_mul_stabilizerSum c x z φ hφ
  rw [hPS, Matrix.trace_smul, smul_eq_mul, mul_eq_zero] at hTr
  rcases hTr with hφ0 | hStr
  swap; exact absurd hStr (stabilizerSum_trace_ne_zero c)
  rw [hφ0, zero_smul] at hPS
  have hψ : phaseOfBit (bitDot z x) * phaseOfBit (bitDot z x) = 1 := phaseOfBit_mul_self _
  have hψne : phaseOfBit (bitDot z x) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hψ
    exact zero_ne_one hψ
  have hS0 : stabilizerSum c = 0 := by
    calc stabilizerSum c
        = (((phaseOfBit (bitDot z x))⁻¹ • (cssPauliX x * cssPauliZ z)) *
            (cssPauliX x * cssPauliZ z)) * stabilizerSum c := by
          rw [Matrix.smul_mul, pauli_square, smul_smul, inv_mul_cancel₀ hψne, one_smul, one_mul]
      _ = ((phaseOfBit (bitDot z x))⁻¹ • (cssPauliX x * cssPauliZ z)) *
          ((cssPauliX x * cssPauliZ z) * stabilizerSum c) := by rw [mul_assoc]
      _ = 0 := by rw [hPS, mul_zero]
  exact (stabilizerSum_trace_ne_zero c) (by rw [hS0, Matrix.trace_zero])

end StabilizerSum

/-- A Pauli product acts by some scalar on the CSS codespace exactly when both labels belong to
their corresponding check row spaces; see [Gottesman1997]. -/
theorem scalar_action_iff_mem_rowspace (c : CssData ι κX κZ) (x z : ι → ZMod 2) :
    (x ∈ LinearMap.range (Matrix.mulVecLin c.hXᵀ) ∧
      z ∈ LinearMap.range (Matrix.mulVecLin c.hZᵀ)) ↔
    ∃ φ : ℂ, ∀ v : cssCodespace c,
      (cssPauliX x * cssPauliZ z) *ᵥ (v : (ι → ZMod 2) → ℂ) =
        φ • (v : (ι → ZMod 2) → ℂ) := by
  constructor
  · rintro ⟨hx', hz'⟩
    refine ⟨1, fun v => ?_⟩
    rw [one_smul]
    exact stabilizer_label_eq_id c x z hx' hz' _ v.property
  · exact fun ⟨φ, hφ⟩ => mem_rowspace_of_scalar_action c x z φ hφ

/-- For labels satisfying the CSS commutation equations, failure of joint row-space membership
is equivalent to nonscalar action on the codespace. The CSS distance is the infimum of
weights of such commuting Pauli products with nonscalar action, as in the stabilizer
framework of [Gottesman1997]. -/
theorem logicalNonscalarRestriction :
    ∀ {ι κX κZ : Type} [Fintype ι] [Fintype κX] [Fintype κZ]
      [DecidableEq ι] [DecidableEq κX] [DecidableEq κZ]
      (c : CssData ι κX κZ) (x z : ι → ZMod 2),
      c.hX *ᵥ z = 0 → c.hZ *ᵥ x = 0 →
      (¬ (x ∈ LinearMap.range (Matrix.mulVecLin (c.hXᵀ)) ∧
          z ∈ LinearMap.range (Matrix.mulVecLin (c.hZᵀ))) ↔
        ¬ ∃ φ : ℂ, ∀ v : cssCodespace c,
          (cssPauliX x * cssPauliZ z) *ᵥ (v : (ι → ZMod 2) → ℂ) =
            φ • (v : (ι → ZMod 2) → ℂ)) ∧
      cssDistance c =
        sInf {w : ℕ∞ | ∃ (x z : ι → ZMod 2),
          c.hX *ᵥ z = 0 ∧ c.hZ *ᵥ x = 0 ∧
          (¬ ∃ φ : ℂ, ∀ v : cssCodespace c,
            (cssPauliX x * cssPauliZ z) *ᵥ (v : (ι → ZMod 2) → ℂ) =
              φ • (v : (ι → ZMod 2) → ℂ)) ∧
          (pauliWeight x z : ℕ∞) = w} := by
  intro ι' κX' κZ' _ _ _ _ _ _ c x z _hxz _hxz'
  refine ⟨not_congr (scalar_action_iff_mem_rowspace c x z), ?_⟩
  rw [cssDistance_eq_logical]
  congr 1
  ext w
  constructor
  · rintro ⟨x', z', h1, h2, h3, h4⟩
    exact ⟨x', z', h1, h2,
      fun hφ => h3 ((scalar_action_iff_mem_rowspace c x' z').mpr hφ), h4⟩
  · rintro ⟨x', z', h1, h2, h3, h4⟩
    refine ⟨x', z', h1, h2, fun hrow => h3 ?_, h4⟩
    exact (scalar_action_iff_mem_rowspace c x' z').mp hrow

end Qatlib.Concepts.CodingDecoding.CssTesters.LogicalNonscalarRestriction
