/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.CodingDecoding.CssTesters.LogicalNonscalarRestriction
public import Qatlib.Concepts.CodingDecoding.CssTesters.CssCode
public import Qatlib.Concepts.CodingDecoding.CssTesters.CssTester

@[expose] public section
open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode Qatlib.Concepts.CodingDecoding.CssTesters Qatlib.Concepts.CodingDecoding.CssTesters.CssTester Qatlib.Concepts.CodingDecoding.CssTesters.LogicalNonscalarRestriction
open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode
open Qatlib.Concepts.CodingDecoding.CssTesters.CssTester
open Qatlib.Concepts.CodingDecoding.CssTesters.LogicalNonscalarRestriction

open Qatlib.Concepts.CodingDecoding.CssTesters

namespace Qatlib.Concepts.CodingDecoding.CssTesters.EveryConsistentSyndromeRealized

open Matrix Filter

open scoped Classical BigOperators ENNReal

variable {ι κX κZ : Type*} [Fintype ι] [Fintype κX] [Fintype κZ]
  [DecidableEq ι] [DecidableEq κX] [DecidableEq κZ]

omit [Fintype ι] [Fintype κX] [Fintype κZ] [DecidableEq ι] [DecidableEq κX] [DecidableEq κZ] in
/-- A vector is fixed by the syndrome projector exactly when every CSS check acts by the
prescribed syndrome phase. -/
theorem cssSyndromeProjector_fixed_iff [Fintype ι] [Fintype κX] [Fintype κZ]
    [DecidableEq ι] [DecidableEq κX] [DecidableEq κZ] (c : CssData ι κX κZ)
    (η : (κX → ZMod 2) × (κZ → ZMod 2)) (v : (ι → ZMod 2) → ℂ) :
    cssSyndromeProjector c η *ᵥ v = v ↔
      ∀ k : κX ⊕ κZ, cssCheck c k *ᵥ v = phaseOfBit (Sum.elim η.1 η.2 k) • v := by
  constructor
  · intro h k
    apply (cssCheckProjector_fixed_iff _ _ _).mp
    rw [← h, Matrix.mulVec_mulVec, cssSyndromeProjector_absorb, h]
  · intro h
    unfold cssSyndromeProjector
    apply list_prod_fixed
    intro S hS
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hS
    exact (cssCheckProjector_fixed_iff _ _ _).mpr (h k)

omit [Fintype κZ] [DecidableEq ι] [DecidableEq κX] [DecidableEq κZ] in
/-- Multiplying the transpose of the X-check matrix by coefficients equals the corresponding
linear combination of X-check rows. -/
theorem rowX_as_sum' [Fintype κZ] [DecidableEq ι] [DecidableEq κX] [DecidableEq κZ] (c : CssData ι κX κZ) (a : κX → ZMod 2) :
    c.hXᵀ *ᵥ a = ∑ i : κX, a i • c.hX i := by
  funext p
  have h1 : (c.hXᵀ *ᵥ a) p = ∑ x : κX, c.hX x p * a x := by
    simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  have h2 : (∑ i : κX, a i • c.hX i) p = ∑ i : κX, a i * c.hX i p := by
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl fun x _ => by simp [Pi.smul_apply, smul_eq_mul]
  rw [h1, h2]
  exact Finset.sum_congr rfl fun x _ => mul_comm _ _

omit [Fintype ι] [Fintype κX] [Fintype κZ] [DecidableEq ι] [DecidableEq κX] [DecidableEq κZ] in
/-- A scalar multiple of an X-check row acts on the syndrome projector by its prescribed
syndrome phase. -/
theorem cssPauliX_smul_check_mul_syndrome [Fintype ι] [Fintype κX] [Fintype κZ]
    [DecidableEq ι] [DecidableEq κX] [DecidableEq κZ] (c : CssData ι κX κZ)
    (η : (κX → ZMod 2) × (κZ → ZMod 2)) (i : κX) (b : ZMod 2) :
    cssPauliX (b • c.hX i) * cssSyndromeProjector c η =
      phaseOfBit (b * η.1 i) • cssSyndromeProjector c η := by
  rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) b with h0 | h1
  · rw [h0, zero_smul, cssPauliX_zero, one_mul, zero_mul, phaseOfBit_zero, one_smul]
  · rw [h1, one_smul, one_mul]
    have h := cssCheck_mul_syndrome c η (Sum.inl i)
    simpa [cssCheck] using h

/-- An X-check row combination acts on the syndrome projector by the phase of its syndrome dot
product. -/
theorem cssPauliX_row_mul_syndrome (c : CssData ι κX κZ)
    (η : (κX → ZMod 2) × (κZ → ZMod 2)) (a : κX → ZMod 2) :
    cssPauliX (c.hXᵀ *ᵥ a) * cssSyndromeProjector c η =
      phaseOfBit (dotProduct a η.1) • cssSyndromeProjector c η := by
  classical
  rw [rowX_as_sum']
  have h : ∀ s : Finset κX, ∀ f : κX → ι → ZMod 2,
      (∀ i ∈ s, f i = a i • c.hX i) →
      cssPauliX (∑ i ∈ s, f i) * cssSyndromeProjector c η =
        phaseOfBit (∑ i ∈ s, a i * η.1 i) • cssSyndromeProjector c η := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro f _
      simp [cssPauliX_zero, one_mul, phaseOfBit_zero, one_smul]
    | @insert i s hi ih =>
      intro f hf
      rw [Finset.sum_insert hi, ← cssPauliX_mul, mul_assoc]
      have hi' : f i = a i • c.hX i := hf i (Finset.mem_insert_self i s)
      have hrest : ∀ j ∈ s, f j = a j • c.hX j := fun j hj => hf j (Finset.mem_insert_of_mem hj)
      rw [hi', ih f hrest, Matrix.mul_smul, cssPauliX_smul_check_mul_syndrome, smul_smul,
        Finset.sum_insert hi, phaseOfBit_add, mul_comm]
  specialize h Finset.univ (fun i => a i • c.hX i) (fun i _ => rfl)
  rw [h]
  simp [dotProduct]

/-- A nonzero syndrome projector forces the X syndrome to be orthogonal to every dependency
among X-check rows. -/
theorem syndrome_consistent_X (c : CssData ι κX κZ)
    (η : (κX → ZMod 2) × (κZ → ZMod 2)) (a : κX → ZMod 2)
    (hP : cssSyndromeProjector c η ≠ 0) (ha : c.hXᵀ *ᵥ a = 0) :
    dotProduct a η.1 = 0 := by
  have h := cssPauliX_row_mul_syndrome c η a
  rw [ha, cssPauliX_zero, one_mul] at h
  by_cases hd : dotProduct a η.1 = 0
  · exact hd
  · have h1 : dotProduct a η.1 = 1 := by
      rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (dotProduct a η.1) with h0 | h1
      · exact absurd h0 hd
      · exact h1
    rw [h1, phaseOfBit_one, neg_one_smul] at h
    have h2 : cssSyndromeProjector c η + cssSyndromeProjector c η = 0 := by
      nth_rewrite 2 [h]
      exact add_neg_cancel _
    have h3 : ((2 : ℂ) • cssSyndromeProjector c η) = 0 := by
      rw [two_smul]
      exact h2
    have h4 : (2 : ℂ) ≠ 0 := by norm_num
    have h5 : cssSyndromeProjector c η = 0 := by
      have hmul : ((2⁻¹ : ℂ) * 2) • cssSyndromeProjector c η =
          (1 : ℂ) • cssSyndromeProjector c η :=
        congrArg (fun z : ℂ => z • cssSyndromeProjector c η) (inv_mul_cancel₀ h4)
      rw [mul_smul, one_smul] at hmul
      rw [show (2 : ℂ) • cssSyndromeProjector c η = 0 from h3, smul_zero] at hmul
      exact hmul.symm
    exact absurd h5 hP

omit [Fintype ι] [Fintype κX] [Fintype κZ] [DecidableEq ι] [DecidableEq κX] [DecidableEq κZ] in
/-- Multiplying the transpose of the Z-check matrix by coefficients equals the corresponding
linear combination of Z-check rows. -/
theorem rowZ_as_sum' [Fintype ι] [Fintype κX] [Fintype κZ]
    [DecidableEq ι] [DecidableEq κX] [DecidableEq κZ] (c : CssData ι κX κZ) (a : κZ → ZMod 2) :
    c.hZᵀ *ᵥ a = ∑ j : κZ, a j • c.hZ j := by
  funext p
  have h1 : (c.hZᵀ *ᵥ a) p = ∑ x : κZ, c.hZ x p * a x := by
    simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  have h2 : (∑ j : κZ, a j • c.hZ j) p = ∑ j : κZ, a j * c.hZ j p := by
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl fun x _ => by simp [Pi.smul_apply, smul_eq_mul]
  rw [h1, h2]
  exact Finset.sum_congr rfl fun x _ => mul_comm _ _

omit [Fintype ι] [Fintype κX] [Fintype κZ] [DecidableEq ι] [DecidableEq κX] [DecidableEq κZ] in
/-- A scalar multiple of a Z-check row acts on the syndrome projector by its prescribed syndrome
phase. -/
theorem cssPauliZ_smul_check_mul_syndrome [Fintype ι] [Fintype κX] [Fintype κZ]
    [DecidableEq ι] [DecidableEq κX] [DecidableEq κZ] (c : CssData ι κX κZ)
    (η : (κX → ZMod 2) × (κZ → ZMod 2)) (j : κZ) (b : ZMod 2) :
    cssPauliZ (b • c.hZ j) * cssSyndromeProjector c η =
      phaseOfBit (b * η.2 j) • cssSyndromeProjector c η := by
  rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) b with h0 | h1
  · rw [h0, zero_smul, cssPauliZ_zero, one_mul, zero_mul, phaseOfBit_zero, one_smul]
  · rw [h1, one_smul, one_mul]
    have h := cssCheck_mul_syndrome c η (Sum.inr j)
    simpa [cssCheck] using h

/-- A Z-check row combination acts on the syndrome projector by the phase of its syndrome dot
product. -/
theorem cssPauliZ_row_mul_syndrome (c : CssData ι κX κZ)
    (η : (κX → ZMod 2) × (κZ → ZMod 2)) (a : κZ → ZMod 2) :
    cssPauliZ (c.hZᵀ *ᵥ a) * cssSyndromeProjector c η =
      phaseOfBit (dotProduct a η.2) • cssSyndromeProjector c η := by
  classical
  rw [rowZ_as_sum']
  have h : ∀ s : Finset κZ, ∀ f : κZ → ι → ZMod 2,
      (∀ j ∈ s, f j = a j • c.hZ j) →
      cssPauliZ (∑ j ∈ s, f j) * cssSyndromeProjector c η =
        phaseOfBit (∑ j ∈ s, a j * η.2 j) • cssSyndromeProjector c η := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro f _
      simp [cssPauliZ_zero, one_mul, phaseOfBit_zero, one_smul]
    | @insert j s hi ih =>
      intro f hf
      rw [Finset.sum_insert hi, ← cssPauliZ_mul, mul_assoc]
      have hj' : f j = a j • c.hZ j := hf j (Finset.mem_insert_self j s)
      have hrest : ∀ k ∈ s, f k = a k • c.hZ k := fun k hk => hf k (Finset.mem_insert_of_mem hk)
      rw [hj', ih f hrest, Matrix.mul_smul, cssPauliZ_smul_check_mul_syndrome, smul_smul,
        Finset.sum_insert hi, phaseOfBit_add, mul_comm]
  specialize h Finset.univ (fun j => a j • c.hZ j) (fun j _ => rfl)
  rw [h]
  simp [dotProduct]

/-- A nonzero syndrome projector forces the Z syndrome to be orthogonal to every dependency
among Z-check rows. -/
theorem syndrome_consistent_Z (c : CssData ι κX κZ)
    (η : (κX → ZMod 2) × (κZ → ZMod 2)) (a : κZ → ZMod 2)
    (hP : cssSyndromeProjector c η ≠ 0) (ha : c.hZᵀ *ᵥ a = 0) :
    dotProduct a η.2 = 0 := by
  have h := cssPauliZ_row_mul_syndrome c η a
  rw [ha, cssPauliZ_zero, one_mul] at h
  by_cases hd : dotProduct a η.2 = 0
  · exact hd
  · have h1 : dotProduct a η.2 = 1 := by
      rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (dotProduct a η.2) with h0 | h1
      · exact absurd h0 hd
      · exact h1
    rw [h1, phaseOfBit_one, neg_one_smul] at h
    have h2 : cssSyndromeProjector c η + cssSyndromeProjector c η = 0 := by
      nth_rewrite 2 [h]
      exact add_neg_cancel _
    have h3 : ((2 : ℂ) • cssSyndromeProjector c η) = 0 := by
      rw [two_smul]
      exact h2
    have h4 : (2 : ℂ) ≠ 0 := by norm_num
    have h5 : cssSyndromeProjector c η = 0 := by
      have hmul : ((2⁻¹ : ℂ) * 2) • cssSyndromeProjector c η =
          (1 : ℂ) • cssSyndromeProjector c η :=
        congrArg (fun z : ℂ => z • cssSyndromeProjector c η) (inv_mul_cancel₀ h4)
      rw [mul_smul, one_smul] at hmul
      rw [show (2 : ℂ) • cssSyndromeProjector c η = 0 from h3, smul_zero] at hmul
      exact hmul.symm
    exact absurd h5 hP

section OrthogonalKer

open LinearMap

variable {k : Type} [Field k] {m n : Type} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n]

def dotFun (y : m → k) : (m → k) →ₗ[k] k where
  toFun a := dotProduct a y
  map_add' _ _ := by simp only [add_dotProduct]
  map_smul' _ _ := by simp only [smul_dotProduct, RingHom.id_apply, smul_eq_mul]

omit [DecidableEq m] in
/-- The linear functional `dotFun y` evaluates as the dot product with `y`. -/
@[simp] theorem dotFun_apply [DecidableEq m] (y a : m → k) : dotFun y a = dotProduct a y := rfl

/-- Every linear functional on a finite coordinate space is represented by a dot product with a
vector. -/
theorem exists_dotProduct_repr (g : (n → k) →ₗ[k] k) :
    ∃ x' : n → k, ∀ w, g w = dotProduct x' w := by
  classical
  refine ⟨fun i => g (Pi.single i (1 : k)), fun w => ?_⟩
  conv_lhs => rw [pi_eq_sum_univ' w]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, dotProduct]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- A vector orthogonal to the kernel of the transposed matrix lies in the matrix range. -/
theorem exists_mulVec_eq_of_orthogonal_ker (M : Matrix m n k) (y : m → k)
    (h : ∀ a : m → k, Mᵀ *ᵥ a = 0 → dotProduct a y = 0) :
    ∃ x : n → k, M *ᵥ x = y := by
  classical
  have hker : LinearMap.ker (Matrix.mulVecLin Mᵀ) ≤ LinearMap.ker (dotFun y) := by
    intro a ha
    simp only [LinearMap.mem_ker, dotFun_apply] at ha ⊢
    exact h a ha
  obtain ⟨g, hg⟩ := LinearMap.exists_extend
    (((LinearMap.ker (Matrix.mulVecLin Mᵀ)).liftQ (dotFun y) hker).comp
      (LinearMap.quotKerEquivRange (Matrix.mulVecLin Mᵀ)).symm.toLinearMap)
  obtain ⟨x', hx'⟩ := exists_dotProduct_repr g
  have hsymm : ∀ a : m → k,
      (LinearMap.quotKerEquivRange (Matrix.mulVecLin Mᵀ)).symm
          ⟨Mᵀ *ᵥ a, LinearMap.mem_range_self _ a⟩ =
        (LinearMap.ker (Matrix.mulVecLin Mᵀ)).mkQ a :=
    fun a => LinearMap.quotKerEquivRange_symm_apply_image (Matrix.mulVecLin Mᵀ) a
      (LinearMap.mem_range_self _ a)
  have key : ∀ a : m → k, dotProduct a y = dotProduct x' (Mᵀ *ᵥ a) := by
    intro a
    have h5 := DFunLike.congr_fun hg ⟨Mᵀ *ᵥ a, LinearMap.mem_range_self _ a⟩
    have h6 : g (Mᵀ *ᵥ a) = dotProduct a y := by
      simpa only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_toLinearMap,
        hsymm a, Submodule.subtype_apply, Submodule.coe_mk, Submodule.mkQ_apply,
        Submodule.liftQ_apply, dotFun_apply] using h5
    exact h6.symm.trans (hx' (Mᵀ *ᵥ a))
  refine ⟨x', ?_⟩
  funext i
  have ki := key (Pi.single i (1 : k))
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.transpose_transpose,
    single_one_dotProduct, dotProduct_single_one] at ki
  exact ki.symm

end OrthogonalKer

omit [DecidableEq κX] [DecidableEq κZ] in

omit [Fintype κX] [DecidableEq ι] in
/-- Each binary matrix-vector product entry equals the bit dot product with the corresponding
row. -/
theorem mulVec_eq_bitDot [Fintype κX] [DecidableEq ι] (M : Matrix κX ι (ZMod 2)) (v : ι → ZMod 2) (i : κX) :
    (M *ᵥ v) i = bitDot v (M i) := by
  simp [Matrix.mulVec, dotProduct, bitDot, mul_comm]

/-- Commuting a Pauli X operator past a Pauli X-Z product introduces the phase given by its
overlap with the Z component. -/
theorem cssPauliX_check_conj (u x z : ι → ZMod 2) :
    cssPauliX u * (cssPauliX x * cssPauliZ z) =
      phaseOfBit (bitDot z u) • ((cssPauliX x * cssPauliZ z) * cssPauliX u) := by
  have hL : cssPauliX u * (cssPauliX x * cssPauliZ z) =
      cssPauliX (u + x) * cssPauliZ z := by
    rw [← mul_assoc, cssPauliX_mul]
  have hR : (cssPauliX x * cssPauliZ z) * cssPauliX u =
      phaseOfBit (bitDot z u) • (cssPauliX (x + u) * cssPauliZ z) := by
    rw [mul_assoc, cssPauliZX_phase, Matrix.mul_smul, ← mul_assoc, cssPauliX_mul]
  rw [hL, hR, smul_smul, phaseOfBit_mul_self, one_smul, add_comm]

/-- Commuting a Pauli Z operator past a Pauli X-Z product introduces the phase given by its
overlap with the X component. -/
theorem cssPauliZ_check_conj (v x z : ι → ZMod 2) :
    cssPauliZ v * (cssPauliX x * cssPauliZ z) =
      phaseOfBit (bitDot v x) • ((cssPauliX x * cssPauliZ z) * cssPauliZ v) := by
  have hL : cssPauliZ v * (cssPauliX x * cssPauliZ z) =
      phaseOfBit (bitDot v x) • (cssPauliX x * cssPauliZ (v + z)) := by
    rw [← mul_assoc, cssPauliZX_phase, Matrix.smul_mul, mul_assoc, cssPauliZ_mul]
  have hR : (cssPauliX x * cssPauliZ z) * cssPauliZ v =
      cssPauliX x * cssPauliZ (z + v) := by
    rw [mul_assoc, cssPauliZ_mul]
  rw [hL, hR, add_comm v z]

omit [DecidableEq κX] [DecidableEq κZ] in
/-- Commuting a CSS check past a Pauli product introduces the phase of the corresponding induced
syndrome bit. -/
theorem cssCheck_pauli_mul_comm [DecidableEq κX] [DecidableEq κZ] (c : CssData ι κX κZ) (x z : ι → ZMod 2)
    (k : κX ⊕ κZ) :
    cssCheck c k * (cssPauliX x * cssPauliZ z) =
      phaseOfBit (Sum.elim (c.hX *ᵥ z) (c.hZ *ᵥ x) k) •
        ((cssPauliX x * cssPauliZ z) * cssCheck c k) := by
  cases k with
  | inl i =>
    have h := cssPauliX_check_conj (c.hX i) x z
    simp only [cssCheck, Sum.elim_inl] at h ⊢
    rw [mulVec_eq_bitDot c.hX z i]
    exact h
  | inr j =>
    have h := cssPauliZ_check_conj (c.hZ j) x z
    simp only [cssCheck, Sum.elim_inr] at h ⊢
    rw [mulVec_eq_bitDot c.hZ x j, bitDot_comm]
    exact h

/-- A Pauli X-Z product multiplied by its phase-corrected copy is the identity. -/
theorem pauli_mul_square (x z : ι → ZMod 2) :
    (cssPauliX x * cssPauliZ z) * (phaseOfBit (bitDot z x) • (cssPauliX x * cssPauliZ z)) =
      1 := by
  rw [Matrix.mul_smul, pauli_square, smul_smul, phaseOfBit_mul_self, one_smul]

/-- A Pauli product with the prescribed syndrome sends every code vector to a vector fixed by
that syndrome projector. -/
theorem pauli_of_code_fixed (c : CssData ι κX κZ) (ηX : κX → ZMod 2) (ηZ : κZ → ZMod 2)
    (x z : ι → ZMod 2) (hxzX : c.hX *ᵥ z = ηX) (hxzZ : c.hZ *ᵥ x = ηZ)
    (w : (ι → ZMod 2) → ℂ) (hw : w ∈ cssCodespace c) :
    cssSyndromeProjector c (ηX, ηZ) *ᵥ
      ((cssPauliX x * cssPauliZ z) *ᵥ w) = (cssPauliX x * cssPauliZ z) *ᵥ w := by
  classical
  have hcheck : ∀ k : κX ⊕ κZ, cssCheck c k *ᵥ w = w := by
    have hmem := (mem_cssCodespace_iff c w).mp hw
    intro k
    cases k with
    | inl i => simpa only [cssCheck, Sum.elim_inl] using hmem.1 i
    | inr j => simpa only [cssCheck, Sum.elim_inr] using hmem.2 j
  have hsyn : Sum.elim (c.hX *ᵥ z) (c.hZ *ᵥ x) = Sum.elim ηX ηZ := by
    rw [hxzX, hxzZ]
  apply (cssSyndromeProjector_fixed_iff c (ηX, ηZ) _).mpr
  intro k
  rw [Matrix.mulVec_mulVec, cssCheck_pauli_mul_comm, Matrix.smul_mulVec,
    ← Matrix.mulVec_mulVec, hcheck k, hsyn]

/-- The phase-corrected inverse Pauli action sends a vector fixed by the syndrome projector into
the codespace. -/
theorem pauli_inv_of_fixed_mem_code (c : CssData ι κX κZ) (ηX : κX → ZMod 2)
    (ηZ : κZ → ZMod 2) (x z : ι → ZMod 2) (hxzX : c.hX *ᵥ z = ηX) (hxzZ : c.hZ *ᵥ x = ηZ)
    (v : (ι → ZMod 2) → ℂ) (hv : cssSyndromeProjector c (ηX, ηZ) *ᵥ v = v) :
    phaseOfBit (bitDot z x) • ((cssPauliX x * cssPauliZ z) *ᵥ v) ∈ cssCodespace c := by
  classical
  have hfix : ∀ k : κX ⊕ κZ, cssCheck c k *ᵥ v =
      phaseOfBit (Sum.elim ηX ηZ k) • v :=
    (cssSyndromeProjector_fixed_iff c (ηX, ηZ) v).mp hv
  rw [mem_cssCodespace_iff]
  constructor
  · intro i
    have hk := hfix (Sum.inl i)
    have hconj := cssCheck_pauli_mul_comm c x z (Sum.inl i)
    simp only [cssCheck, Sum.elim_inl] at hk hconj
    rw [congrFun hxzX i] at hconj
    show cssPauliX (c.hX i) *ᵥ
        (phaseOfBit (bitDot z x) • (cssPauliX x * cssPauliZ z) *ᵥ v) = _
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hconj, Matrix.smul_mulVec,
      ← Matrix.mulVec_mulVec, hk, Matrix.mulVec_smul, smul_smul, smul_smul, mul_assoc,
      phaseOfBit_mul_self, mul_one]
  · intro j
    have hk := hfix (Sum.inr j)
    have hconj := cssCheck_pauli_mul_comm c x z (Sum.inr j)
    simp only [cssCheck, Sum.elim_inr] at hk hconj
    rw [congrFun hxzZ j] at hconj
    show cssPauliZ (c.hZ j) *ᵥ
        (phaseOfBit (bitDot z x) • (cssPauliX x * cssPauliZ z) *ᵥ v) = _
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hconj, Matrix.smul_mulVec,
      ← Matrix.mulVec_mulVec, hk, Matrix.mulVec_smul, smul_smul, smul_smul, mul_assoc,
      phaseOfBit_mul_self, mul_one]

/-- Every nonzero syndrome sector has a Pauli representative and finite syndrome weight, and is
the Pauli image of the codespace. -/
theorem everyConsistentSyndromeRealized :
    ∀ {ι κX κZ : Type} [Fintype ι] [Fintype κX] [Fintype κZ]
      [DecidableEq ι] [DecidableEq κX] [DecidableEq κZ]
      (c : CssData ι κX κZ) (ηX : κX → ZMod 2) (ηZ : κZ → ZMod 2),
      cssSyndromeProjector c (ηX, ηZ) ≠ 0 →
      (∃ (x z : ι → ZMod 2), c.hX *ᵥ z = ηX ∧ c.hZ *ᵥ x = ηZ) ∧
      cssSyndromeWeight c ηX ηZ ≠ ⊤ ∧
      ∀ (x z : ι → ZMod 2), c.hX *ᵥ z = ηX → c.hZ *ᵥ x = ηZ →
        LinearMap.range (Matrix.mulVecLin (cssSyndromeProjector c (ηX, ηZ))) =
          Submodule.map (Matrix.mulVecLin (cssPauliX x * cssPauliZ z))
            (cssCodespace c) := by
  intro ι' κX' κZ' _ _ _ _ _ _ c ηX ηZ hP
  classical
  have hz : ∃ z : ι' → ZMod 2, c.hX *ᵥ z = ηX := by
    apply exists_mulVec_eq_of_orthogonal_ker
    intro a ha
    exact syndrome_consistent_X c (ηX, ηZ) a hP ha
  have hx : ∃ x : ι' → ZMod 2, c.hZ *ᵥ x = ηZ := by
    apply exists_mulVec_eq_of_orthogonal_ker
    intro a ha
    exact syndrome_consistent_Z c (ηX, ηZ) a hP ha
  obtain ⟨z, hz'⟩ := hz
  obtain ⟨x, hx'⟩ := hx
  refine ⟨⟨x, z, hz', hx'⟩, ?_, ?_⟩
  · intro htop
    have hle : cssSyndromeWeight c ηX ηZ ≤ ((pauliWeight x z : ℕ) : ℕ∞) :=
      sInf_le ⟨x, z, hz', hx', rfl⟩
    rw [htop] at hle
    exact absurd hle (not_le.2 (ENat.natCast_lt_top _))
  · intro x z hxzX hxzZ
    apply le_antisymm
    · intro v hv
      obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hv
      have hidem : cssSyndromeProjector c (ηX, ηZ) * cssSyndromeProjector c (ηX, ηZ) =
          cssSyndromeProjector c (ηX, ηZ) := by
        rw [cssSyndromeProjector_mul, ite_eq_left rfl]
      have hfix : cssSyndromeProjector c (ηX, ηZ) *ᵥ
          (cssSyndromeProjector c (ηX, ηZ) *ᵥ u) = cssSyndromeProjector c (ηX, ηZ) *ᵥ u := by
        rw [Matrix.mulVec_mulVec, hidem]
      have hmem := pauli_inv_of_fixed_mem_code c ηX ηZ x z hxzX hxzZ _ hfix
      refine Submodule.mem_map.mpr ⟨_, hmem, ?_⟩
      show (cssPauliX x * cssPauliZ z) *ᵥ
        (phaseOfBit (bitDot z x) • (cssPauliX x * cssPauliZ z) *ᵥ
          (cssSyndromeProjector c (ηX, ηZ) *ᵥ u)) = _
      rw [Matrix.mulVec_smul,
        Matrix.mulVec_mulVec (cssSyndromeProjector c (ηX, ηZ) *ᵥ u)
          (cssPauliX x * cssPauliZ z) (cssPauliX x * cssPauliZ z),
        pauli_square, Matrix.smul_mulVec, Matrix.one_mulVec, smul_smul, phaseOfBit_mul_self,
        one_smul]
      exact (Matrix.mulVecLin_apply _ _).symm
    · intro v hv
      obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
      exact ⟨_, pauli_of_code_fixed c ηX ηZ x z hxzX hxzZ w hw⟩

end Qatlib.Concepts.CodingDecoding.CssTesters.EveryConsistentSyndromeRealized
