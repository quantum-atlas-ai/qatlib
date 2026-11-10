/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Ext
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.SimpRw
import Qatlib.Concepts.CodingDecoding.CssTesters.CssCode
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode

open Qatlib.Concepts.CodingDecoding.CssTesters

namespace Qatlib.Concepts.CodingDecoding.CssTesters.CssTester

open Matrix

open scoped ComplexOrder

variable {ι κX κZ : Type*} [Fintype ι] [Fintype κX] [Fintype κZ] [DecidableEq ι]
  [DecidableEq κX] [DecidableEq κZ]

def cssCheck (c : CssData ι κX κZ) :
    (κX ⊕ κZ) → Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ :=
  Sum.elim (fun i => cssPauliX (c.hX i)) (fun j => cssPauliZ (c.hZ j))

noncomputable def cssCheckProjector (S : Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ) (b : ZMod 2) :
    Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ :=
  (2⁻¹ : ℂ) • (1 + phaseOfBit b • S)

noncomputable def cssSyndromeProjector (c : CssData ι κX κZ)
    (η : (κX → ZMod 2) × (κZ → ZMod 2)) :
    Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ :=
  (Finset.univ.toList.map fun k =>
    cssCheckProjector (cssCheck c k) (Sum.elim η.1 η.2 k)).prod

noncomputable def cssSyndromeWeight (c : CssData ι κX κZ)
    (ηX : κX → ZMod 2) (ηZ : κZ → ZMod 2) : ℕ∞ :=
  sInf {w : ℕ∞ | ∃ (x z : ι → ZMod 2), c.hX *ᵥ z = ηX ∧ c.hZ *ᵥ x = ηZ ∧
    (pauliWeight x z : ℕ∞) = w}

noncomputable def cssNeighborhood (c : CssData ι κX κZ) (ℓ : ℕ) :
    Submodule ℂ ((ι → ZMod 2) → ℂ) :=
  Submodule.span ℂ
    {v | ∃ (x z : ι → ZMod 2) (w : cssCodespace c), pauliWeight x z ≤ ℓ ∧
      v = (cssPauliX x * cssPauliZ z) *ᵥ (w : (ι → ZMod 2) → ℂ)}

noncomputable def cssNeighborhoodProjector (c : CssData ι κX κZ) (ℓ : ℕ) :
    Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ :=
  ∑ η ∈ Finset.univ.filter
      fun η : (κX → ZMod 2) × (κZ → ZMod 2) =>
        cssSyndromeWeight c η.1 η.2 ≤ (ℓ : ℕ∞),
    cssSyndromeProjector c η

noncomputable def cssDistanceOperator (c : CssData ι κX κZ) :
    Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ :=
  ∑ ℓ ∈ Finset.range (Fintype.card ι + 1),
    (ℓ : ℂ) • (cssNeighborhoodProjector c ℓ -
      (if ℓ = 0 then 0 else cssNeighborhoodProjector c (ℓ - 1)))

noncomputable def cssTester (c : CssData ι κX κZ) : Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ :=
  ((Fintype.card (κX ⊕ κZ) : ℕ) : ℂ)⁻¹ •
    ∑ k ∈ Finset.univ, cssCheckProjector (cssCheck c k) 1

def cssHasSoundnessAtLeast (c : CssData ι κX κZ) (σ : ℝ) : Prop :=
  (cssTester c - ((σ / (Fintype.card ι : ℝ) : ℂ) • cssDistanceOperator c)).PosSemidef

private theorem cssCheck_square (c : CssData ι κX κZ) (k : κX ⊕ κZ) :
    cssCheck c k * cssCheck c k = 1 := by
  cases k with
  | inl i => exact cssPauliX_self_mul (c.hX i)
  | inr j => exact cssPauliZ_self_mul (c.hZ j)

private theorem cssCheck_hermitian (c : CssData ι κX κZ) (k : κX ⊕ κZ) :
    (cssCheck c k).IsHermitian := by
  cases k with
  | inl i => exact cssPauliX_isHermitian (c.hX i)
  | inr j => exact cssPauliZ_isHermitian (c.hZ j)

private theorem css_check_cross (c : CssData ι κX κZ) (i : κX) (j : κZ) :
    cssPauliX (c.hX i) * cssPauliZ (c.hZ j) = cssPauliZ (c.hZ j) * cssPauliX (c.hX i) := by
  have h : bitDot (c.hX i) (c.hZ j) = 0 := by
    simpa [bitDot, dotProduct, Matrix.mul_apply] using congrFun (congrFun c.hcompat i) j
  rw [cssPauliXZ_comm, bitDot_comm, h, phaseOfBit_zero, one_smul]

private theorem cssCheck_commute (c : CssData ι κX κZ) (k k' : κX ⊕ κZ) :
    Commute (cssCheck c k) (cssCheck c k') := by
  change cssCheck c k * cssCheck c k' = cssCheck c k' * cssCheck c k
  cases k with
  | inl i =>
    cases k' with
    | inl i' => simpa only [cssCheck, Sum.elim_inl, cssPauliX_mul, add_comm] using
        (rfl : cssPauliX (c.hX i + c.hX i') = cssPauliX (c.hX i + c.hX i'))
    | inr j => exact css_check_cross c i j
  | inr j =>
    cases k' with
    | inl i => exact (css_check_cross c i j).symm
    | inr j' => simpa only [cssCheck, Sum.elim_inr, cssPauliZ_mul, add_comm] using
        (rfl : cssPauliZ (c.hZ j + c.hZ j') = cssPauliZ (c.hZ j + c.hZ j'))

private theorem cssCheckProjector_add (S : Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ) :
    cssCheckProjector S 0 + cssCheckProjector S 1 = 1 := by
  simp only [cssCheckProjector, phaseOfBit_zero, phaseOfBit_one, one_smul, neg_one_smul]
  module

private theorem cssCheckProjector_hermitian
    (S : Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ) (hS : S.IsHermitian) (b : ZMod 2) :
    (cssCheckProjector S b).IsHermitian := by
  exact (Matrix.isHermitian_one.add (hS.smul (phaseOfBit_star b))).smul (by simp)

private theorem cssCheckProjector_mul
    (S : Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ) (hS : S * S = 1) (b b' : ZMod 2) :
    cssCheckProjector S b * cssCheckProjector S b' =
      if b = b' then cssCheckProjector S b else 0 := by
  have hc : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases hc b with rfl | rfl <;> rcases hc b' with rfl | rfl <;>
    simp only [cssCheckProjector, phaseOfBit_zero, phaseOfBit_one, one_smul, neg_one_smul,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, add_mul, mul_add, neg_mul, mul_neg,
      neg_neg, one_mul, mul_one, hS] <;> norm_num <;> module

private noncomputable def cssCheckAlgebra (c : CssData ι κX κZ) :
    Subalgebra ℂ (Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ) :=
  Algebra.adjoin ℂ (Set.range (cssCheck c))

private instance cssCheckAlgebra_commutative (c : CssData ι κX κZ) :
    IsMulCommutative (cssCheckAlgebra c) :=
  Algebra.isMulCommutative_adjoin ℂ (by
    rintro _ ⟨k, rfl⟩ _ ⟨k', rfl⟩ _
    exact cssCheck_commute c k k')

open scoped IsMulCommutative

private noncomputable def cssCheckAlgebraProjector (c : CssData ι κX κZ)
    (k : κX ⊕ κZ) (b : ZMod 2) : cssCheckAlgebra c :=
  ⟨cssCheckProjector (cssCheck c k) b, by
    apply (cssCheckAlgebra c).smul_mem
    apply (cssCheckAlgebra c).add_mem (cssCheckAlgebra c).one_mem
    apply (cssCheckAlgebra c).smul_mem
    exact Algebra.subset_adjoin ⟨k, rfl⟩⟩

private noncomputable def cssAlgebraSyndromeProjector (c : CssData ι κX κZ)
    (η : (κX → ZMod 2) × (κZ → ZMod 2)) : cssCheckAlgebra c :=
  ∏ k : κX ⊕ κZ, cssCheckAlgebraProjector c k (Sum.elim η.1 η.2 k)

private theorem cssAlgebraSyndromeProjector_coe (c : CssData ι κX κZ)
    (η : (κX → ZMod 2) × (κZ → ZMod 2)) :
    (cssAlgebraSyndromeProjector c η : Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ) =
      cssSyndromeProjector c η := by
  unfold cssAlgebraSyndromeProjector
  rw [← Finset.prod_map_toList]
  change (cssCheckAlgebra c).val _ = _
  rw [map_list_prod]
  simp [cssSyndromeProjector, cssCheckAlgebraProjector, List.map_map, Function.comp_def]

private theorem sum_binary_values {R : Type*} [AddCommMonoid R] (f : ZMod 2 → R) :
    (∑ b : ZMod 2, f b) = f 0 + f 1 := by
  have hs : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  rw [hs]
  simp [show (0 : ZMod 2) ≠ 1 from by decide]

private theorem cssCheckAlgebraProjector_sum (c : CssData ι κX κZ) (k : κX ⊕ κZ) :
    (∑ b : ZMod 2, cssCheckAlgebraProjector c k b) = 1 := by
  rw [sum_binary_values]
  apply Subtype.ext
  exact cssCheckProjector_add (cssCheck c k)

private theorem cssAlgebraSyndromeProjector_sum (c : CssData ι κX κZ) :
    (∑ η : (κX → ZMod 2) × (κZ → ZMod 2), cssAlgebraSyndromeProjector c η) = 1 := by
  classical
  let e : ((κX → ZMod 2) × (κZ → ZMod 2)) ≃ ((κX ⊕ κZ) → ZMod 2) :=
    { toFun := fun η => Sum.elim η.1 η.2
      invFun := fun f => ((fun i => f (Sum.inl i)), (fun j => f (Sum.inr j)))
      left_inv := fun _ => rfl
      right_inv := fun f => by funext k; cases k <;> rfl }
  have he := e.sum_comp (fun f => ∏ k : κX ⊕ κZ, cssCheckAlgebraProjector c k (f k))
  change (∑ η, ∏ k : κX ⊕ κZ, cssCheckAlgebraProjector c k (e η k)) = 1
  rw [he, ← Fintype.prod_sum]
  simp_rw [cssCheckAlgebraProjector_sum]
  simp

theorem cssSyndromeProjector_sum (c : CssData ι κX κZ) :
    ∑ η ∈ Finset.univ, cssSyndromeProjector c η = 1 := by
  have h := congrArg (cssCheckAlgebra c).val (cssAlgebraSyndromeProjector_sum c)
  rw [map_sum, map_one] at h
  change (∑ η, (cssAlgebraSyndromeProjector c η : Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ)) = 1 at h
  simpa only [cssAlgebraSyndromeProjector_coe] using h

private theorem cssCheckAlgebraProjector_mul (c : CssData ι κX κZ) (k : κX ⊕ κZ)
    (b b' : ZMod 2) :
    cssCheckAlgebraProjector c k b * cssCheckAlgebraProjector c k b' =
      if b = b' then cssCheckAlgebraProjector c k b else 0 := by
  apply Subtype.ext
  simpa only [cssCheckAlgebraProjector, Subalgebra.coe_mul, apply_ite Subtype.val,
    Subalgebra.coe_zero] using cssCheckProjector_mul (cssCheck c k) (cssCheck_square c k) b b'

private theorem cssAlgebraSyndromeProjector_mul (c : CssData ι κX κZ)
    (η η' : (κX → ZMod 2) × (κZ → ZMod 2)) :
    cssAlgebraSyndromeProjector c η * cssAlgebraSyndromeProjector c η' =
      if η = η' then cssAlgebraSyndromeProjector c η else 0 := by
  classical
  by_cases h : η = η'
  · subst η'
    simp only [cssAlgebraSyndromeProjector, ← Finset.prod_mul_distrib,
      cssCheckAlgebraProjector_mul, ite_true]
  · rw [if_neg h]
    unfold cssAlgebraSyndromeProjector
    rw [← Finset.prod_mul_distrib]
    have hk : ∃ k, Sum.elim η.1 η.2 k ≠ Sum.elim η'.1 η'.2 k := by
      by_contra hn
      push Not at hn
      apply h
      apply Prod.ext
      · funext i
        exact hn (Sum.inl i)
      · funext j
        exact hn (Sum.inr j)
    obtain ⟨k, hk⟩ := hk
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    rw [cssCheckAlgebraProjector_mul, if_neg hk]

theorem cssSyndromeProjector_mul (c : CssData ι κX κZ)
    (η η' : (κX → ZMod 2) × (κZ → ZMod 2)) :
    cssSyndromeProjector c η * cssSyndromeProjector c η' =
      if η = η' then cssSyndromeProjector c η else 0 := by
  have h := congrArg (cssCheckAlgebra c).val (cssAlgebraSyndromeProjector_mul c η η')
  rw [map_mul] at h
  simp only [apply_ite (cssCheckAlgebra c).val, map_zero] at h
  change (cssAlgebraSyndromeProjector c η : Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ) *
    (cssAlgebraSyndromeProjector c η' : Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ) =
      if η = η' then (cssAlgebraSyndromeProjector c η : Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ) else 0 at h
  simpa only [cssAlgebraSyndromeProjector_coe] using h

theorem cssNeighborhoodProjector_idem (c : CssData ι κX κZ) (ℓ : ℕ) :
    cssNeighborhoodProjector c ℓ * cssNeighborhoodProjector c ℓ = cssNeighborhoodProjector c ℓ := by
  classical
  unfold cssNeighborhoodProjector
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum, cssSyndromeProjector_mul]
  simp
  apply Finset.sum_congr rfl
  intro η hη
  rw [if_pos (Finset.mem_filter.mp hη).2]

private theorem cssCheckAlgebraProjector_absorb (c : CssData ι κX κZ)
    (η : (κX → ZMod 2) × (κZ → ZMod 2)) (k : κX ⊕ κZ) :
    cssCheckAlgebraProjector c k (Sum.elim η.1 η.2 k) * cssAlgebraSyndromeProjector c η =
      cssAlgebraSyndromeProjector c η := by
  classical
  unfold cssAlgebraSyndromeProjector
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
  rw [← mul_assoc, cssCheckAlgebraProjector_mul, if_pos rfl]

private theorem cssCheckProjector_absorb (c : CssData ι κX κZ)
    (η : (κX → ZMod 2) × (κZ → ZMod 2)) (k : κX ⊕ κZ) :
    cssCheckProjector (cssCheck c k) (Sum.elim η.1 η.2 k) * cssSyndromeProjector c η =
      cssSyndromeProjector c η := by
  have h := congrArg (cssCheckAlgebra c).val (cssCheckAlgebraProjector_absorb c η k)
  rw [map_mul] at h
  change cssCheckProjector (cssCheck c k) (Sum.elim η.1 η.2 k) *
      (cssAlgebraSyndromeProjector c η : Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ) =
        (cssAlgebraSyndromeProjector c η : Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ) at h
  simpa only [cssAlgebraSyndromeProjector_coe] using h

private theorem cssCheckProjector_fixed_iff
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

private theorem list_prod_fixed
    (l : List (Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ)) (v : (ι → ZMod 2) → ℂ)
    (h : ∀ S ∈ l, S *ᵥ v = v) : l.prod *ᵥ v = v := by
  induction l with
  | nil => simp
  | cons S l ih =>
    rw [List.prod_cons, ← Matrix.mulVec_mulVec, ih (fun T hT => h T (List.mem_cons_of_mem _ hT)),
      h S (by simp)]

private theorem cssSyndromeProjector_fixed_iff (c : CssData ι κX κZ)
    (η : (κX → ZMod 2) × (κZ → ZMod 2)) (v : (ι → ZMod 2) → ℂ) :
    cssSyndromeProjector c η *ᵥ v = v ↔
      ∀ k : κX ⊕ κZ, cssCheck c k *ᵥ v = phaseOfBit (Sum.elim η.1 η.2 k) • v := by
  constructor
  · intro h k
    apply (cssCheckProjector_fixed_iff _ _ _).mp
    rw [← h, Matrix.mulVec_mulVec, cssCheckProjector_absorb, h]
  · intro h
    unfold cssSyndromeProjector
    apply list_prod_fixed
    intro S hS
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hS
    exact (cssCheckProjector_fixed_iff _ _ _).mpr (h k)

private theorem mem_cssCodespace_check_iff (c : CssData ι κX κZ) (v : (ι → ZMod 2) → ℂ) :
    v ∈ cssCodespace c ↔ ∀ k : κX ⊕ κZ, cssCheck c k *ᵥ v = v := by
  simp [cssCodespace, cssXStabilized, cssZStabilized, cssXCheckKernel, cssZCheckKernel,
    cssCheck, sub_eq_zero, Sum.forall]

private theorem cssSyndromeWeight_witness_le (c : CssData ι κX κZ)
    (η : (κX → ZMod 2) × (κZ → ZMod 2)) (ℓ : ℕ)
    (h : cssSyndromeWeight c η.1 η.2 ≤ (ℓ : ℕ∞)) :
    ∃ (x z : ι → ZMod 2), c.hX *ᵥ z = η.1 ∧ c.hZ *ᵥ x = η.2 ∧ pauliWeight x z ≤ ℓ := by
  classical
  let S : Set ℕ∞ := {w | ∃ (x z : ι → ZMod 2), c.hX *ᵥ z = η.1 ∧
    c.hZ *ᵥ x = η.2 ∧ (pauliWeight x z : ℕ∞) = w}
  change sInf S ≤ (ℓ : ℕ∞) at h
  have hs : S.Nonempty := by
    by_contra hn
    rw [Set.not_nonempty_iff_eq_empty.mp hn, sInf_empty] at h
    simp at h
  obtain ⟨x, z, hx, hz, hw⟩ := csInf_mem hs
  refine ⟨x, z, hx, hz, ?_⟩
  have hh : (pauliWeight x z : ℕ∞) ≤ (ℓ : ℕ∞) := by rw [hw]; exact h
  exact_mod_cast hh

private theorem pauliError_square (x z : ι → ZMod 2) :
    (cssPauliX x * cssPauliZ z) * (cssPauliX x * cssPauliZ z) = phaseOfBit (bitDot z x) • 1 := by
  rw [cssPauliXZ_mul, binary_add_self, binary_add_self, cssPauliX_zero, cssPauliZ_zero, one_mul]

private noncomputable def pauliErrorInverse (x z : ι → ZMod 2) :
    Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ := phaseOfBit (bitDot z x) • (cssPauliX x * cssPauliZ z)

private theorem pauliError_mul_inverse (x z : ι → ZMod 2) :
    (cssPauliX x * cssPauliZ z) * pauliErrorInverse x z = 1 := by
  rw [pauliErrorInverse, Matrix.mul_smul, pauliError_square, smul_smul,
    phaseOfBit_mul_self, one_smul]

private theorem pauliError_inverse_mul (x z : ι → ZMod 2) :
    pauliErrorInverse x z * (cssPauliX x * cssPauliZ z) = 1 := by
  rw [pauliErrorInverse, Matrix.smul_mul, pauliError_square, smul_smul,
    phaseOfBit_mul_self, one_smul]

private theorem cssCheck_pauli_mul (c : CssData ι κX κZ) (x z : ι → ZMod 2) (k : κX ⊕ κZ) :
    cssCheck c k * (cssPauliX x * cssPauliZ z) =
      phaseOfBit (Sum.elim (c.hX *ᵥ z) (c.hZ *ᵥ x) k) •
        ((cssPauliX x * cssPauliZ z) * cssCheck c k) := by
  cases k with
  | inl i =>
    have he : cssCheck c (Sum.inl i) = cssPauliX (c.hX i) * cssPauliZ 0 := by simp [cssCheck]
    have hd : bitDot z (c.hX i) = (c.hX *ᵥ z) i := by rw [bitDot_comm]; rfl
    rw [he, cssPauliXZ_mul, cssPauliXZ_mul]
    simp only [Sum.elim_inl, bitDot_zero_left, phaseOfBit_zero, one_smul, zero_add,
      add_zero, hd, smul_smul, phaseOfBit_mul_self]
    rw [add_comm]
  | inr j =>
    have he : cssCheck c (Sum.inr j) = cssPauliX 0 * cssPauliZ (c.hZ j) := by simp [cssCheck]
    rw [he, cssPauliXZ_mul, cssPauliXZ_mul]
    change _ = phaseOfBit (bitDot (c.hZ j) x) • _
    simp only [bitDot_zero_right, phaseOfBit_zero, one_smul, zero_add, add_zero]
    rw [add_comm]

private theorem cssCheck_pauli_inverse (c : CssData ι κX κZ) (x z : ι → ZMod 2) (k : κX ⊕ κZ) :
    cssCheck c k * pauliErrorInverse x z =
      phaseOfBit (Sum.elim (c.hX *ᵥ z) (c.hZ *ᵥ x) k) •
        (pauliErrorInverse x z * cssCheck c k) := by
  rw [pauliErrorInverse, Matrix.mul_smul, cssCheck_pauli_mul, Matrix.smul_mul, smul_smul,
    smul_smul]
  rw [mul_comm]

private theorem pauliError_syndrome_of_code (c : CssData ι κX κZ) (x z : ι → ZMod 2)
    (w : (ι → ZMod 2) → ℂ) (hw : w ∈ cssCodespace c) :
    ∀ k : κX ⊕ κZ, cssCheck c k *ᵥ ((cssPauliX x * cssPauliZ z) *ᵥ w) =
      phaseOfBit (Sum.elim (c.hX *ᵥ z) (c.hZ *ᵥ x) k) • ((cssPauliX x * cssPauliZ z) *ᵥ w) := by
  intro k
  rw [Matrix.mulVec_mulVec, cssCheck_pauli_mul, Matrix.smul_mulVec,
    ← Matrix.mulVec_mulVec, (mem_cssCodespace_check_iff c w).mp hw k]

private theorem pauliError_preimage_in_code (c : CssData ι κX κZ) (x z : ι → ZMod 2)
    (v : (ι → ZMod 2) → ℂ)
    (hv : ∀ k : κX ⊕ κZ, cssCheck c k *ᵥ v =
      phaseOfBit (Sum.elim (c.hX *ᵥ z) (c.hZ *ᵥ x) k) • v) :
    pauliErrorInverse x z *ᵥ v ∈ cssCodespace c := by
  apply (mem_cssCodespace_check_iff _ _).mpr
  intro k
  rw [Matrix.mulVec_mulVec, cssCheck_pauli_inverse, Matrix.smul_mulVec,
    ← Matrix.mulVec_mulVec, hv k, Matrix.mulVec_smul, smul_smul, phaseOfBit_mul_self, one_smul]

private theorem cssNeighborhoodProjector_mul_syndrome (c : CssData ι κX κZ) (ℓ : ℕ)
    (η : (κX → ZMod 2) × (κZ → ZMod 2)) :
    cssNeighborhoodProjector c ℓ * cssSyndromeProjector c η =
      if cssSyndromeWeight c η.1 η.2 ≤ (ℓ : ℕ∞) then cssSyndromeProjector c η else 0 := by
  classical
  unfold cssNeighborhoodProjector
  rw [Finset.sum_mul]
  simp_rw [cssSyndromeProjector_mul]
  simp

theorem cssNeighborhoodProjector_range (c : CssData ι κX κZ) (ℓ : ℕ) :
    LinearMap.range (Matrix.mulVecLin (cssNeighborhoodProjector c ℓ)) = cssNeighborhood c ℓ := by
  classical
  apply le_antisymm
  · rintro v ⟨u, rfl⟩
    change cssNeighborhoodProjector c ℓ *ᵥ u ∈ cssNeighborhood c ℓ
    unfold cssNeighborhoodProjector
    rw [Matrix.sum_mulVec]
    apply Submodule.sum_mem
    intro η hη
    have hh := (Finset.mem_filter.mp hη).2
    obtain ⟨x, z, hx, hz, hw⟩ := cssSyndromeWeight_witness_le c η ℓ hh
    let vη := cssSyndromeProjector c η *ᵥ u
    have hf : cssSyndromeProjector c η *ᵥ vη = vη := by
      rw [Matrix.mulVec_mulVec, cssSyndromeProjector_mul, if_pos rfl]
    have he : ∀ k : κX ⊕ κZ, cssCheck c k *ᵥ vη =
        phaseOfBit (Sum.elim (c.hX *ᵥ z) (c.hZ *ᵥ x) k) • vη := by
      simpa only [hx, hz] using (cssSyndromeProjector_fixed_iff c η vη).mp hf
    let w := pauliErrorInverse x z *ᵥ vη
    have hc : w ∈ cssCodespace c := pauliError_preimage_in_code c x z vη he
    have hev : (cssPauliX x * cssPauliZ z) *ᵥ w = vη := by
      rw [Matrix.mulVec_mulVec, pauliError_mul_inverse, Matrix.one_mulVec]
    exact Submodule.subset_span ⟨x, z, ⟨w, hc⟩, hw, hev.symm⟩
  · unfold cssNeighborhood
    apply Submodule.span_le.mpr
    rintro v ⟨x, z, w, hw, rfl⟩
    let η : (κX → ZMod 2) × (κZ → ZMod 2) := (c.hX *ᵥ z, c.hZ *ᵥ x)
    have hew : cssSyndromeWeight c η.1 η.2 ≤ (pauliWeight x z : ℕ∞) :=
      sInf_le ⟨x, z, rfl, rfl, rfl⟩
    have hη : cssSyndromeWeight c η.1 η.2 ≤ (ℓ : ℕ∞) :=
      hew.trans (by exact_mod_cast hw)
    have hf : cssSyndromeProjector c η *ᵥ ((cssPauliX x * cssPauliZ z) *ᵥ (w : (ι → ZMod 2) → ℂ)) =
        (cssPauliX x * cssPauliZ z) *ᵥ (w : (ι → ZMod 2) → ℂ) :=
      (cssSyndromeProjector_fixed_iff _ _ _).mpr (pauliError_syndrome_of_code c x z w w.property)
    refine ⟨(cssPauliX x * cssPauliZ z) *ᵥ (w : (ι → ZMod 2) → ℂ), ?_⟩
    change cssNeighborhoodProjector c ℓ *ᵥ
        ((cssPauliX x * cssPauliZ z) *ᵥ (w : (ι → ZMod 2) → ℂ)) = _
    rw [← hf, Matrix.mulVec_mulVec, cssNeighborhoodProjector_mul_syndrome, if_pos hη, hf]

private theorem cssCheck_mul_syndrome (c : CssData ι κX κZ)
    (η : (κX → ZMod 2) × (κZ → ZMod 2)) (k : κX ⊕ κZ) :
    cssCheck c k * cssSyndromeProjector c η =
      phaseOfBit (Sum.elim η.1 η.2 k) • cssSyndromeProjector c η := by
  have hcol (b : ι → ZMod 2) :
      cssCheckProjector (cssCheck c k) (Sum.elim η.1 η.2 k) *ᵥ
        (fun a => cssSyndromeProjector c η a b) = (fun a => cssSyndromeProjector c η a b) := by
    ext a
    change (cssCheckProjector (cssCheck c k) (Sum.elim η.1 η.2 k) * cssSyndromeProjector c η) a b = _
    rw [cssCheckProjector_absorb]
  ext a b
  exact congrFun ((cssCheckProjector_fixed_iff _ _ _).mp (hcol b)) a

private theorem cssReject_mul_syndrome (c : CssData ι κX κZ)
    (η : (κX → ZMod 2) × (κZ → ZMod 2)) (k : κX ⊕ κZ) :
    cssCheckProjector (cssCheck c k) 1 * cssSyndromeProjector c η =
      if Sum.elim η.1 η.2 k = 1 then cssSyndromeProjector c η else 0 := by
  rw [cssCheckProjector, Matrix.smul_mul, Matrix.add_mul, Matrix.smul_mul, one_mul,
    cssCheck_mul_syndrome, phaseOfBit_one, smul_smul]
  by_cases h : Sum.elim η.1 η.2 k = 1 <;> simp only [phaseOfBit, h, if_true, if_false] <;> module

private theorem cssSyndrome_check_count (η : (κX → ZMod 2) × (κZ → ZMod 2)) :
    ((Finset.univ : Finset (κX ⊕ κZ)).filter (fun k => Sum.elim η.1 η.2 k = 1)).card =
      bitWeight η.1 + bitWeight η.2 := by
  have hb : ∀ b : ZMod 2, b ≠ 0 ↔ b = 1 := by decide
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  simp only [bitWeight, hb, Finset.card_eq_sum_ones, Finset.sum_filter]

private theorem cssTester_mul_syndrome (c : CssData ι κX κZ)
    (η : (κX → ZMod 2) × (κZ → ZMod 2)) :
    cssTester c * cssSyndromeProjector c η =
      (((bitWeight η.1 + bitWeight η.2 : ℕ) : ℂ) / (Fintype.card (κX ⊕ κZ) : ℂ)) •
        cssSyndromeProjector c η := by
  classical
  unfold cssTester
  rw [Matrix.smul_mul, Finset.sum_mul]
  simp_rw [cssReject_mul_syndrome]
  rw [← Finset.sum_filter, Finset.sum_const, cssSyndrome_check_count,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  congr 1
  rw [div_eq_mul_inv, mul_comm]

theorem cssTester_eq_syndrome (c : CssData ι κX κZ) :
    cssTester c = ∑ η ∈ Finset.univ,
      (((bitWeight η.1 + bitWeight η.2 : ℕ) : ℂ) / (Fintype.card (κX ⊕ κZ) : ℂ)) •
        cssSyndromeProjector c η := by
  calc
    cssTester c = cssTester c * 1 := (mul_one _).symm
    _ = cssTester c * (∑ η ∈ Finset.univ, cssSyndromeProjector c η) := by
      rw [cssSyndromeProjector_sum]
    _ = _ := by
      rw [Finset.mul_sum]
      simp_rw [cssTester_mul_syndrome]

private theorem pauliWeight_le_card (x z : ι → ZMod 2) : pauliWeight x z ≤ Fintype.card ι := by
  exact (Finset.card_filter_le _ _).trans_eq Finset.card_univ

private theorem cssSyndromeWeight_top_or_le (c : CssData ι κX κZ)
    (η : (κX → ZMod 2) × (κZ → ZMod 2)) :
    cssSyndromeWeight c η.1 η.2 = ⊤ ∨ cssSyndromeWeight c η.1 η.2 ≤ (Fintype.card ι : ℕ∞) := by
  classical
  by_cases ht : cssSyndromeWeight c η.1 η.2 = ⊤
  · exact Or.inl ht
  · right
    let S : Set ℕ∞ := {w | ∃ (x z : ι → ZMod 2), c.hX *ᵥ z = η.1 ∧
      c.hZ *ᵥ x = η.2 ∧ (pauliWeight x z : ℕ∞) = w}
    have hs : S.Nonempty := by
      by_contra h
      apply ht
      change sInf S = ⊤
      rw [Set.not_nonempty_iff_eq_empty.mp h, sInf_empty]
    obtain ⟨x, z, _, _, hw⟩ := csInf_mem hs
    change sInf S ≤ (Fintype.card ι : ℕ∞)
    rw [← hw]
    exact_mod_cast pauliWeight_le_card x z

private noncomputable def cssLayerCoeff (w : ℕ∞) (ℓ : ℕ) : ℂ :=
  (if w ≤ (ℓ : ℕ∞) then 1 else 0) -
    (if ℓ = 0 then 0 else if w ≤ ((ℓ - 1 : ℕ) : ℕ∞) then 1 else 0)

private theorem cssLayerCoeff_eq (w : ℕ∞) (ℓ : ℕ) :
    cssLayerCoeff w ℓ = if w = (ℓ : ℕ∞) then 1 else 0 := by
  cases w using ENat.recTopCoe with
  | top => simp [cssLayerCoeff]
  | coe k =>
    simp only [cssLayerCoeff, ENat.coe_le_coe, ENat.coe_inj]
    by_cases hℓ : ℓ = 0
    · subst ℓ
      simp
    · by_cases hk : k = ℓ
      · subst k
        have hn : ¬ ℓ ≤ ℓ - 1 := by omega
        simp only [if_neg hℓ, if_pos (le_refl ℓ), if_neg hn, ite_true]
        norm_num
      · have he : k ≤ ℓ ↔ k ≤ ℓ - 1 := by omega
        simp only [if_neg hℓ, if_neg hk, he]
        exact sub_self _

private theorem cssLayerCoeff_weighted_sum (w : ℕ∞) (N : ℕ)
    (hw : w = ⊤ ∨ w ≤ (N : ℕ∞)) :
    (∑ ℓ ∈ Finset.range (N + 1), (ℓ : ℂ) * cssLayerCoeff w ℓ) = (w.toNat : ℂ) := by
  simp_rw [cssLayerCoeff_eq]
  cases w using ENat.recTopCoe with
  | top => simp
  | coe k =>
    have hk : k ≤ N := by simpa using hw
    rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp [Finset.mem_range, show k < N + 1 from by omega]

private theorem cssNeighborhoodProjector_indicator (c : CssData ι κX κZ) (ℓ : ℕ) :
    cssNeighborhoodProjector c ℓ = ∑ η : (κX → ZMod 2) × (κZ → ZMod 2),
      (if cssSyndromeWeight c η.1 η.2 ≤ (ℓ : ℕ∞) then (1 : ℂ) else 0) • cssSyndromeProjector c η := by
  classical
  unfold cssNeighborhoodProjector
  rw [Finset.sum_filter]
  simp

theorem cssDistanceOperator_eq_syndrome (c : CssData ι κX κZ) :
    cssDistanceOperator c = ∑ η ∈ Finset.univ,
      ((cssSyndromeWeight c η.1 η.2).toNat : ℂ) • cssSyndromeProjector c η := by
  classical
  unfold cssDistanceOperator
  simp_rw [cssNeighborhoodProjector_indicator]
  have hp (ℓ : ℕ) :
      (if ℓ = 0 then (0 : Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ) else
        ∑ η : (κX → ZMod 2) × (κZ → ZMod 2),
          (if cssSyndromeWeight c η.1 η.2 ≤ ((ℓ - 1 : ℕ) : ℕ∞) then (1 : ℂ) else 0) • cssSyndromeProjector c η) =
      ∑ η : (κX → ZMod 2) × (κZ → ZMod 2),
        (if ℓ = 0 then (0 : ℂ) else if cssSyndromeWeight c η.1 η.2 ≤ ((ℓ - 1 : ℕ) : ℕ∞) then 1 else 0) •
          cssSyndromeProjector c η := by
    by_cases h : ℓ = 0 <;> simp [h]
  simp_rw [hp, ← Finset.sum_sub_distrib, ← sub_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro η _
  change (∑ ℓ ∈ Finset.range (Fintype.card ι + 1),
    ((ℓ : ℂ) * cssLayerCoeff (cssSyndromeWeight c η.1 η.2) ℓ) • cssSyndromeProjector c η) = _
  rw [← Finset.sum_smul, cssLayerCoeff_weighted_sum _ _ (cssSyndromeWeight_top_or_le c η)]

private theorem cssAlgebraProduct_hermitian (c : CssData ι κX κZ)
    (η : (κX → ZMod 2) × (κZ → ZMod 2)) (s : Finset (κX ⊕ κZ)) :
    ((∏ k ∈ s, cssCheckAlgebraProjector c k (Sum.elim η.1 η.2 k) : cssCheckAlgebra c) :
      Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ).IsHermitian := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (Matrix.isHermitian_one : (1 : Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ).IsHermitian)
  | @insert k s hk ih =>
    rw [Finset.prod_insert hk]
    change ((cssCheckAlgebraProjector c k (Sum.elim η.1 η.2 k) : Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ) *
      ((∏ j ∈ s, cssCheckAlgebraProjector c j (Sum.elim η.1 η.2 j) : cssCheckAlgebra c) :
        Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ)).IsHermitian
    apply ((cssCheckProjector_hermitian (cssCheck c k) (cssCheck_hermitian c k) _).commute_iff ih).mp
    exact congrArg (cssCheckAlgebra c).val (mul_comm
      (cssCheckAlgebraProjector c k (Sum.elim η.1 η.2 k))
      (∏ j ∈ s, cssCheckAlgebraProjector c j (Sum.elim η.1 η.2 j)))

private theorem cssSyndromeProjector_hermitian (c : CssData ι κX κZ)
    (η : (κX → ZMod 2) × (κZ → ZMod 2)) : (cssSyndromeProjector c η).IsHermitian := by
  rw [← cssAlgebraSyndromeProjector_coe c η]
  exact cssAlgebraProduct_hermitian c η Finset.univ

private theorem cssSyndromeProjector_posSemidef (c : CssData ι κX κZ)
    (η : (κX → ZMod 2) × (κZ → ZMod 2)) : (cssSyndromeProjector c η).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (cssSyndromeProjector c η)
  rw [(cssSyndromeProjector_hermitian c η).eq, cssSyndromeProjector_mul, if_pos rfl] at h
  exact h

private theorem cssCodespace_exists_ne_zero (c : CssData ι κX κZ) :
    ∃ w : (ι → ZMod 2) → ℂ, w ∈ cssCodespace c ∧ w ≠ 0 := by
  have hd : 0 < Module.finrank ℂ ↥(cssCodespace c) := by
    rw [cssCodespace_finrank]
    exact pow_pos (by decide : 0 < (2 : ℕ)) _
  letI : Nontrivial ↥(cssCodespace c) := Module.finrank_pos_iff.mp hd
  obtain ⟨w, hw⟩ := exists_ne (0 : cssCodespace c)
  refine ⟨w, w.property, ?_⟩
  intro h
  apply hw
  apply Subtype.ext
  exact h

private theorem cssSyndromeProjector_exists_fixed_ne_zero (c : CssData ι κX κZ)
    (η : (κX → ZMod 2) × (κZ → ZMod 2)) (hη : cssSyndromeWeight c η.1 η.2 ≠ ⊤) :
    ∃ v : (ι → ZMod 2) → ℂ, cssSyndromeProjector c η *ᵥ v = v ∧ v ≠ 0 := by
  classical
  have hb : cssSyndromeWeight c η.1 η.2 ≤ (Fintype.card ι : ℕ∞) :=
    (cssSyndromeWeight_top_or_le c η).resolve_left hη
  obtain ⟨x, z, hx, hz, _⟩ := cssSyndromeWeight_witness_le c η (Fintype.card ι) hb
  obtain ⟨w, hw, hw0⟩ := cssCodespace_exists_ne_zero c
  let v := (cssPauliX x * cssPauliZ z) *ᵥ w
  refine ⟨v, ?_, ?_⟩
  · apply (cssSyndromeProjector_fixed_iff _ _ _).mpr
    simpa only [hx, hz] using pauliError_syndrome_of_code c x z w hw
  · intro hv
    have he : pauliErrorInverse x z *ᵥ v = w := by
      rw [Matrix.mulVec_mulVec, pauliError_inverse_mul, Matrix.one_mulVec]
    rw [hv, Matrix.mulVec_zero] at he
    exact hw0 he.symm

private theorem posSemidef_real_eigen_nonneg
    (T : Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ) (hT : T.PosSemidef)
    (a : ℝ) (v : (ι → ZMod 2) → ℂ) (hv : v ≠ 0)
    (he : T *ᵥ v = (a : ℂ) • v) : 0 ≤ a := by
  classical
  have hi : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  obtain ⟨i, hi⟩ := hi
  have hn : 0 < ∑ j : ι → ZMod 2, Complex.normSq (v j) :=
    Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨i, Finset.mem_univ i, Complex.normSq_pos.mpr hi⟩
  have hq : star v ⬝ᵥ v = ((∑ j : ι → ZMod 2, Complex.normSq (v j) : ℝ) : ℂ) := by
    simp only [dotProduct, Pi.star_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
      Complex.ofReal_sum]
  have hp := hT.dotProduct_mulVec_nonneg v
  rw [he, dotProduct_smul, hq] at hp
  have hreal : 0 ≤ a * ∑ j : ι → ZMod 2, Complex.normSq (v j) := by
    simpa [smul_eq_mul] using (Complex.nonneg_iff.mp hp).1
  exact (mul_nonneg_iff_of_pos_right hn).mp hreal

private noncomputable def cssSoundnessCoeff (c : CssData ι κX κZ) (σ : ℝ)
    (η : (κX → ZMod 2) × (κZ → ZMod 2)) : ℝ :=
  (bitWeight η.1 + bitWeight η.2 : ℕ) / (Fintype.card (κX ⊕ κZ) : ℝ) -
    σ / (Fintype.card ι : ℝ) * ((cssSyndromeWeight c η.1 η.2).toNat : ℝ)

private theorem cssSoundness_difference (c : CssData ι κX κZ) (σ : ℝ) :
    cssTester c - ((σ / (Fintype.card ι : ℝ) : ℂ) • cssDistanceOperator c) =
      ∑ η : (κX → ZMod 2) × (κZ → ZMod 2),
        (cssSoundnessCoeff c σ η : ℂ) • cssSyndromeProjector c η := by
  rw [cssTester_eq_syndrome, cssDistanceOperator_eq_syndrome, Finset.smul_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro η _
  rw [smul_smul, ← sub_smul]
  congr 1
  simp [cssSoundnessCoeff]

theorem cssHasSoundnessAtLeast_iff (c : CssData ι κX κZ) (σ : ℝ) :
    cssHasSoundnessAtLeast c σ ↔ ∀ η : (κX → ZMod 2) × (κZ → ZMod 2),
      σ / (Fintype.card ι : ℝ) * ((cssSyndromeWeight c η.1 η.2).toNat : ℝ) ≤
        ((bitWeight η.1 + bitWeight η.2 : ℕ) : ℝ) / (Fintype.card (κX ⊕ κZ) : ℝ) := by
  classical
  unfold cssHasSoundnessAtLeast
  rw [cssSoundness_difference]
  constructor
  · intro h η
    apply sub_nonneg.mp
    change 0 ≤ cssSoundnessCoeff c σ η
    by_cases ht : cssSyndromeWeight c η.1 η.2 = ⊤
    · simp only [cssSoundnessCoeff, ht, ENat.toNat_top, Nat.cast_zero, mul_zero, sub_zero]
      exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · obtain ⟨v, hv, hv0⟩ := cssSyndromeProjector_exists_fixed_ne_zero c η ht
      let T := ∑ η' : (κX → ZMod 2) × (κZ → ZMod 2),
        (cssSoundnessCoeff c σ η' : ℂ) • cssSyndromeProjector c η'
      have hmul : T * cssSyndromeProjector c η =
          (cssSoundnessCoeff c σ η : ℂ) • cssSyndromeProjector c η := by
        unfold T
        rw [Finset.sum_mul]
        simp_rw [Matrix.smul_mul, cssSyndromeProjector_mul]
        simp
      have he : T *ᵥ v = (cssSoundnessCoeff c σ η : ℂ) • v := by
        rw [← hv, Matrix.mulVec_mulVec, hmul, Matrix.smul_mulVec, hv]
      exact posSemidef_real_eigen_nonneg T h _ v hv0 he
  · intro h
    apply Matrix.posSemidef_sum
    intro η _
    apply (cssSyndromeProjector_posSemidef c η).smul
    apply Complex.nonneg_iff.mpr
    refine ⟨?_, by simp⟩
    change 0 ≤ cssSoundnessCoeff c σ η
    exact sub_nonneg.mpr (h η)

end Qatlib.Concepts.CodingDecoding.CssTesters.CssTester
