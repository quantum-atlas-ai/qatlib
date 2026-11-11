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

/-!
# CSS syndrome projectors and local testers

This module constructs the joint syndrome projectors of a CSS code, the subspaces reachable by
Pauli errors of bounded weight, and the associated distance operator. The commuting stabilizer
formalism underlying these constructions is described in [Gottesman1997].

The tester `cssTester` averages the rejecting check projectors. Its syndrome decomposition and
that of `cssDistanceOperator` reduce the operator soundness condition to scalar inequalities on
syndromes.

## Main statements

* `cssSyndromeProjector_sum`: the syndrome projectors sum to the identity.
* `cssSyndromeProjector_mul`: distinct syndrome projectors are orthogonal.
* `cssNeighborhoodProjector_range`: the neighborhood projector has the prescribed error
  neighborhood as its range.
* `cssHasSoundnessAtLeast_iff`: soundness is equivalent to the syndrome inequalities.

## References

* [Gottesman, 1997][Gottesman1997]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode

open Qatlib.Concepts.CodingDecoding.CssTesters

namespace Qatlib.Concepts.CodingDecoding.CssTesters.CssTester

open Matrix

open scoped ComplexOrder

variable {ι κX κZ : Type*} [Fintype ι] [Fintype κX] [Fintype κZ] [DecidableEq ι]
  [DecidableEq κX] [DecidableEq κZ]

/-- The family of X and Z stabilizer check matrices, indexed by the sum of the two check types. -/
def cssCheck (c : CssData ι κX κZ) :
    (κX ⊕ κZ) → Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ :=
  Sum.elim (fun i => cssPauliX (c.hX i)) (fun j => cssPauliZ (c.hZ j))

/-- The matrix `(1 + phaseOfBit b • S) / 2`, selecting the eigenvalue `phaseOfBit b` when `S` is
an involution. -/
noncomputable def cssCheckProjector (S : Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ) (b : ZMod 2) :
    Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ :=
  (2⁻¹ : ℂ) • (1 + phaseOfBit b • S)

/-- The product of the check projectors selecting the X and Z syndrome bits specified by `η`. -/
noncomputable def cssSyndromeProjector (c : CssData ι κX κZ)
    (η : (κX → ZMod 2) × (κZ → ZMod 2)) :
    Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ :=
  (Finset.univ.toList.map fun k =>
    cssCheckProjector (cssCheck c k) (Sum.elim η.1 η.2 k)).prod

/-- The infimum of the Pauli weights realizing the prescribed syndrome, with value `⊤` when no
realization exists. -/
noncomputable def cssSyndromeWeight (c : CssData ι κX κZ)
    (ηX : κX → ZMod 2) (ηZ : κZ → ZMod 2) : ℕ∞ :=
  sInf {w : ℕ∞ | ∃ (x z : ι → ZMod 2), c.hX *ᵥ z = ηX ∧ c.hZ *ᵥ x = ηZ ∧
    (pauliWeight x z : ℕ∞) = w}

/-- The complex span of code vectors acted on by Pauli errors of weight at most `ℓ`. -/
noncomputable def cssNeighborhood (c : CssData ι κX κZ) (ℓ : ℕ) :
    Submodule ℂ ((ι → ZMod 2) → ℂ) :=
  Submodule.span ℂ
    {v | ∃ (x z : ι → ZMod 2) (w : cssCodespace c), pauliWeight x z ≤ ℓ ∧
      v = (cssPauliX x * cssPauliZ z) *ᵥ (w : (ι → ZMod 2) → ℂ)}

/-- The sum of the syndrome projectors whose minimum realizing Pauli weight is at most `ℓ`. -/
noncomputable def cssNeighborhoodProjector (c : CssData ι κX κZ) (ℓ : ℕ) :
    Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ :=
  ∑ η ∈ Finset.univ.filter
      fun η : (κX → ZMod 2) × (κZ → ZMod 2) =>
        cssSyndromeWeight c η.1 η.2 ≤ (ℓ : ℕ∞),
    cssSyndromeProjector c η

/-- The weighted sum of successive neighborhood projector differences, with each layer weighted
by its radius. -/
noncomputable def cssDistanceOperator (c : CssData ι κX κZ) :
    Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ :=
  ∑ ℓ ∈ Finset.range (Fintype.card ι + 1),
    (ℓ : ℂ) • (cssNeighborhoodProjector c ℓ -
      (if ℓ = 0 then 0 else cssNeighborhoodProjector c (ℓ - 1)))

/-- The average of the rejecting projectors for the X and Z checks. -/
noncomputable def cssTester (c : CssData ι κX κZ) : Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ :=
  ((Fintype.card (κX ⊕ κZ) : ℕ) : ℂ)⁻¹ •
    ∑ k ∈ Finset.univ, cssCheckProjector (cssCheck c k) 1

/-- The condition that the tester minus `σ / Fintype.card ι` times the distance operator is
positive semidefinite. -/
def cssHasSoundnessAtLeast (c : CssData ι κX κZ) (σ : ℝ) : Prop :=
  (cssTester c - ((σ / (Fintype.card ι : ℝ) : ℂ) • cssDistanceOperator c)).PosSemidef

/-- Every CSS check squares to the identity. -/
private theorem cssCheck_square (c : CssData ι κX κZ) (k : κX ⊕ κZ) :
    cssCheck c k * cssCheck c k = 1 := by
  cases k with
  | inl i => exact cssPauliX_self_mul (c.hX i)
  | inr j => exact cssPauliZ_self_mul (c.hZ j)

/-- Every CSS check matrix is Hermitian. -/
private theorem cssCheck_hermitian (c : CssData ι κX κZ) (k : κX ⊕ κZ) :
    (cssCheck c k).IsHermitian := by
  cases k with
  | inl i => exact cssPauliX_isHermitian (c.hX i)
  | inr j => exact cssPauliZ_isHermitian (c.hZ j)

/-- An X check commutes with a Z check of the same CSS code. -/
private theorem css_check_cross (c : CssData ι κX κZ) (i : κX) (j : κZ) :
    cssPauliX (c.hX i) * cssPauliZ (c.hZ j) = cssPauliZ (c.hZ j) * cssPauliX (c.hX i) := by
  have h : bitDot (c.hX i) (c.hZ j) = 0 := by
    simpa [bitDot, dotProduct, Matrix.mul_apply] using congrFun (congrFun c.hcompat i) j
  rw [cssPauliXZ_comm, bitDot_comm, h, phaseOfBit_zero, one_smul]

/-- Any two CSS check matrices commute. -/
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

/-- The two bit projectors associated with a matrix sum to the identity. -/
private theorem cssCheckProjector_add (S : Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ) :
    cssCheckProjector S 0 + cssCheckProjector S 1 = 1 := by
  simp only [cssCheckProjector, phaseOfBit_zero, phaseOfBit_one, one_smul, neg_one_smul]
  module

/-- The bit projector of a Hermitian matrix is Hermitian. -/
private theorem cssCheckProjector_hermitian
    (S : Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ) (hS : S.IsHermitian) (b : ZMod 2) :
    (cssCheckProjector S b).IsHermitian := by
  exact (Matrix.isHermitian_one.add (hS.smul (phaseOfBit_star b))).smul (by simp)

/-- For an involution, the bit projectors are idempotent and mutually orthogonal. -/
private theorem cssCheckProjector_mul
    (S : Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ) (hS : S * S = 1) (b b' : ZMod 2) :
    cssCheckProjector S b * cssCheckProjector S b' =
      if b = b' then cssCheckProjector S b else 0 := by
  have hc : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases hc b with rfl | rfl <;> rcases hc b' with rfl | rfl <;>
    simp only [cssCheckProjector, phaseOfBit_zero, phaseOfBit_one, one_smul, neg_one_smul,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, add_mul, mul_add, neg_mul, mul_neg,
      neg_neg, one_mul, mul_one, hS] <;> norm_num <;> module

/-- The complex subalgebra generated by the CSS check matrices. -/
private noncomputable def cssCheckAlgebra (c : CssData ι κX κZ) :
    Subalgebra ℂ (Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ) :=
  Algebra.adjoin ℂ (Set.range (cssCheck c))

private instance cssCheckAlgebra_commutative (c : CssData ι κX κZ) :
    IsMulCommutative (cssCheckAlgebra c) :=
  Algebra.isMulCommutative_adjoin ℂ (by
    rintro _ ⟨k, rfl⟩ _ ⟨k', rfl⟩ _
    exact cssCheck_commute c k k')

open scoped IsMulCommutative

/-- A bit projector of a CSS check, regarded as an element of the check algebra. -/
private noncomputable def cssCheckAlgebraProjector (c : CssData ι κX κZ)
    (k : κX ⊕ κZ) (b : ZMod 2) : cssCheckAlgebra c :=
  ⟨cssCheckProjector (cssCheck c k) b, by
    apply (cssCheckAlgebra c).smul_mem
    apply (cssCheckAlgebra c).add_mem (cssCheckAlgebra c).one_mem
    apply (cssCheckAlgebra c).smul_mem
    exact Algebra.subset_adjoin ⟨k, rfl⟩⟩

/-- The product of the selected bit projectors inside the commutative check algebra. -/
private noncomputable def cssAlgebraSyndromeProjector (c : CssData ι κX κZ)
    (η : (κX → ZMod 2) × (κZ → ZMod 2)) : cssCheckAlgebra c :=
  ∏ k : κX ⊕ κZ, cssCheckAlgebraProjector c k (Sum.elim η.1 η.2 k)

/-- Coercing the check algebra syndrome projector to a matrix yields `cssSyndromeProjector`. -/
private theorem cssAlgebraSyndromeProjector_coe (c : CssData ι κX κZ)
    (η : (κX → ZMod 2) × (κZ → ZMod 2)) :
    (cssAlgebraSyndromeProjector c η : Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ) =
      cssSyndromeProjector c η := by
  unfold cssAlgebraSyndromeProjector
  rw [← Finset.prod_map_toList]
  change (cssCheckAlgebra c).val _ = _
  rw [map_list_prod]
  simp [cssSyndromeProjector, cssCheckAlgebraProjector, List.map_map, Function.comp_def]

/-- A sum indexed by `ZMod 2` is the sum of the values at zero and one. -/
private theorem sum_binary_values {R : Type*} [AddCommMonoid R] (f : ZMod 2 → R) :
    (∑ b : ZMod 2, f b) = f 0 + f 1 := by
  have hs : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  rw [hs]
  simp [show (0 : ZMod 2) ≠ 1 from by decide]

/-- The two bit projectors for a check sum to the identity in the check algebra. -/
private theorem cssCheckAlgebraProjector_sum (c : CssData ι κX κZ) (k : κX ⊕ κZ) :
    (∑ b : ZMod 2, cssCheckAlgebraProjector c k b) = 1 := by
  rw [sum_binary_values]
  apply Subtype.ext
  exact cssCheckProjector_add (cssCheck c k)

/-- The syndrome projectors sum to the identity inside the check algebra. -/
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

/-- The joint CSS syndrome projectors sum to the identity, giving a complete decomposition as in
the stabilizer formalism of [Gottesman1997]. -/
theorem cssSyndromeProjector_sum (c : CssData ι κX κZ) :
    ∑ η ∈ Finset.univ, cssSyndromeProjector c η = 1 := by
  have h := congrArg (cssCheckAlgebra c).val (cssAlgebraSyndromeProjector_sum c)
  rw [map_sum, map_one] at h
  change (∑ η, (cssAlgebraSyndromeProjector c η : Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ)) = 1 at h
  simpa only [cssAlgebraSyndromeProjector_coe] using h

/-- Bit projectors of a fixed check multiply to the matching projector or zero in the check
algebra. -/
private theorem cssCheckAlgebraProjector_mul (c : CssData ι κX κZ) (k : κX ⊕ κZ)
    (b b' : ZMod 2) :
    cssCheckAlgebraProjector c k b * cssCheckAlgebraProjector c k b' =
      if b = b' then cssCheckAlgebraProjector c k b else 0 := by
  apply Subtype.ext
  simpa only [cssCheckAlgebraProjector, Subalgebra.coe_mul, apply_ite Subtype.val,
    Subalgebra.coe_zero] using cssCheckProjector_mul (cssCheck c k) (cssCheck_square c k) b b'

/-- Syndrome projectors in the check algebra multiply to the matching projector or zero. -/
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

/-- The CSS syndrome projectors are idempotent and pairwise orthogonal; see [Gottesman1997] for
the stabilizer formalism. -/
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

/-- Each CSS neighborhood projector is idempotent. -/
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

/-- The bit projector selected by a syndrome acts as the identity on its syndrome projector in
the check algebra. -/
private theorem cssCheckAlgebraProjector_absorb (c : CssData ι κX κZ)
    (η : (κX → ZMod 2) × (κZ → ZMod 2)) (k : κX ⊕ κZ) :
    cssCheckAlgebraProjector c k (Sum.elim η.1 η.2 k) * cssAlgebraSyndromeProjector c η =
      cssAlgebraSyndromeProjector c η := by
  classical
  unfold cssAlgebraSyndromeProjector
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
  rw [← mul_assoc, cssCheckAlgebraProjector_mul, if_pos rfl]

/-- A check projector selected by a syndrome absorbs the corresponding syndrome projector. -/
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

/-- A vector is fixed by the bit projector exactly when it has eigenvalue `phaseOfBit b` under
`S`. -/
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

/-- A product of matrices fixes a vector when every factor fixes it. -/
private theorem list_prod_fixed
    (l : List (Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ)) (v : (ι → ZMod 2) → ℂ)
    (h : ∀ S ∈ l, S *ᵥ v = v) : l.prod *ᵥ v = v := by
  induction l with
  | nil => simp
  | cons S l ih =>
    rw [List.prod_cons, ← Matrix.mulVec_mulVec, ih (fun T hT => h T (List.mem_cons_of_mem _ hT)),
      h S (by simp)]

/-- A vector is fixed by the syndrome projector exactly when all checks have the eigenvalues
specified by the syndrome. -/
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

/-- A vector belongs to the CSS codespace exactly when every check fixes it. -/
private theorem mem_cssCodespace_check_iff (c : CssData ι κX κZ) (v : (ι → ZMod 2) → ℂ) :
    v ∈ cssCodespace c ↔ ∀ k : κX ⊕ κZ, cssCheck c k *ᵥ v = v := by
  simp [cssCodespace, cssXStabilized, cssZStabilized, cssXCheckKernel, cssZCheckKernel,
    cssCheck, sub_eq_zero, Sum.forall]

/-- A syndrome of weight at most `ℓ` has a realizing Pauli error of weight at most `ℓ`. -/
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

/-- The square of the Pauli product with labels `x` and `z` is the identity times `phaseOfBit
(bitDot z x)`. -/
private theorem pauliError_square (x z : ι → ZMod 2) :
    (cssPauliX x * cssPauliZ z) * (cssPauliX x * cssPauliZ z) = phaseOfBit (bitDot z x) • 1 := by
  rw [cssPauliXZ_mul, binary_add_self, binary_add_self, cssPauliX_zero, cssPauliZ_zero, one_mul]

/-- The Pauli product with labels `x` and `z`, multiplied by the phase that makes it its
inverse. -/
private noncomputable def pauliErrorInverse (x z : ι → ZMod 2) :
    Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ := phaseOfBit (bitDot z x) • (cssPauliX x * cssPauliZ z)

/-- Multiplying a Pauli error by `pauliErrorInverse` on the right gives the identity. -/
private theorem pauliError_mul_inverse (x z : ι → ZMod 2) :
    (cssPauliX x * cssPauliZ z) * pauliErrorInverse x z = 1 := by
  rw [pauliErrorInverse, Matrix.mul_smul, pauliError_square, smul_smul,
    phaseOfBit_mul_self, one_smul]

/-- Multiplying a Pauli error by `pauliErrorInverse` on the left gives the identity. -/
private theorem pauliError_inverse_mul (x z : ι → ZMod 2) :
    pauliErrorInverse x z * (cssPauliX x * cssPauliZ z) = 1 := by
  rw [pauliErrorInverse, Matrix.smul_mul, pauliError_square, smul_smul,
    phaseOfBit_mul_self, one_smul]

/-- Commuting a CSS check past a Pauli error introduces the phase determined by the
corresponding syndrome bit. -/
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

/-- Commuting a CSS check past the inverse Pauli error introduces its syndrome phase. -/
private theorem cssCheck_pauli_inverse (c : CssData ι κX κZ) (x z : ι → ZMod 2) (k : κX ⊕ κZ) :
    cssCheck c k * pauliErrorInverse x z =
      phaseOfBit (Sum.elim (c.hX *ᵥ z) (c.hZ *ᵥ x) k) •
        (pauliErrorInverse x z * cssCheck c k) := by
  rw [pauliErrorInverse, Matrix.mul_smul, cssCheck_pauli_mul, Matrix.smul_mul, smul_smul,
    smul_smul]
  rw [mul_comm]

/-- A Pauli error applied to a code vector has the check eigenvalues specified by its syndrome. -/
private theorem pauliError_syndrome_of_code (c : CssData ι κX κZ) (x z : ι → ZMod 2)
    (w : (ι → ZMod 2) → ℂ) (hw : w ∈ cssCodespace c) :
    ∀ k : κX ⊕ κZ, cssCheck c k *ᵥ ((cssPauliX x * cssPauliZ z) *ᵥ w) =
      phaseOfBit (Sum.elim (c.hX *ᵥ z) (c.hZ *ᵥ x) k) • ((cssPauliX x * cssPauliZ z) *ᵥ w) := by
  intro k
  rw [Matrix.mulVec_mulVec, cssCheck_pauli_mul, Matrix.smul_mulVec,
    ← Matrix.mulVec_mulVec, (mem_cssCodespace_check_iff c w).mp hw k]

/-- Applying the inverse Pauli error to a vector with its syndrome yields a code vector. -/
private theorem pauliError_preimage_in_code (c : CssData ι κX κZ) (x z : ι → ZMod 2)
    (v : (ι → ZMod 2) → ℂ)
    (hv : ∀ k : κX ⊕ κZ, cssCheck c k *ᵥ v =
      phaseOfBit (Sum.elim (c.hX *ᵥ z) (c.hZ *ᵥ x) k) • v) :
    pauliErrorInverse x z *ᵥ v ∈ cssCodespace c := by
  apply (mem_cssCodespace_check_iff _ _).mpr
  intro k
  rw [Matrix.mulVec_mulVec, cssCheck_pauli_inverse, Matrix.smul_mulVec,
    ← Matrix.mulVec_mulVec, hv k, Matrix.mulVec_smul, smul_smul, phaseOfBit_mul_self, one_smul]

/-- The neighborhood projector preserves a syndrome projector of weight at most `ℓ` and
annihilates one of larger weight. -/
private theorem cssNeighborhoodProjector_mul_syndrome (c : CssData ι κX κZ) (ℓ : ℕ)
    (η : (κX → ZMod 2) × (κZ → ZMod 2)) :
    cssNeighborhoodProjector c ℓ * cssSyndromeProjector c η =
      if cssSyndromeWeight c η.1 η.2 ≤ (ℓ : ℕ∞) then cssSyndromeProjector c η else 0 := by
  classical
  unfold cssNeighborhoodProjector
  rw [Finset.sum_mul]
  simp_rw [cssSyndromeProjector_mul]
  simp

/-- The range of the neighborhood projector is exactly the span of code vectors with Pauli
errors of weight at most `ℓ`. -/
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

/-- A check acts on a syndrome projector by the eigenvalue encoded by its syndrome bit. -/
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

/-- The rejecting check projector preserves a syndrome projector exactly when its selected
syndrome bit is one, and otherwise annihilates it. -/
private theorem cssReject_mul_syndrome (c : CssData ι κX κZ)
    (η : (κX → ZMod 2) × (κZ → ZMod 2)) (k : κX ⊕ κZ) :
    cssCheckProjector (cssCheck c k) 1 * cssSyndromeProjector c η =
      if Sum.elim η.1 η.2 k = 1 then cssSyndromeProjector c η else 0 := by
  rw [cssCheckProjector, Matrix.smul_mul, Matrix.add_mul, Matrix.smul_mul, one_mul,
    cssCheck_mul_syndrome, phaseOfBit_one, smul_smul]
  by_cases h : Sum.elim η.1 η.2 k = 1 <;> simp only [phaseOfBit, h, if_true, if_false] <;> module

/-- The number of nonzero syndrome bits in the combined check index is the sum of the X and Z
Hamming weights. -/
private theorem cssSyndrome_check_count (η : (κX → ZMod 2) × (κZ → ZMod 2)) :
    ((Finset.univ : Finset (κX ⊕ κZ)).filter (fun k => Sum.elim η.1 η.2 k = 1)).card =
      bitWeight η.1 + bitWeight η.2 := by
  have hb : ∀ b : ZMod 2, b ≠ 0 ↔ b = 1 := by decide
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  simp only [bitWeight, hb, Finset.card_eq_sum_ones, Finset.sum_filter]

/-- On each syndrome projector, the tester acts by the fraction of violated checks. -/
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

/-- The tester is the sum of the syndrome projectors weighted by their fractions of violated
checks. -/
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

/-- A Pauli error has weight at most the number of qubits. -/
private theorem pauliWeight_le_card (x z : ι → ZMod 2) : pauliWeight x z ≤ Fintype.card ι := by
  exact (Finset.card_filter_le _ _).trans_eq Finset.card_univ

/-- The minimum realizing Pauli weight is either infinite or at most the number of qubits. -/
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

/-- The difference of successive threshold indicators selecting the layer of radius `ℓ`. -/
private noncomputable def cssLayerCoeff (w : ℕ∞) (ℓ : ℕ) : ℂ :=
  (if w ≤ (ℓ : ℕ∞) then 1 else 0) -
    (if ℓ = 0 then 0 else if w ≤ ((ℓ - 1 : ℕ) : ℕ∞) then 1 else 0)

/-- The layer coefficient is one exactly when `w` equals the finite radius `ℓ`, and zero
otherwise. -/
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

/-- The weighted sum of layer coefficients through radius `N` equals `w.toNat` when `w` is
infinite or at most `N`. -/
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

/-- The neighborhood projector is the syndrome sum weighted by the indicator of the radius
bound. -/
private theorem cssNeighborhoodProjector_indicator (c : CssData ι κX κZ) (ℓ : ℕ) :
    cssNeighborhoodProjector c ℓ = ∑ η : (κX → ZMod 2) × (κZ → ZMod 2),
      (if cssSyndromeWeight c η.1 η.2 ≤ (ℓ : ℕ∞) then (1 : ℂ) else 0) • cssSyndromeProjector c η := by
  classical
  unfold cssNeighborhoodProjector
  rw [Finset.sum_filter]
  simp

/-- The distance operator is diagonal in the syndrome decomposition, with coefficient equal to
the natural value of each syndrome weight. -/
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

/-- A finite product of the bit projectors selected by a syndrome is Hermitian as a matrix. -/
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

/-- Each CSS syndrome projector is Hermitian. -/
private theorem cssSyndromeProjector_hermitian (c : CssData ι κX κZ)
    (η : (κX → ZMod 2) × (κZ → ZMod 2)) : (cssSyndromeProjector c η).IsHermitian := by
  rw [← cssAlgebraSyndromeProjector_coe c η]
  exact cssAlgebraProduct_hermitian c η Finset.univ

/-- Each CSS syndrome projector is positive semidefinite. -/
private theorem cssSyndromeProjector_posSemidef (c : CssData ι κX κZ)
    (η : (κX → ZMod 2) × (κZ → ZMod 2)) : (cssSyndromeProjector c η).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (cssSyndromeProjector c η)
  rw [(cssSyndromeProjector_hermitian c η).eq, cssSyndromeProjector_mul, if_pos rfl] at h
  exact h

/-- Every CSS codespace contains a nonzero vector. -/
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

/-- A syndrome with finite realizing weight has a nonzero vector fixed by its syndrome
projector. -/
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

/-- A real eigenvalue of a positive semidefinite matrix with a nonzero eigenvector is
nonnegative. -/
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

/-- The fraction of violated checks minus the normalized soundness parameter times the syndrome
weight. -/
private noncomputable def cssSoundnessCoeff (c : CssData ι κX κZ) (σ : ℝ)
    (η : (κX → ZMod 2) × (κZ → ZMod 2)) : ℝ :=
  (bitWeight η.1 + bitWeight η.2 : ℕ) / (Fintype.card (κX ⊕ κZ) : ℝ) -
    σ / (Fintype.card ι : ℝ) * ((cssSyndromeWeight c η.1 η.2).toNat : ℝ)

/-- The difference defining soundness is the syndrome sum weighted by `cssSoundnessCoeff`. -/
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

/-- The operator soundness condition holds exactly when the normalized distance contribution is
bounded by the fraction of violated checks for every syndrome. -/
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
