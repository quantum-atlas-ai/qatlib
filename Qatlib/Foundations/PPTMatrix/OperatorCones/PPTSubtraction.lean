/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.PPTMatrix.OperatorCones.ForMathlib.PositiveRankOneCoefficient
public import Qatlib.Foundations.PPTMatrix.OperatorCones.Lift

@[expose] public section




/-!
# Compatible product ranges and finite PPT rank descent

A compatible product vector lies in the range of `X`, and its conjugate on the
reference factor lies in the range of the reference partial transpose. Subtracting
the same positive projector coefficient from both matrices preserves PPT and
strictly decreases their rank sum. Consequently, if every nonzero PPT matrix in
a fixed bipartite dimension has such a direction, every PPT matrix there is
separable. This is a conditional reduction: existence of those directions for
2×3 matrices is still the separate Woronowicz obligation.
-/

open Matrix
open scoped Kronecker ComplexOrder

namespace Qatlib.Foundations.PPTMatrix.OperatorCones

variable {κ n : Type*} [Fintype κ] [DecidableEq κ] [Fintype n] [DecidableEq n]

/-- A nonzero product vector in the first range, compatible with partial conjugation
in the partial-transpose range. These are actual matrix-vector range equations. -/
def HasCompatibleProductRanges (X : Matrix (κ × n) (κ × n) ℂ) : Prop :=
  ∃ (a : κ → ℂ) (b : n → ℂ) (w z : κ × n → ℂ),
    prodVec a b ≠ 0 ∧ X *ᵥ w = prodVec a b ∧
      partialTransposeRef X *ᵥ z = prodVec (star a) b

omit [Fintype κ] [DecidableEq κ] [Fintype n] [DecidableEq n] in
/-- Establishes `prodVec_star_left_ne_zero`: `prodVec (star a) b ≠ 0`, for the stated parameters. -/
theorem prodVec_star_left_ne_zero {a : κ → ℂ} {b : n → ℂ}
    (hab : prodVec a b ≠ 0) : prodVec (star a) b ≠ 0 := by
  intro hz
  apply hab
  funext x
  have hx := congrFun hz x
  change star (a x.1) * b x.2 = 0 at hx
  change a x.1 * b x.2 = 0
  rcases mul_eq_zero.mp hx with ha | hb
  · exact mul_eq_zero.mpr (Or.inl (star_eq_zero.mp ha))
  · exact mul_eq_zero.mpr (Or.inr hb)

omit [Fintype κ] [DecidableEq κ] [Fintype n] [DecidableEq n] in
/-- Establishes `partialTransposeRef_pureState_prodVec`: `partialTransposeRef (pureState (prodVec a b)) = pureState (prodVec (star a) b)`, for the stated parameters. -/
theorem partialTransposeRef_pureState_prodVec (a : κ → ℂ) (b : n → ℂ) :
    partialTransposeRef (pureState (prodVec a b)) = pureState (prodVec (star a) b) := by
  ext x y
  simp only [partialTransposeRef_apply, pureState, Matrix.vecMulVec_apply,
    prodVec, Pi.star_apply, star_mul, star_star]
  ring

omit [Fintype κ] [DecidableEq κ] [Fintype n] [DecidableEq n] in
/-- Establishes `partialTransposeRef_sub_product_projector`: `partialTransposeRef (X - c • pureState (prodVec a b)) = partialTransposeRef X - c • pureState (prodVec (star a) b)`, for the stated parameters. -/
theorem partialTransposeRef_sub_product_projector
    (X : Matrix (κ × n) (κ × n) ℂ) (c : ℂ) (a : κ → ℂ) (b : n → ℂ) :
    partialTransposeRef (X - c • pureState (prodVec a b)) =
      partialTransposeRef X - c • pureState (prodVec (star a) b) := by
  have hlinear : partialTransposeRef (X - c • pureState (prodVec a b)) =
      partialTransposeRef X - c • partialTransposeRef (pureState (prodVec a b)) := by
    ext x y
    rfl
  rw [hlinear, partialTransposeRef_pureState_prodVec]

omit [DecidableEq κ] [DecidableEq n] in
/-- Establishes `isSeparable_smul_pureState_prodVec`: `IsSeparable ((t : ℂ) • pureState (prodVec a b))`, for the stated parameters. -/
theorem isSeparable_smul_pureState_prodVec (a : κ → ℂ) (b : n → ℂ)
    (t : ℝ) (ht : 0 ≤ t) : IsSeparable ((t : ℂ) • pureState (prodVec a b)) := by
  rw [pureState_prodVec, ← Matrix.smul_kronecker]
  exact IsSeparable.kronecker
    ((Matrix.posSemidef_vecMulVec_self_star a).smul (Complex.zero_le_real.mpr ht))
    (Matrix.posSemidef_vecMulVec_self_star b)

/-- Compatible range directions admit a PPT subtraction with strictly smaller rank sum
and a separable remainder. No rank or invertibility restriction is imposed. -/
theorem exists_ppt_subtraction_of_compatible_ranges
    {X : Matrix (κ × n) (κ × n) ℂ} (hX : X.PosSemidef)
    (hΓ : (partialTransposeRef X).PosSemidef) (hcompat : HasCompatibleProductRanges X) :
    ∃ Y : Matrix (κ × n) (κ × n) ℂ,
      Y.PosSemidef ∧ (partialTransposeRef Y).PosSemidef ∧
      Y.rank + (partialTransposeRef Y).rank < X.rank + (partialTransposeRef X).rank ∧
      IsSeparable (X - Y) := by
  obtain ⟨a, b, w, z, hab, hw, hz⟩ := hcompat
  obtain ⟨s, hs, hspos, hsrank, hsbelow, hsweak⟩ :=
    exists_positive_subtraction_of_range hX hab ⟨w, hw⟩
  obtain ⟨t, ht, htpos, htrank, htbelow, htweak⟩ :=
    exists_positive_subtraction_of_range hΓ (prodVec_star_left_ne_zero hab) ⟨z, hz⟩
  let c := min s t
  let Y := X - (c : ℂ) • pureState (prodVec a b)
  have hc : 0 < c := lt_min hs ht
  have hY : Y.PosSemidef := hsbelow c (min_le_left s t)
  have hYΓeq : partialTransposeRef Y =
      partialTransposeRef X - (c : ℂ) • pureState (prodVec (star a) b) :=
    partialTransposeRef_sub_product_projector X (c : ℂ) a b
  have hYΓ : (partialTransposeRef Y).PosSemidef := by
    rw [hYΓeq]
    exact htbelow c (min_le_right s t)
  have hle : Y.rank ≤ X.rank := hsweak c
  have hleΓ : (partialTransposeRef Y).rank ≤ (partialTransposeRef X).rank := by
    rw [hYΓeq]
    exact htweak c
  have hdrop : Y.rank + (partialTransposeRef Y).rank <
      X.rank + (partialTransposeRef X).rank := by
    rcases le_total s t with hst | hts
    · have hc_eq : c = s := min_eq_left hst
      have hlt : Y.rank < X.rank := by simpa only [Y, hc_eq, pureState] using hsrank
      omega
    · have hc_eq : c = t := min_eq_right hts
      have hlt : (partialTransposeRef Y).rank < (partialTransposeRef X).rank := by
        rw [hYΓeq, hc_eq]
        exact htrank
      omega
  refine ⟨Y, hY, hYΓ, hdrop, ?_⟩
  have hdiff : X - Y = (c : ℂ) • pureState (prodVec a b) := by dsimp [Y]; abel
  rw [hdiff]
  exact isSeparable_smul_pureState_prodVec a b c hc.le

/-- Finite rank descent reduces PPT separability in a fixed bipartite dimension
to the compatible product-range property for every nonzero PPT operator there. -/
theorem isSeparable_of_compatible_product_range_property
    (hproperty : ∀ X : Matrix (κ × n) (κ × n) ℂ,
      X.PosSemidef → (partialTransposeRef X).PosSemidef → X ≠ 0 →
        HasCompatibleProductRanges X)
    {X : Matrix (κ × n) (κ × n) ℂ} (hX : X.PosSemidef)
    (hΓ : (partialTransposeRef X).PosSemidef) : IsSeparable X := by
  suffices h : ∀ m : ℕ, ∀ Y : Matrix (κ × n) (κ × n) ℂ,
      Y.rank + (partialTransposeRef Y).rank = m →
      Y.PosSemidef → (partialTransposeRef Y).PosSemidef → IsSeparable Y by
    exact h _ X rfl hX hΓ
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro Y hmeasure hY hYΓ
    by_cases hz : Y = 0
    · rw [hz]
      exact IsSeparable.zero
    obtain ⟨Z, hZ, hZΓ, hdrop, hsep⟩ :=
      exists_ppt_subtraction_of_compatible_ranges hY hYΓ (hproperty Y hY hYΓ hz)
    have hsmall : Z.rank + (partialTransposeRef Z).rank < m := by omega
    have hsepZ := ih _ hsmall Z rfl hZ hZΓ
    have heq : Y = Z + (Y - Z) := by abel
    rw [heq]
    exact hsepZ.add hsep

end Qatlib.Foundations.PPTMatrix.OperatorCones
