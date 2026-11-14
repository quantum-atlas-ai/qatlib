/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.ZMod.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic
public import Mathlib.Tactic.Abel

@[expose] public section

/-!
# Potts partition sums and cocycle weight enumerators

The graph coboundary sends a vertex coloring to the differences of its endpoint colors. Counting
its fibers relates a sum over colorings to the Hamming-weight enumerator of its image, yielding
`potts_weight_enumerator` with a factor equal to the coboundary kernel size [GeraciLidar2008].

## Main statements

* `sum_coboundary_eq`: A sum over colorings equals the kernel size times the sum over image
  words.
* `potts_weight_enumerator`: The edge-normalized Potts sum equals the kernel size times the code
  weight enumerator.

## References

* [Geraci and Lidar, 2008][GeraciLidar2008]
-/

set_option autoImplicit false

namespace Qatlib.Papers.PottsPartEval07.PottsBridge

open scoped BigOperators

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable (q : ℕ) [NeZero q] (ends : E → V × V)

/-- The additive map taking a vertex coloring to its endpoint differences on edges. -/
def coboundary : (V → ZMod q) →+ (E → ZMod q) where
  toFun σ := fun e => σ (ends e).1 - σ (ends e).2
  map_zero' := by
    ext e
    simp
  map_add' := by
    intro σ τ
    ext e
    simp only [Pi.add_apply]
    abel

omit [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [NeZero q] in
/-- The coboundary at an edge is the color at its first endpoint minus the color at its second
endpoint. -/
@[simp] lemma coboundary_apply (σ : V → ZMod q) (e : E) :
    coboundary q ends σ e = σ (ends e).1 - σ (ends e).2 := rfl

/-- The number of edges on which a word over `ZMod q` is nonzero. -/
def hammingWeight (w : E → ZMod q) : ℕ :=
  (Finset.univ.filter fun e => w e ≠ 0).card

/-- The finite set of edges whose endpoints have the same color. -/
def monochromatic (σ : V → ZMod q) : Finset E :=
  Finset.univ.filter fun e => σ (ends e).1 = σ (ends e).2

omit [Fintype V] [DecidableEq V] [DecidableEq E] [NeZero q] in
/-- The Hamming weight of a coloring's coboundary plus its number of monochromatic edges equals
the total number of edges [GeraciLidar2008]. -/
theorem weight_add_monochromatic (σ : V → ZMod q) :
    hammingWeight q (coboundary q ends σ) + (monochromatic q ends σ).card = Fintype.card E := by
  have hfil : (Finset.univ.filter fun e => ¬ σ (ends e).1 = σ (ends e).2)
      = (Finset.univ.filter fun e => coboundary q ends σ e ≠ 0) := by
    apply Finset.filter_congr
    intro e _
    rw [coboundary_apply]
    exact sub_ne_zero.symm
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset E)) (p := fun e => σ (ends e).1 = σ (ends e).2)
  rw [Finset.card_univ] at h
  rw [hfil] at h
  unfold hammingWeight monochromatic
  omega

/-- The number of vertex colorings whose coboundary is zero. -/
noncomputable def kernelSize : ℕ :=
  (Finset.univ.filter fun σ : V → ZMod q => coboundary q ends σ = 0).card

/-- The univariate Hamming-weight enumerator of the image of the graph coboundary. -/
noncomputable def codeWeightEnum (y : ℝ) : ℝ :=
  ∑ w ∈ Finset.univ.image (coboundary q ends), y ^ hammingWeight q w

omit [DecidableEq E] in
/-- Every nonempty fiber of the graph coboundary has cardinality equal to its kernel size. -/
theorem fiber_card_eq_kernelSize (w : E → ZMod q)
    (hw : w ∈ Finset.univ.image (coboundary q ends)) :
    (Finset.univ.filter fun σ : V → ZMod q => coboundary q ends σ = w).card
      = kernelSize q ends := by
  obtain ⟨σ₀, _hmem, rfl⟩ := Finset.mem_image.mp hw
  have hx : coboundary q ends σ₀ ∈ Set.range (coboundary q ends) := ⟨σ₀, rfl⟩
  have hy : (0 : E → ZMod q) ∈ Set.range (coboundary q ends) :=
    ⟨0, map_zero (coboundary q ends)⟩
  have h := AddMonoidHom.card_fiber_eq_of_mem_range (coboundary q ends) hx hy
  simpa [kernelSize] using h

omit [DecidableEq E] in
/-- The sum of weight monomials over vertex colorings is the kernel size times the weight sum
over coboundary image words [GeraciLidar2008]. -/
theorem sum_coboundary_eq (y : ℝ) :
    (∑ σ : V → ZMod q, y ^ hammingWeight q (coboundary q ends σ))
      = (kernelSize q ends : ℝ)
        * ∑ w ∈ Finset.univ.image (coboundary q ends), y ^ hammingWeight q w := by
  have hmap : ∀ σ ∈ (Finset.univ : Finset (V → ZMod q)),
      coboundary q ends σ ∈ Finset.univ.image (coboundary q ends) :=
    fun σ _ => Finset.mem_image.mpr ⟨σ, Finset.mem_univ _, rfl⟩
  have key := Finset.sum_fiberwise_of_maps_to' (s := Finset.univ)
    (t := Finset.univ.image (coboundary q ends)) (g := coboundary q ends)
    (f := fun w => y ^ hammingWeight q w) hmap
  rw [← key]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro w hw
  rw [Finset.sum_const, fiber_card_eq_kernelSize q ends w hw, nsmul_eq_mul]

/-- The partition sum assigning a coloring the inverse of `y` raised to its number of
monochromatic edges. -/
noncomputable def pottsZ (y : ℝ) : ℝ :=
  ∑ σ : V → ZMod q, (y ^ (monochromatic q ends σ).card)⁻¹

omit [DecidableEq E] in
/-- For nonzero `y`, multiplying the Potts partition sum by `y` to the edge count gives the
kernel size times the code weight enumerator [GeraciLidar2008]. -/
theorem potts_weight_enumerator (y : ℝ) (hy : y ≠ 0) :
    y ^ Fintype.card E * pottsZ q ends y
      = (kernelSize q ends : ℝ) * codeWeightEnum q ends y := by
  have hterm : ∀ σ : V → ZMod q,
      y ^ Fintype.card E * (y ^ (monochromatic q ends σ).card)⁻¹
        = y ^ hammingWeight q (coboundary q ends σ) := by
    intro σ
    have hsum := weight_add_monochromatic q ends σ
    have hle : (monochromatic q ends σ).card ≤ Fintype.card E := by omega
    rw [← pow_sub₀ y hy hle]
    congr 1
    omega
  unfold pottsZ codeWeightEnum
  rw [show y ^ Fintype.card E * (∑ σ : V → ZMod q, (y ^ (monochromatic q ends σ).card)⁻¹)
      = ∑ σ : V → ZMod q, y ^ hammingWeight q (coboundary q ends σ) from by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun σ _ => hterm σ)]
  exact sum_coboundary_eq q ends y

end Qatlib.Papers.PottsPartEval07.PottsBridge
