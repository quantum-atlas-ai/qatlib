/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.NumberTheory.GaussSum
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 5: the Gauss-sum product identity

The paper defines, for a nontrivial multiplicative character `χ` of `Fˣ` and a
nontrivial additive character `η` of `F`,

```
G(χ, t) = (1 / sqrt q) * ∑_{y ∈ Fˣ} χ(y) * η(t y),        q = #F.
```

Mathlib's `gaussSum χ ψ` is `∑_{y ∈ F} χ y * ψ y`; since a nontrivial
multiplicative character vanishes at `0`, this is the same sum over `Fˣ`.

The paper's displayed identity is `G(χ, z) * conj (G(χ, t)) = χ(z / t)`.
The proof printed in the paper actually gives `χ(t / z)`: the conjugation
inverts the multiplicative character.  We prove the mathematically correct
identity with `χ (t / z)`, and record the equivalent `χ⁻¹ (z / t)` form.
-/

set_option autoImplicit false

namespace Qatlib.Papers.HSPAffine13.MainResults

open AddChar MulChar

variable {F : Type*} [Field F] [Fintype F]

/-- The paper's normalized Gauss sum `G(χ, t)`, written in terms of Mathlib's
`gaussSum`.  The additive character is shifted by `t`. -/
noncomputable def paperGauss (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (t : F) : ℂ :=
  (((Real.sqrt (Fintype.card F) : ℝ) : ℂ))⁻¹ * gaussSum χ (ψ.mulShift t)

omit [Fintype F] in
/-- The inverse of a shifted additive character is the shift by the negative. -/
theorem addChar_mulShift_inv (ψ : AddChar F ℂ) (t : F) :
    (ψ.mulShift t)⁻¹ = ψ.mulShift (-t) := by
  ext x
  simp [mulShift_apply, neg_mul]

/-- **Unnormalized Lemma 5.**  For a nontrivial multiplicative character `χ`,
a primitive additive character `ψ`, and nonzero `z, t`,

```
gaussSum χ ψ_z * conj (gaussSum χ ψ_t) = q * χ (t / z).
```

This is the unnormalized form of the paper's Gauss-sum product identity. -/
theorem gaussSum_mul_star_gaussSum (χ : MulChar F ℂ) (hχ : χ ≠ 1)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {z t : F} (hz : z ≠ 0) (ht : t ≠ 0) :
    gaussSum χ (ψ.mulShift z) * star (gaussSum χ (ψ.mulShift t)) =
      (Fintype.card F : ℂ) * χ (t / z) := by
  let uz : Fˣ := Units.mk0 z hz
  have huz : (uz : F) = z := rfl
  have hstar : star (gaussSum χ (ψ.mulShift t)) =
      gaussSum χ⁻¹ ((ψ.mulShift t)⁻¹) := star_gaussSum_eq χ (ψ.mulShift t)
  have hz' : gaussSum χ (ψ.mulShift z) = χ⁻¹ (uz : F) * gaussSum χ ψ := by
    simpa only [huz] using gaussSum_mulShift_eq χ ψ uz
  have ht' : gaussSum χ⁻¹ ((ψ.mulShift t)⁻¹) = χ (-t) * gaussSum χ⁻¹ ψ := by
    rw [addChar_mulShift_inv]
    have h := gaussSum_mulShift_eq χ⁻¹ ψ (Units.mk0 (-t) (neg_ne_zero.mpr ht))
    simpa using h
  have hnum : gaussSum χ⁻¹ ψ = χ (-1) * gaussSum χ⁻¹ ψ⁻¹ := by
    have h := (mul_gaussSum_inv_eq_gaussSum (χ := χ⁻¹) (ψ := ψ)).symm
    have hneg1 : χ⁻¹ (-1) = χ (-1) := by
      rw [MulChar.inv_apply_eq_inv']
      exact inv_eq_of_mul_eq_one_right (by
        have h := map_mul χ (-1) (-1)
        simpa using h.symm)
    simpa [hneg1] using h
  have hcard : gaussSum χ ψ * gaussSum χ⁻¹ ψ⁻¹ = (Fintype.card F : ℂ) :=
    gaussSum_mul_gaussSum_eq_card hχ hψ
  have hcoef : χ⁻¹ (uz : F) * χ (-t) * χ (-1) = χ (t / z) := by
    have hnegut : χ (-t) = χ (-1) * χ t := by
      simpa using (map_mul χ (-1) t)
    have hχneg : χ (-1) * χ (-1) = 1 := by
      have h := map_mul χ (-1) (-1)
      simpa using h.symm
    have hzprod : χ⁻¹ (uz : F) = (χ (uz : F))⁻¹ := by
      simpa [Ring.inverse_eq_inv] using (inv_apply_eq_inv' χ (uz : F))
    have hzval : χ (uz : F) = χ z := by rw [huz]
    have hmapinv : χ (z⁻¹) = (χ z)⁻¹ := by
      rw [← MulChar.inv_apply' χ z, MulChar.inv_apply_eq_inv']
    have htdiv : χ (t / z) = χ t * (χ z)⁻¹ := by
      rw [div_eq_mul_inv, map_mul, hmapinv]
    rw [hnegut, hzprod, hzval, htdiv]
    calc
      (χ z)⁻¹ * (χ (-1) * χ t) * χ (-1)
          = (χ z)⁻¹ * χ t * (χ (-1) * χ (-1)) := by ring
      _ = (χ z)⁻¹ * χ t := by rw [hχneg]; ring
      _ = χ t * (χ z)⁻¹ := by ring
  rw [hz', hstar, ht', hnum]
  calc
    (χ⁻¹ (uz : F) * gaussSum χ ψ) *
        (χ (-t) * (χ (-1) * gaussSum χ⁻¹ ψ⁻¹)) =
        (χ⁻¹ (uz : F) * χ (-t) * χ (-1)) *
          (gaussSum χ ψ * gaussSum χ⁻¹ ψ⁻¹) := by ring
    _ = χ (t / z) * (Fintype.card F : ℂ) := by rw [hcoef, hcard]
    _ = (Fintype.card F : ℂ) * χ (t / z) := by ring

/-- **Lemma 5 (normalized form).**  With the paper's normalization,

```
G(χ, z) * conj (G(χ, t)) = χ (t / z).
```

This is the normalized Gauss-sum product identity; the paper prints the
right-hand side as `χ (z / t)`, which is the inverse character value. -/
theorem paperGauss_mul_star (χ : MulChar F ℂ) (hχ : χ ≠ 1)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {z t : F} (hz : z ≠ 0) (ht : t ≠ 0) :
    paperGauss χ ψ z * star (paperGauss χ ψ t) = χ (t / z) := by
  let a : ℂ := (((Real.sqrt (Fintype.card F) : ℝ) : ℂ))⁻¹
  have ha : star a = a := by
    simp [a]
  have hstar : star (paperGauss χ ψ t) =
      a * star (gaussSum χ (ψ.mulShift t)) := by
    unfold paperGauss
    rw [star_mul, ha]
    ring
  rw [hstar]
  change a * gaussSum χ (ψ.mulShift z) *
      (a * star (gaussSum χ (ψ.mulShift t))) = χ (t / z)
  have haa : a * a = ((Fintype.card F : ℂ))⁻¹ := by
    have hq : (((Real.sqrt (Fintype.card F) : ℝ) : ℂ)) ≠ 0 := by
      have hpos : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
      exact_mod_cast (Real.sqrt_ne_zero'.mpr hpos)
    unfold a
    field_simp [hq]
    have hsq : ((Real.sqrt (Fintype.card F) : ℝ) : ℂ) ^ 2 =
        (Fintype.card F : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      norm_num
    rw [hsq]
  calc
    a * gaussSum χ (ψ.mulShift z) * (a * star (gaussSum χ (ψ.mulShift t))) =
        (a * a) * (gaussSum χ (ψ.mulShift z) *
          star (gaussSum χ (ψ.mulShift t))) := by ring
    _ = ((Fintype.card F : ℂ))⁻¹ * ((Fintype.card F : ℂ) * χ (t / z)) := by
      rw [haa, gaussSum_mul_star_gaussSum χ hχ hψ hz ht]
    _ = χ (t / z) := by
      have hq : (Fintype.card F : ℂ) ≠ 0 := by
        have hpos : 0 < Fintype.card F := Fintype.card_pos
        exact_mod_cast hpos.ne'
      field_simp [hq]

/-- The paper's printed right-hand side, written with the inverse character. -/
theorem paperGauss_mul_star_inv (χ : MulChar F ℂ) (hχ : χ ≠ 1)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {z t : F} (hz : z ≠ 0) (ht : t ≠ 0) :
    paperGauss χ ψ z * star (paperGauss χ ψ t) = χ⁻¹ (z / t) := by
  rw [paperGauss_mul_star χ hχ hψ hz ht, MulChar.inv_apply']
  rw [inv_div]

end Qatlib.Papers.HSPAffine13.MainResults
