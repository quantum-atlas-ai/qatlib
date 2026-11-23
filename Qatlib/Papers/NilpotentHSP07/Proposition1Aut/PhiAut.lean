/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.NilpotentHSP07.MainResults.Nil2Defs

@[expose] public section

/-!
# The nonzero coordinate scalings as group automorphisms

Fixed source: [Ivanyos, Sanselme, Santha 2007](https://arxiv.org/abs/0707.1260),
Proposition 1.  In the coordinate model of a `p`-group of exponent `p` and nilpotency class two,
the map `phi j` scales the first coordinates by `j` and the second coordinates by `j * j`.  The
public library already proves that these maps are multiplicative (`phi_mul`), bijective for
nonzero `j` (`phi_bijective`), and compute the two power identities of Proposition 1 on the
derived subgroup (`phi_gPrime_pow`, `exists_zg`).

This module packages the nonzero scalings as actual group automorphisms, proves that composition
of scalings is scaling by the product, and bundles the family as a monoid homomorphism from the
unit group of `ZMod p`.  The coordinate model is required to have at least one first coordinate
(`0 < m`), so the statement is not about the degenerate trivial group.

## Main statements

* `phiAut` is the automorphism `phi j` for nonzero `j`.
* `phiAut_comp` identifies composition of two such automorphisms with `phi (j * k)`.
* `phiAutUnit` is the monoid homomorphism `(ZMod p)ˣ →* MulAut (Coord p m d)`.
* `proposition1_phi_automorphism` bundles the nonzero scalings and their derived-subgroup
  power law in the coordinate model.

## References

* [Ivanyos et al., 2007][IvanyosSanselmeSantha2007a], Proposition 1
-/

set_option autoImplicit false

namespace Qatlib.Papers.NilpotentHSP07.Proposition1Aut

open Qatlib.Papers.NilpotentHSP07.MainResults

variable {p m d : ℕ} [Fact p.Prime] [F : Nil2Form p m d]

omit F in
/-- Two coordinate scalings compose by multiplying their parameters.  This is the coordinate
form of the fact that the maps `phi j` form a multiplicative family. -/
theorem phi_comp (j k : ZMod p) (g : Coord p m d) :
    phi j (phi k g) = phi (j * k) g := by
  apply Coord.ext <;> funext i
  · simp only [phi, Pi.smul_apply, smul_smul]
  · simp only [phi, Pi.smul_apply, smul_smul]
    ring

/-- For nonzero `j`, the coordinate scaling `phi j` is a group automorphism.  This is the
automorphism assertion in [Ivanyos et al., Proposition 1][IvanyosSanselmeSantha2007a] in the
coordinate model. -/
noncomputable def phiAut (j : ZMod p) (hj : j ≠ 0) : Coord p m d ≃* Coord p m d where
  toFun := phi j
  invFun := phi j⁻¹
  left_inv g := by
    rw [phi_comp, inv_mul_cancel₀ hj, phi_one]
  right_inv g := by
    rw [phi_comp, mul_inv_cancel₀ hj, phi_one]
  map_mul' := phi_mul j

/-- The automorphism `phiAut j hj` acts by the coordinate scaling `phi j`. -/
@[simp] theorem phiAut_apply (j : ZMod p) (hj : j ≠ 0) (g : Coord p m d) :
    phiAut j hj g = phi j g := rfl

/-- The inverse automorphism acts by the inverse coordinate scaling. -/
@[simp] theorem phiAut_symm_apply (j : ZMod p) (hj : j ≠ 0) (g : Coord p m d) :
    (phiAut j hj).symm g = phi j⁻¹ g := rfl

/-- Composing two nonzero coordinate automorphisms is the coordinate automorphism with the
product parameter. -/
theorem phiAut_comp (j k : ZMod p) (hj : j ≠ 0) (hk : k ≠ 0) (g : Coord p m d) :
    phiAut j hj (phiAut k hk g) = phiAut (j * k) (mul_ne_zero hj hk) g := by
  simp only [phiAut_apply]
  exact phi_comp j k g

/-- On the derived subgroup `gPrime`, the automorphism `phiAut j` raises to the natural
representative of `j * j`.  This is the first power identity of
[Ivanyos et al., Proposition 1][IvanyosSanselmeSantha2007a], transported to the bundled
automorphism. -/
theorem phiAut_apply_gPrime (j : ZMod p) (hj : j ≠ 0) (z : Coord p m d)
    (hz : z ∈ gPrime (p := p) (m := m) (d := d)) :
    phiAut j hj z = z ^ (j * j).val := by
  simp only [phiAut_apply]
  exact phi_gPrime_pow j z hz

/-- The nonzero coordinate scalings assemble into a monoid homomorphism from the unit group of
`ZMod p` to the automorphism group of the coordinate model.  This is the bundled family of
automorphisms from [Ivanyos et al., Proposition 1][IvanyosSanselmeSantha2007a]. -/
noncomputable def phiAutUnit : (ZMod p)ˣ →* MulAut (Coord p m d) where
  toFun j := phiAut (j : ZMod p) (Units.ne_zero j)
  map_one' := by
    apply MulEquiv.ext
    intro g
    simp [phiAut, phi_one]
  map_mul' j k := by
    apply MulEquiv.ext
    intro g
    simp only [MulAut.mul_apply, phiAut_apply, phi_comp, Units.val_mul]

/-- The bundled family evaluates to the coordinate scaling on every element. -/
@[simp] theorem phiAutUnit_apply (j : (ZMod p)ˣ) (g : Coord p m d) :
    phiAutUnit j g = phi (j : ZMod p) g := rfl

/-- The nonzero part of the derived-subgroup power law of [IvanyosSanselmeSantha2007a],
Proposition 1, in the coordinate model: the
nonzero scalings form a family of group automorphisms, and on the derived subgroup each one acts
by the power `j * j`.  The hypothesis `0 < m` excludes the degenerate coordinate model with no
first coordinate. -/
theorem proposition1_phi_automorphism (_hm : 0 < m) :
    ∃ Phi : (ZMod p)ˣ →* MulAut (Coord p m d),
      (∀ (j : (ZMod p)ˣ) (g : Coord p m d), Phi j g = phi (j : ZMod p) g) ∧
        (∀ (j : (ZMod p)ˣ) (z : Coord p m d), z ∈ gPrime →
          Phi j z = z ^ (((j : ZMod p) * (j : ZMod p))).val) := by
  refine ⟨phiAutUnit, fun _ _ => rfl, ?_⟩
  intro j z hz
  rw [phiAutUnit_apply]
  exact phi_gPrime_pow (j : ZMod p) z hz

end Qatlib.Papers.NilpotentHSP07.Proposition1Aut
