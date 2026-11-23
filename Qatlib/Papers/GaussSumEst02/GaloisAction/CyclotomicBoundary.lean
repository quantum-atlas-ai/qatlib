/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.NumberTheory.Cyclotomic.Gal
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

@[expose] public section

/-!
# Corrected boundary for the Section 5.2 cyclotomic automorphisms

Fixed source: [van Dam and Seroussi, 2002](https://arxiv.org/abs/quant-ph/0207131),
Section 5.2 (page 6).
The source proposes, for `m = q - 1`, a field automorphism fixing `ζ_p` and sending
`ζ_m ↦ ζ_m^a` in order to transport the Gauss sum `G(χ, β)` to `G(χ^a, β)`.  A
unital homomorphism between fields is injective and preserves the exact multiplicative
order of roots of unity. For `gcd(a, m) > 1` the prescription `ζ_m ↦ ζ_m^a`
therefore cannot define a field map, even after adjoining `ζ_p`.

This module formalizes the corrected algebraic boundary: the automorphism exists
exactly for units `a ∈ (ZMod m)ˣ` (realized by the standard cyclotomic Galois
group), it never exists for `gcd(a, m) > 1` (order obstruction), and the absolute
degree of the `m`-th cyclotomic field equals Euler's totient.  Transporting a
complex-valued Gauss sum into the cyclotomic field and evaluating numerically in
polylogarithmic time is not claimed; the large field degree is a representation
obstacle, not a proof that every classical approximation algorithm is slow.

## Main statements

* `zeta_aut_exists`: for `a` coprime to `m`, the ℚ-algebra automorphism of the
  `m`-th cyclotomic field sending `ζ` to `ζ^a` exists.
* `zeta_pow_not_primitive_of_not_coprime`: for `2 ≤ m` and `gcd(a, m) > 1`, the
  power `ζ^a` of a primitive `m`-th root `ζ` is not a primitive `m`-th root, so no
  field endomorphism can send `ζ ↦ ζ^a`.
* `cyclotomicField_finrank_rat`: the `m`-th cyclotomic field has ℚ-dimension `φ(m)`.
* `section52_cyclotomic_boundary`: the combined corrected boundary used downstream.

## References

* [van Dam and Seroussi, 2002][VanDamSeroussi2002]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.GaussSumEst02.GaloisAction.CyclotomicBoundary

open Polynomial IsCyclotomicExtension

/-- The standard library instances for the singleton cyclotomic extension are keyed
by a `match` on the modulus, which blocks type-class synthesis for a variable
modulus; this direct wrapper restores synthesizability in the statements below. -/
instance cyclotomicField_isCyclotomicExtension (m : ℕ) :
    IsCyclotomicExtension {m} ℚ (CyclotomicField m ℚ) :=
  CyclotomicField.instIsCyclotomicExtensionSingletonNatSetOfCharZero m ℚ

/-- The canonical primitive `m`-th root of unity in the `m`-th cyclotomic field over
the rationals. -/
noncomputable abbrev zetaRat (m : ℕ) [NeZero m] : CyclotomicField m ℚ :=
  IsCyclotomicExtension.zeta m ℚ (CyclotomicField m ℚ)

/-- The cyclotomic polynomial over the rationals is irreducible (Gauss). -/
theorem cyclotomic_irreducible_rat (m : ℕ) (hm : 0 < m) :
    Irreducible (cyclotomic m ℚ) :=
  cyclotomic.irreducible_rat hm

/-- For `a` coprime to `m`, the ℚ-algebra automorphism of the `m`-th cyclotomic
field sending the canonical primitive root `ζ` to `ζ^a` exists [VanDamSeroussi2002]. -/
theorem zeta_aut_exists (m a : ℕ) [NeZero m] (ha : a.Coprime m) :
    ∃ σ : CyclotomicField m ℚ ≃ₐ[ℚ] CyclotomicField m ℚ,
      σ (zetaRat m) = (zetaRat m) ^ a := by
  have hirr : Irreducible (cyclotomic m ℚ) := cyclotomic.irreducible_rat (NeZero.pos m)
  exact ⟨(IsCyclotomicExtension.fromZetaAut
    (hμ := (IsCyclotomicExtension.zeta_spec m ℚ (CyclotomicField m ℚ)).pow_of_coprime a ha)
    hirr), IsCyclotomicExtension.fromZetaAut_spec
      ((IsCyclotomicExtension.zeta_spec m ℚ (CyclotomicField m ℚ)).pow_of_coprime a ha) hirr⟩

/-- Every ℚ-algebra endomorphism of the `m`-th cyclotomic field is injective, since a
unital homomorphism from a field is injective. -/
theorem zeta_endomorphism_injective (m : ℕ) [NeZero m]
    (σ : CyclotomicField m ℚ →ₐ[ℚ] CyclotomicField m ℚ) :
    Function.Injective σ :=
  RingHom.injective σ.toRingHom

/-- For `2 ≤ m` and `gcd(a, m) > 1`, the power `ζ^a` of a primitive `m`-th root of
unity is not a primitive `m`-th root: its multiplicative order is `m / gcd(a, m)`,
which is strictly less than `m` [VanDamSeroussi2002].  Consequently the source's
prescription `ζ ↦ ζ^a` is not realized by any field endomorphism. -/
theorem zeta_pow_not_primitive_of_not_coprime (m a : ℕ) [NeZero m] (hm : 2 ≤ m)
    (ha : ¬ a.Coprime m) :
    ¬ IsPrimitiveRoot ((zetaRat m) ^ a) m := by
  have hζ : IsPrimitiveRoot (zetaRat m) m :=
    IsCyclotomicExtension.zeta_spec m ℚ (CyclotomicField m ℚ)
  have hg2 : 2 ≤ m.gcd a := by
    have hpos : 0 < m.gcd a := Nat.gcd_pos_of_pos_left a (by omega)
    rcases Nat.lt_or_ge (m.gcd a) 2 with h | h
    · have h1 : m.gcd a = 1 := by omega
      exact absurd (by rwa [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm] : a.Coprime m) ha
    · exact h
  intro hcontra
  have hordlt : orderOf ((zetaRat m) ^ a) < m := by
    rcases Nat.eq_zero_or_pos a with ha0 | ha0
    · subst ha0
      rw [pow_zero, orderOf_one]
      omega
    · rw [orderOf_pow' (zetaRat m) (Nat.ne_of_gt ha0), hζ.eq_orderOf.symm]
      exact Nat.div_lt_self (by omega) hg2
  have hEq : orderOf ((zetaRat m) ^ a) = m := hcontra.eq_orderOf.symm
  omega

/-- For `2 ≤ m` and `gcd(a, m) > 1`, no ℚ-algebra endomorphism `σ` of the `m`-th
cyclotomic field can satisfy `σ ζ = ζ^a`: injectivity would force `ζ^a` to be a
primitive `m`-th root, contradicting the order computation
`zeta_pow_not_primitive_of_not_coprime` [VanDamSeroussi2002]. -/
theorem zeta_no_endomorphism_zeta_pow_of_not_coprime (m a : ℕ) [NeZero m] (hm : 2 ≤ m)
    (ha : ¬ a.Coprime m) (σ : CyclotomicField m ℚ →ₐ[ℚ] CyclotomicField m ℚ) :
    σ (zetaRat m) ≠ (zetaRat m) ^ a := by
  have hζ : IsPrimitiveRoot (zetaRat m) m :=
    IsCyclotomicExtension.zeta_spec m ℚ (CyclotomicField m ℚ)
  intro hσ
  have hinj : Function.Injective σ := zeta_endomorphism_injective m σ
  have hσprim : IsPrimitiveRoot (σ (zetaRat m)) m := hζ.map_of_injective hinj
  rw [hσ] at hσprim
  exact zeta_pow_not_primitive_of_not_coprime m a hm ha hσprim

/-- The `m`-th cyclotomic field over the rationals has dimension `φ(m)`, Euler's
totient of `m`. Section 5.2 of [VanDamSeroussi2002] concerns the relative degree
of `ℚ(ζ_m, ζ_p)` over `ℚ(ζ_p)`, with `m` coprime to `p`. The equality here
computes the absolute degree of `ℚ(ζ_m)`. -/
theorem cyclotomicField_finrank_rat (m : ℕ) [NeZero m] :
    Module.finrank ℚ (CyclotomicField m ℚ) = m.totient :=
  IsCyclotomicExtension.finrank (CyclotomicField m ℚ)
    (cyclotomic.irreducible_rat (NeZero.pos m))

/-- The corrected Section 5.2 boundary in one statement: the cyclotomic Galois
action on the canonical primitive root `ζ` of the `m`-th cyclotomic field exists
exactly for the unit exponents `a ∈ (ZMod m)ˣ`; for `gcd(a, m) > 1` the source's
prescription is not a field map, and the ambient field has ℚ-dimension `φ(m)`.  The
transport of a complex-valued Gauss sum into the cyclotomic field, fixing `ζ_p`,
and any polylogarithmic numerical evaluation are not formalized here. -/
theorem section52_cyclotomic_boundary (m a : ℕ) [NeZero m] (hm : 2 ≤ m) :
    (a.Coprime m → ∃ σ : CyclotomicField m ℚ ≃ₐ[ℚ] CyclotomicField m ℚ,
      σ (zetaRat m) = (zetaRat m) ^ a) ∧
    (∀ σ : CyclotomicField m ℚ →ₐ[ℚ] CyclotomicField m ℚ,
      ¬ a.Coprime m → σ (zetaRat m) ≠ (zetaRat m) ^ a) ∧
    Module.finrank ℚ (CyclotomicField m ℚ) = m.totient :=
  ⟨fun ha => zeta_aut_exists m a ha,
   fun σ hna => zeta_no_endomorphism_zeta_pow_of_not_coprime m a hm hna σ,
   cyclotomicField_finrank_rat m⟩

end Qatlib.Papers.GaussSumEst02.GaloisAction.CyclotomicBoundary
