/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.CfOrder.CompositeOrderDlogSampling
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Exact-order sampling support over cyclic multiplicative groups

Fixed source: quant-ph/9508027v2, section 6, printed pp.23–24.
The finite group transport below uses Fourier registers of exact size r, the
known generator order. It is not the source's off-grid power-of-two clock
p < q < 2p, and it does not implement a polynomial-time group operation or
order-finding subroutine. The inverse-record identity is algebraic correctness,
not a computational cost theorem.
The odd prime-power example is the unit group of the ring ZMod (p^alpha),
not the multiplicative group of a field of cardinality p^alpha. These are
separate mathematical objects; no finite-field instance is asserted here.
Thus this module supplies partial support for c016, not its full algorithm.
-/

set_option autoImplicit false

namespace Qatlib.Papers.ShorFactoring97.DlogSamplingLaw

open Qatlib.Concepts.HspRecovery.CfOrder

/-! ## §1. The record law over a multiplicative group -/

/-- **The §6 record law does not use the additive structure of `Z_p`.**  For any
finite commutative group `G`, a generator `g` of order exactly `r` (so `g^r = 1`
and `x ↦ g^x` is injective on `ZMod r`), and a hidden value `h = g^d`, the
record distribution of the two-exponent oracle — the frozen `cyclicDlogRecordDist`
on the group tag `Additive G` — puts probability `1/r` on the line `b = d·a` and
`0` elsewhere.  This supplies exact-order algebraic support for the generalization, but
not the source off-grid sampling law or an efficient algorithm. -/
theorem mulDlogLineLaw (r : ℕ) [NeZero r] (G : Type) [CommGroup G] [Fintype G]
    [DecidableEq G] (g h : G) (d a b : ZMod r) (hr : 2 ≤ r) (hgr : g ^ r = 1)
    (hinj : Function.Injective (fun x : ZMod r => g ^ x.val)) (hh : h = g ^ d.val) :
    (cyclicDlogRecordDist r (Additive.ofMul g) (Additive.ofMul h)).prob (a, b) =
      if b = d * a then (1 : ℝ) / (r : ℝ) else 0 := by
  have hp : r • Additive.ofMul g = 0 := by
    rw [← ofMul_pow, hgr, ofMul_one]
  have hinj' : Function.Injective (fun x : ZMod r => x.val • Additive.ofMul g) := by
    intro x y hxy
    simp only at hxy
    exact hinj hxy
  have hh' : Additive.ofMul h = d.val • Additive.ofMul g := by
    simp [hh]
  simpa using composite_dlog_actual_line_law r (Additive G) (Additive.ofMul g)
    (Additive.ofMul h) d a b hr hp hinj' hh'

/-! ## §2. Every finite cyclic group supplies a generator of known order -/

/-- A finite cyclic group has an element whose order is the group order: the
generator whose order the algorithm is assumed to know. -/
theorem cyclic_generator_order (G : Type) [CommGroup G] [Fintype G] [IsCyclic G] :
    ∃ g : G, orderOf g = Fintype.card G := by
  obtain ⟨g, hg⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp ‹IsCyclic G›
  exact ⟨g, by rwa [Nat.card_eq_fintype_card] at hg⟩

/-- **The §6 sampling law for any finite cyclic group.**  With `g` of order equal
to the group order `|G|` and hidden value `h = g^d`, the record law is `1/|G|` on
the line `b = d·a`.  No property special to `Z_p` enters. -/
theorem cyclic_dlog_line_law (G : Type) [CommGroup G] [Fintype G] [DecidableEq G]
    (g h : G) (hne : Fintype.card G ≠ 0) (hr : 2 ≤ Fintype.card G)
    (horder : orderOf g = Fintype.card G) (d a b : ZMod (Fintype.card G))
    (hh : h = g ^ d.val) :
    (cyclicDlogRecordDist (Fintype.card G) (Additive.ofMul g) (Additive.ofMul h)).prob (a, b) =
      if b = d * a then (1 : ℝ) / (Fintype.card G : ℝ) else 0 := by
  haveI : NeZero (Fintype.card G) := ⟨hne⟩
  refine mulDlogLineLaw (Fintype.card G) G g h d a b hr ?_ ?_ hh
  · rw [← horder]
    exact pow_orderOf_eq_one g
  · intro x y hxy
    have hmod : x.val ≡ y.val [MOD orderOf g] := pow_eq_pow_iff_modEq.mp hxy
    rw [horder, Nat.ModEq] at hmod
    rw [Nat.mod_eq_of_lt (ZMod.val_lt x), Nat.mod_eq_of_lt (ZMod.val_lt y)] at hmod
    exact ZMod.val_injective _ hmod

/-! ## §3. The `Z_{p^α}` instance -/

/-- For an odd prime `p`, the unit group of `ZMod (p^α)` is cyclic — the
number-theoretic hypothesis the paper cites ("the multiplicative group `(mod p^α)`
for any odd prime power `p^α` is cyclic").  The side condition `NeZero (p^α)` is
automatic for a prime `p`. -/
theorem units_prime_pow_isCyclic (p α : ℕ) [NeZero (p ^ α)] (hp : p.Prime) (hp2 : p ≠ 2) :
    IsCyclic (ZMod (p ^ α))ˣ :=
  ZMod.isCyclic_units_of_prime_pow p hp hp2 α

/-- The `Z_{p^α}` generator: a unit whose order is `φ(p^α)`, the order the
algorithm is assumed to know.  This is the paper's "for any odd prime power
`p^α`" instance of the general algorithm. -/
theorem units_prime_pow_generator (p α : ℕ) [NeZero (p ^ α)] (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ g : (ZMod (p ^ α))ˣ, orderOf g = Fintype.card (ZMod (p ^ α))ˣ ∧
      Fintype.card (ZMod (p ^ α))ˣ = Nat.totient (p ^ α) := by
  haveI := units_prime_pow_isCyclic p α hp hp2
  obtain ⟨g, hg⟩ := cyclic_generator_order (ZMod (p ^ α))ˣ
  exact ⟨g, hg, ZMod.card_units_eq_totient (p ^ α)⟩

/-- **The §6 record law over the unit group of `ZMod n`.**  For a generator `g` of
the unit group of order `|(ZMod n)ˣ|` and hidden value `h = g^d`, the record
distribution is `1/|(ZMod n)ˣ|` exactly on the good line.  This is the form the
general algorithm takes on any ring whose unit group is cyclic; the paper's
`Z_{p^α}` case is supplied by `units_prime_pow_dlog` below. -/
theorem units_zmod_line_law (n : ℕ) [NeZero n] (g h : (ZMod n)ˣ)
    (hne : Fintype.card (ZMod n)ˣ ≠ 0) (hr : 2 ≤ Fintype.card (ZMod n)ˣ)
    (horder : orderOf g = Fintype.card (ZMod n)ˣ)
    (d a b : ZMod (Fintype.card (ZMod n)ˣ)) (hh : h = g ^ d.val) :
    (cyclicDlogRecordDist (Fintype.card (ZMod n)ˣ) (Additive.ofMul g)
        (Additive.ofMul h)).prob (a, b) =
      if b = d * a then (1 : ℝ) / (Fintype.card (ZMod n)ˣ : ℝ) else 0 :=
  cyclic_dlog_line_law (ZMod n)ˣ g h hne hr horder d a b hh

/-- **Exact-order sampling over the units of an odd-prime-power modular ring.**  There is a
generator `g` of the unit group of `ZMod (p^α)` whose order is `φ(p^α)`, and for
every hidden value `h = g^d` the §6 record law puts probability `1/|(ZMod p^α)ˣ|`
on the good line.  This is a modular-ring unit-group example, not a finite-field instance.
The exact-order record law has no off-grid circuit or computational cost claim. -/
theorem units_prime_pow_dlog (p α : ℕ) [NeZero (p ^ α)] (hp : p.Prime) (hp2 : p ≠ 2)
    (hr : 2 ≤ Fintype.card (ZMod (p ^ α))ˣ) :
    ∃ g : (ZMod (p ^ α))ˣ, orderOf g = Fintype.card (ZMod (p ^ α))ˣ ∧
      Fintype.card (ZMod (p ^ α))ˣ = Nat.totient (p ^ α) ∧
      ∀ (h : (ZMod (p ^ α))ˣ) (d a b : ZMod (Fintype.card (ZMod (p ^ α))ˣ)),
        h = g ^ d.val →
        (cyclicDlogRecordDist (Fintype.card (ZMod (p ^ α))ˣ) (Additive.ofMul g)
            (Additive.ofMul h)).prob (a, b) =
          if b = d * a then (1 : ℝ) / (Fintype.card (ZMod (p ^ α))ˣ : ℝ) else 0 := by
  obtain ⟨g, horder, hcard⟩ := units_prime_pow_generator p α hp hp2
  refine ⟨g, horder, hcard, ?_⟩
  intro h d a b hh
  exact units_zmod_line_law (p ^ α) g h (by omega) hr horder d a b hh

/-! ## §4. Recovery needs only multiplication and inversion -/

/-- A good record determines the hidden exponent with one multiplication by an
inverse: this establishes algebraic correctness only. No polynomial-time implementation
of the group operations or of the inverse modulo r is certified. -/
theorem good_record_dlog_recovery (r : ℕ) [NeZero r] (d a b : ZMod r) (u : (ZMod r)ˣ)
    (hu : (u : ZMod r) = a) (hba : b = d * a) :
    b * ((u⁻¹ : (ZMod r)ˣ) : ZMod r) = d := by
  rw [hba, ← hu]
  show d * (u : ZMod r) * ((u⁻¹ : (ZMod r)ˣ) : ZMod r) = d
  rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]

end Qatlib.Papers.ShorFactoring97.DlogSamplingLaw
