/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.ZMod.Aut
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic

/-!
# Trivial cyclic actions and direct-product splittings

`mulAutZModEquivUnits` identifies cyclic-group automorphisms with modular units, giving the
automorphism-group cardinality as Euler’s totient. A prime-order cyclic group acts trivially
when that prime does not divide this cardinality; the resulting semidirect products split as
direct products. See [ChiKimLee2006] for the mathematical setting.

## Main statements

* `theorem1_cyclic_factor_action_trivial`: proves triviality for a distinct prime-power factor
  under the stated divisibility restriction.
* `theorem1_cyclic_factor_split`: produces the corresponding direct-product isomorphism.
* `semidirectProductTrivialEquiv`: constructs a direct-product equivalence for any trivial
  action.

## References

* [Chi et al., 2006][ChiKimLee2006]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SemiDirectHSP06.MainResults

open Multiplicative

/-- The multiplicative equivalence between automorphisms of the cyclic group modulo `n` and
units modulo `n`. -/
def mulAutZModEquivUnits (n : ℕ) :
    MulAut (Multiplicative (ZMod n)) ≃* (ZMod n)ˣ :=
  (MulAutMultiplicative (ZMod n)).trans (ZMod.AddAutEquivUnits n).toMultiplicative

/-- For nonzero `n`, the automorphism group of the cyclic group modulo `n` has cardinality
`n.totient`. See [Chi et al., 2006, Theorem 1][ChiKimLee2006]. -/
theorem card_mulAut_multiplicative_zmod (n : ℕ) [NeZero n] :
    Fintype.card (MulAut (Multiplicative (ZMod n))) = n.totient := by
  rw [Fintype.card_congr (mulAutZModEquivUnits n).toEquiv, ZMod.card_units_eq_totient]

/-- Every homomorphism from a cyclic group of prime order `p` to a finite group of cardinality
coprime to `p` is trivial. See [Chi et al., 2006, Theorem 1][ChiKimLee2006]. -/
theorem monoidHom_zmod_prime_eq_one_of_coprime_card
    {B : Type*} [Group B] [Fintype B] {p : ℕ} (hp : p.Prime)
    (hcop : Nat.Coprime p (Fintype.card B))
    (φ : Multiplicative (ZMod p) →* B) : φ = 1 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hgen : ∀ x : Multiplicative (ZMod p),
      x = Multiplicative.ofAdd (1 : ZMod p) ^ x.toAdd.val := by
    intro x
    nth_rewrite 1 [← ofAdd_toAdd x]
    rw [← ofAdd_nsmul]
    congr 1
    rw [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
  have hgp : Multiplicative.ofAdd (1 : ZMod p) ^ p = 1 := by
    rw [← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_self,
      ofAdd_zero]
  have hgpow : φ (Multiplicative.ofAdd (1 : ZMod p)) = 1 := by
    have h1 : (φ (Multiplicative.ofAdd (1 : ZMod p))) ^ p = 1 := by
      rw [← map_pow, hgp, map_one]
    have hdvd : orderOf (φ (Multiplicative.ofAdd (1 : ZMod p))) ∣ p :=
      orderOf_dvd_iff_pow_eq_one.mpr h1
    have hdvdB : orderOf (φ (Multiplicative.ofAdd (1 : ZMod p))) ∣ Fintype.card B := by
      rw [Fintype.card_eq_nat_card]
      exact orderOf_dvd_natCard (φ (Multiplicative.ofAdd (1 : ZMod p)))
    have hgcd : orderOf (φ (Multiplicative.ofAdd (1 : ZMod p))) ∣
        Nat.gcd p (Fintype.card B) := Nat.dvd_gcd hdvd hdvdB
    rw [Nat.Coprime.gcd_eq_one hcop] at hgcd
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hgcd)
  refine MonoidHom.ext fun x => ?_
  rw [hgen x, map_pow, hgpow, one_pow]
  rfl

/-- For distinct primes `p` and `q`, positive `r`, and `p` not dividing `q - 1`, every action of
the cyclic group of order `p` on the cyclic group of order `q ^ r` is trivial. See [Chi et
al., 2006, Theorem 1][ChiKimLee2006]. -/
theorem theorem1_cyclic_factor_action_trivial
    {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hr : 0 < r)
    (hq1 : ¬ p ∣ q - 1)
    (φ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod (q ^ r)))) :
    φ = 1 := by
  haveI : NeZero (q ^ r) := ⟨(pow_pos hq.pos r).ne'⟩
  apply monoidHom_zmod_prime_eq_one_of_coprime_card hp
  rw [card_mulAut_multiplicative_zmod, Nat.totient_prime_pow hq hr]
  apply (Nat.Prime.coprime_iff_not_dvd hp).mpr
  intro h
  have hqnp : ¬ p ∣ q := fun hd => hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp hd)
  rcases hp.dvd_mul.mp h with h1 | h2
  · exact hqnp (hp.dvd_of_dvd_pow h1)
  · exact hq1 h2

/-- For prime `p` and nonzero `n`, every cyclic order-`p` action on the cyclic group modulo `n`
is trivial if `p` does not divide `n.totient`. See [Chi et al., 2006, Theorem
1][ChiKimLee2006]. -/
theorem theorem1_action_trivial_of_not_dvd_totient
    {n p : ℕ} (hp : p.Prime) [NeZero n] (hn : ¬ p ∣ n.totient)
    (φ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod n))) : φ = 1 := by
  apply monoidHom_zmod_prime_eq_one_of_coprime_card hp
  rw [card_mulAut_multiplicative_zmod]
  exact (Nat.Prime.coprime_iff_not_dvd hp).mpr hn

/-- The multiplicative equivalence from a semidirect product with trivial action to the direct
product of its factors. -/
def semidirectProductTrivialEquiv (N G : Type*) [Group N] [Group G] :
    SemidirectProduct N G (1 : G →* MulAut N) ≃* N × G where
  toFun x := (x.left, x.right)
  invFun y := ⟨y.1, y.2⟩
  left_inv x := by cases x; rfl
  right_inv y := rfl
  map_mul' x y := by
    ext <;> simp [SemidirectProduct.mul_left, SemidirectProduct.mul_right]

/-- For distinct primes `p` and `q`, positive `r`, and `p` not dividing `q - 1`, the semidirect
product for any such cyclic action is isomorphic to the direct product. See [Chi et al.,
2006, Theorem 1][ChiKimLee2006]. -/
theorem theorem1_cyclic_factor_split
    {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hr : 0 < r)
    (hq1 : ¬ p ∣ q - 1)
    (φ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod (q ^ r)))) :
    Nonempty (SemidirectProduct (Multiplicative (ZMod (q ^ r)))
        (Multiplicative (ZMod p)) φ ≃*
      (Multiplicative (ZMod (q ^ r)) × Multiplicative (ZMod p))) := by
  rw [theorem1_cyclic_factor_action_trivial hp hq hpq hr hq1 φ]
  exact ⟨semidirectProductTrivialEquiv _ _⟩

/-- A semidirect product of commutative groups with trivial action has commuting elements. -/
theorem semidirectProduct_comm_of_trivial_action
    {N G : Type*} [CommGroup N] [CommGroup G]
    (a b : SemidirectProduct N G (1 : G →* MulAut N)) : a * b = b * a := by
  apply (semidirectProductTrivialEquiv N G).injective
  simp only [map_mul]
  exact mul_comm _ _

end Qatlib.Papers.SemiDirectHSP06.MainResults
