/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SemiDirectHSP06.MainResults.Defs
import Qatlib.Papers.SemiDirectHSP06.MainResults.Lemma1Componentwise
import Qatlib.Papers.SemiDirectHSP06.MainResults.SdpSplitTrivialFirst
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Splitting a coprime cyclic factor from a semidirect product

The induced first-coordinate homomorphisms are upgraded to automorphisms and assembled into
`sdpFstAction`. For distinct primes with `p` not dividing `q - 1`, this action is trivial, so
`lemma2_factor_decomposition` splits off the cyclic group of order `q ^ s` as a direct factor.
See [ChiKimLee2006] for the mathematical setting.

## Main statements

* `sdp_action_trivial_first`: shows that the action fixes the first cyclic factor pointwise.
* `lemma2_factor_decomposition`: produces an action on the remaining factor and a direct-product
  decomposition.

## References

* [Chi et al., 2006][ChiKimLee2006]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SemiDirectHSP06.MainResults

open SemidirectProduct

variable {p q s r : ℕ}

/-- Every element of the multiplicatively written cyclic group modulo nonzero `n` has `n`th
power one. -/
lemma ofAdd_pow_card (n : ℕ) [NeZero n] (x : Multiplicative (ZMod n)) : x ^ n = 1 := by
  have hx : x = Multiplicative.ofAdd x.toAdd := by simp
  rw [hx, ← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self]
  simp

/-- If `k` is coprime to nonzero `n`, an element of the cyclic group modulo `n` whose `k`th
power is one is the identity. -/
lemma mul_eq_one_of_pow_eq_one {n k : ℕ} [NeZero n] (hcop : Nat.Coprime k n)
    {x : Multiplicative (ZMod n)} (h : x ^ k = 1) : x = 1 := by
  have hx : x = Multiplicative.ofAdd x.toAdd := by simp
  rw [hx] at h
  have hns : Multiplicative.ofAdd ((k : ℕ) • x.toAdd) = 1 := by
    rw [ofAdd_nsmul]
    exact h
  have hy : (k : ℕ) • x.toAdd = 0 := by
    have := congrArg Multiplicative.toAdd hns
    simpa using this
  have hz : x.toAdd = 0 := zmod_eq_zero_of_nsmul_eq_zero hcop hy
  rw [hx, hz]
  simp

/-- For distinct primes, applying the product action to an element of the first cyclic factor
leaves its second coordinate equal to one. -/
lemma sdp_second_coord_trivial (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (φ : Multiplicative (ZMod p) →*
      MulAut (Multiplicative (ZMod (q ^ s)) × Multiplicative (ZMod (p ^ r))))
    (g : Multiplicative (ZMod p)) (a : Multiplicative (ZMod (q ^ s))) :
    (φ g (a, 1)).2 = 1 := by
  haveI : NeZero (q ^ s) := ⟨pow_ne_zero _ hq.ne_zero⟩
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hpair : ((a, 1) : Multiplicative (ZMod (q ^ s)) ×
      Multiplicative (ZMod (p ^ r))) ^ (q ^ s) = 1 := by
    ext <;> simp [ofAdd_pow_card]
  have hFpow : (φ g (a, 1)) ^ (q ^ s) = 1 := by
    rw [← map_pow, hpair, map_one]
  have hbpow : ((φ g (a, 1)).2) ^ (q ^ s) = 1 := by
    have := congrArg Prod.snd hFpow
    simpa using this
  exact mul_eq_one_of_pow_eq_one (coprime_prime_powers hp hq hpq) hbpow

/-- For distinct primes, applying the product action to an element of the second cyclic factor
leaves its first coordinate equal to one. -/
lemma sdp_first_coord_trivial (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (φ : Multiplicative (ZMod p) →*
      MulAut (Multiplicative (ZMod (q ^ s)) × Multiplicative (ZMod (p ^ r))))
    (g : Multiplicative (ZMod p)) (b : Multiplicative (ZMod (p ^ r))) :
    (φ g (1, b)).1 = 1 := by
  haveI : NeZero (q ^ s) := ⟨pow_ne_zero _ hq.ne_zero⟩
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hpair : ((1, b) : Multiplicative (ZMod (q ^ s)) ×
      Multiplicative (ZMod (p ^ r))) ^ (p ^ r) = 1 := by
    ext <;> simp [ofAdd_pow_card]
  have hFpow : (φ g (1, b)) ^ (p ^ r) = 1 := by
    rw [← map_pow, hpair, map_one]
  have habpow : ((φ g (1, b)).1) ^ (p ^ r) = 1 := by
    have := congrArg Prod.fst hFpow
    simpa using this
  exact mul_eq_one_of_pow_eq_one (coprime_prime_powers hp hq hpq).symm habpow

/-- The endomorphism of the first cyclic factor obtained by embedding it into the product,
applying `φ g`, and projecting back. -/
def sdpFstHom
    (φ : Multiplicative (ZMod p) →*
      MulAut (Multiplicative (ZMod (q ^ s)) × Multiplicative (ZMod (p ^ r))))
    (g : Multiplicative (ZMod p)) :
    Multiplicative (ZMod (q ^ s)) →* Multiplicative (ZMod (q ^ s)) where
  toFun a := (φ g (a, 1)).1
  map_one' := by
    change (φ g ((1 : Multiplicative (ZMod (q ^ s))), 1)).1 = 1
    rw [show ((1 : Multiplicative (ZMod (q ^ s))), (1 : Multiplicative (ZMod (p ^ r)))) =
      (1 : Multiplicative (ZMod (q ^ s)) × Multiplicative (ZMod (p ^ r))) from rfl, map_one]
    rfl
  map_mul' a b := by
    have hprod : (φ g) (a * b, 1) = (φ g) (a, 1) * (φ g) (b, 1) := by
      rw [← map_mul]
      congr 1
      ext <;> simp
    exact congrArg Prod.fst hprod

/-- The induced first-coordinate homomorphism is injective if the action preserves the first
factor. -/
lemma sdpFstHom_injective
    (φ : Multiplicative (ZMod p) →*
      MulAut (Multiplicative (ZMod (q ^ s)) × Multiplicative (ZMod (p ^ r))))
    (hA : ∀ (g : Multiplicative (ZMod p)) (a : Multiplicative (ZMod (q ^ s))),
      (φ g (a, 1)).2 = 1)
    (g : Multiplicative (ZMod p)) : Function.Injective (sdpFstHom φ g) := by
  intro a b hab
  have hpairs : φ g (a, 1) = φ g (b, 1) := by
    ext
    · exact hab
    · rw [hA, hA]
  have := (φ g).injective hpairs
  simpa using congrArg Prod.fst this

/-- For prime `q`, the induced first-coordinate homomorphism is surjective under the
factor-preservation hypothesis. -/
lemma sdpFstHom_surjective (hq : q.Prime)
    (φ : Multiplicative (ZMod p) →*
      MulAut (Multiplicative (ZMod (q ^ s)) × Multiplicative (ZMod (p ^ r))))
    (hA : ∀ (g : Multiplicative (ZMod p)) (a : Multiplicative (ZMod (q ^ s))),
      (φ g (a, 1)).2 = 1)
    (g : Multiplicative (ZMod p)) : Function.Surjective (sdpFstHom φ g) := by
  haveI : NeZero (q ^ s) := ⟨pow_ne_zero _ hq.ne_zero⟩
  haveI : Finite (Multiplicative (ZMod (q ^ s))) := inferInstance
  exact (Finite.injective_iff_surjective).mp (sdpFstHom_injective φ hA g)

/-- The automorphism of the first cyclic factor obtained from the induced homomorphism under the
factor-preservation hypothesis. -/
def sdpFstAut (hq : q.Prime)
    (φ : Multiplicative (ZMod p) →*
      MulAut (Multiplicative (ZMod (q ^ s)) × Multiplicative (ZMod (p ^ r))))
    (hA : ∀ (g : Multiplicative (ZMod p)) (a : Multiplicative (ZMod (q ^ s))),
      (φ g (a, 1)).2 = 1)
    (g : Multiplicative (ZMod p)) : MulAut (Multiplicative (ZMod (q ^ s))) :=
  MulEquiv.ofBijective (sdpFstHom φ g)
    ⟨sdpFstHom_injective φ hA g, sdpFstHom_surjective hq φ hA g⟩

/-- The induced first-factor automorphism sends `a` to the first coordinate of `φ g (a, 1)`. -/
lemma sdpFstAut_apply (hq : q.Prime)
    (φ : Multiplicative (ZMod p) →*
      MulAut (Multiplicative (ZMod (q ^ s)) × Multiplicative (ZMod (p ^ r))))
    (hA : ∀ (g : Multiplicative (ZMod p)) (a : Multiplicative (ZMod (q ^ s))),
      (φ g (a, 1)).2 = 1)
    (g : Multiplicative (ZMod p)) (a : Multiplicative (ZMod (q ^ s))) :
    sdpFstAut hq φ hA g a = (φ g (a, 1)).1 := rfl

/-- The induced first-factor automorphisms respect multiplication of acting-group elements. -/
lemma sdpFstAut_map_mul (hq : q.Prime)
    (φ : Multiplicative (ZMod p) →*
      MulAut (Multiplicative (ZMod (q ^ s)) × Multiplicative (ZMod (p ^ r))))
    (hA : ∀ (g : Multiplicative (ZMod p)) (a : Multiplicative (ZMod (q ^ s))),
      (φ g (a, 1)).2 = 1)
    (g1 g2 : Multiplicative (ZMod p)) :
    sdpFstAut hq φ hA (g1 * g2) =
      sdpFstAut hq φ hA g1 * sdpFstAut hq φ hA g2 := by
  ext a
  change (φ (g1 * g2) (a, 1)).1 = (φ g1 ((φ g2 (a, 1)).1, 1)).1
  rw [map_mul]
  have hpair : φ g2 (a, 1) = ((φ g2 (a, 1)).1, 1) := by
    ext <;> simp [hA]
  have key : (φ g1) ((φ g2 (a, 1)).1, 1) = (φ g1) (φ g2 (a, 1)) := by rw [hpair]
  rw [key]
  rfl

/-- The action on the first cyclic factor obtained from `φ` under the factor-preservation
hypothesis. -/
def sdpFstAction (hq : q.Prime)
    (φ : Multiplicative (ZMod p) →*
      MulAut (Multiplicative (ZMod (q ^ s)) × Multiplicative (ZMod (p ^ r))))
    (hA : ∀ (g : Multiplicative (ZMod p)) (a : Multiplicative (ZMod (q ^ s))),
      (φ g (a, 1)).2 = 1) :
    Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod (q ^ s))) where
  toFun g := sdpFstAut hq φ hA g
  map_one' := by
    ext a
    change (φ 1 (a, 1)).1 = a
    simp
  map_mul' := sdpFstAut_map_mul hq φ hA

/-- For distinct primes `p` and `q`, positive `s`, and `p` not dividing `q - 1`, the action
fixes every element of the first cyclic factor. -/
lemma sdp_action_trivial_first (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hs : 0 < s) (hndvd : ¬ p ∣ q - 1)
    (φ : Multiplicative (ZMod p) →*
      MulAut (Multiplicative (ZMod (q ^ s)) × Multiplicative (ZMod (p ^ r)))) :
    ∀ (g : Multiplicative (ZMod p)) (a : Multiplicative (ZMod (q ^ s))),
      φ g (a, 1) = (a, 1) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (q ^ s) := ⟨pow_ne_zero _ hq.ne_zero⟩
  have hA := sdp_second_coord_trivial hp hq hpq φ
  haveI : Finite (Multiplicative (ZMod (q ^ s))) := inferInstance
  haveI : IsCyclic (Multiplicative (ZMod (q ^ s))) := inferInstance
  have hcardN1 : Nat.card (Multiplicative (ZMod (q ^ s))) = q ^ s := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  have hcardAut : Nat.card (MulAut (Multiplicative (ZMod (q ^ s)))) =
      q ^ (s - 1) * (q - 1) := by
    rw [IsCyclic.card_mulAut, hcardN1, Nat.totient_prime_pow hq hs]
  have hcop : Nat.Coprime p (Nat.card (MulAut (Multiplicative (ZMod (q ^ s))))) := by
    rw [hcardAut]
    refine (Nat.Prime.coprime_iff_not_dvd hp).2 ?_
    intro hdvd
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h1 | h2
    · have hpq' : p = q :=
        (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow h1)
      exact hpq hpq'
    · exact hndvd h2
  have hgen : (Multiplicative.ofAdd (1 : ZMod p)) ^ p = 1 := by
    rw [ofAdd_one_pow]
    simp
  have hpow : (sdpFstAction hq φ hA
      (Multiplicative.ofAdd (1 : ZMod p))) ^ p = 1 := by
    rw [← map_pow, hgen, map_one]
  have hdvd1 : orderOf (sdpFstAction hq φ hA
      (Multiplicative.ofAdd (1 : ZMod p))) ∣ p := by
    rw [orderOf_dvd_iff_pow_eq_one]
    exact hpow
  have hdvd2 : orderOf (sdpFstAction hq φ hA
      (Multiplicative.ofAdd (1 : ZMod p))) ∣
      Nat.card (MulAut (Multiplicative (ZMod (q ^ s)))) :=
    orderOf_dvd_natCard _
  have horder : orderOf (sdpFstAction hq φ hA
      (Multiplicative.ofAdd (1 : ZMod p))) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2
  have hone : sdpFstAction hq φ hA
      (Multiplicative.ofAdd (1 : ZMod p)) = 1 := orderOf_eq_one_iff.mp horder
  intro g a
  have hg : g = (Multiplicative.ofAdd (1 : ZMod p)) ^ g.toAdd.val := by
    rw [ofAdd_one_pow]
    exact (congrArg Multiplicative.ofAdd (ZMod.natCast_zmod_val g.toAdd)).symm
  have hfg : sdpFstAction hq φ hA g = 1 := by
    rw [hg, map_pow, hone, one_pow]
  have hfirst : (φ g (a, 1)).1 = a := by
    have h1a : sdpFstAction hq φ hA g a = a := by
      rw [hfg]
      rfl
    simpa [sdpFstAction, sdpFstAut, sdpFstHom] using h1a
  exact Prod.ext hfirst (hA g a)

/-- For distinct primes `p` and `q`, positive exponents, and `p` not dividing `q - 1`, the
semidirect product is isomorphic to the first cyclic factor times a semidirect product on
the second factor. See [Chi et al., 2006, Lemma 2][ChiKimLee2006]. -/
theorem lemma2_factor_decomposition
    {p q s r : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hs : 0 < s) (_hr : 0 < r) (hndvd : ¬ p ∣ q - 1)
    (φ : Multiplicative (ZMod p) →*
        MulAut (Multiplicative (ZMod (q ^ s)) × Multiplicative (ZMod (p ^ r)))) :
    ∃ ψ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod (p ^ r))),
      Nonempty
        (SemidirectProduct (Multiplicative (ZMod (q ^ s)) × Multiplicative (ZMod (p ^ r)))
            (Multiplicative (ZMod p)) φ ≃*
          (Multiplicative (ZMod (q ^ s)) ×
            SemidirectProduct (Multiplicative (ZMod (p ^ r)))
              (Multiplicative (ZMod p)) ψ)) := by
  have h1 := sdp_action_trivial_first hp hq hpq hs hndvd φ
  have h2 := sdp_first_coord_trivial hp hq hpq φ
  exact ⟨sdp_sndAction h1 h2, sdp_split_trivial_first (φ := φ) h1 h2⟩

end Qatlib.Papers.SemiDirectHSP06.MainResults
