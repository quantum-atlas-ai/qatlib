/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SemidirectHSP07.MainResults.Group
import Mathlib.Algebra.Group.Prod
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.Nat.Totient

/-!
# Separating a trivially acted-on cyclic factor

This module supplies the group-theoretic facts behind the product isomorphism discussed in
[CosmePortugal2007]. It counts automorphisms of `Cyc n`, proves triviality of actions whose
source and automorphism-group orders are coprime, and shows that automorphisms of finite
products of coprime orders preserve the two factors.

The construction `semidirectProdMulEquiv` separates a factor on which the action is trivial. The
specialized `source_isomorphism` uses the explicit action `prodAct ψ` on the product of cyclic
factors.

## Main statements

- `card_mulAut_cyc` computes the automorphism-group cardinality as Euler's totient.
* `hom_to_mulAut_cyc_eq_one` proves triviality of the indicated action on the distinct-prime
  cyclic factor.
* `mulAut_prod_coprime_decomposes` expresses each automorphism as a pair of factor
  automorphisms.
* `semidirectProdMulEquiv` and `source_isomorphism` construct the product separation for the
  stated actions.

## References

* [Cosme and Portugal, 2007][CosmePortugal2007]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SemidirectHSP07.MainResults

open scoped commutatorElement

/-- For nonzero `n`, the automorphism group of `Cyc n` has natural cardinality `Nat.totient n`
[CosmePortugal2007]. -/
theorem card_mulAut_cyc (n : ℕ) [NeZero n] :
    Nat.card (MulAut (Cyc n)) = Nat.totient n := by
  have : Finite (Cyc n) := Finite.of_fintype (Multiplicative (ZMod n))
  have h : Nat.card (MulAut (Cyc n)) = Nat.totient (Nat.card (Cyc n)) :=
    IsCyclic.card_mulAut (Cyc n)
  simpa [card_Cyc] using h

/-- An action of a finite group `C` on a finite group `A` is trivial if the orders of `C` and
`MulAut A` are coprime. -/
theorem hom_to_mulAut_coprime_eq_one
    {C A : Type*} [Group C] [Group A] [Finite C] [Finite A]
    (hcop : Nat.Coprime (Nat.card C) (Nat.card (MulAut A)))
    (ψ : C →* MulAut A) : ψ = 1 := by
  have h1 : Nat.card ψ.range ∣ Nat.card C := Subgroup.card_range_dvd ψ
  have h2 : Nat.card ψ.range ∣ Nat.card (MulAut A) :=
    Subgroup.card_subgroup_dvd_card ψ.range
  have hg : Nat.card ψ.range ∣ Nat.gcd (Nat.card C) (Nat.card (MulAut A)) :=
    Nat.dvd_gcd h1 h2
  rw [Nat.coprime_iff_gcd_eq_one.mp hcop] at hg
  rw [← MonoidHom.range_eq_bot_iff]
  exact Subgroup.eq_bot_of_card_eq ψ.range (Nat.dvd_one.mp hg)

/-- For distinct primes `p` and `q`, positive `s`, and `p` not dividing `q - 1`, every action of
`Cyc (p ^ 2)` on `Cyc (q ^ s)` is trivial [CosmePortugal2007]. -/
theorem hom_to_mulAut_cyc_eq_one
    (p q s : ℕ) (hp : p.Prime) (hq : q.Prime) (hs : 0 < s)
    (hne : p ≠ q) (hnd : ¬ p ∣ (q - 1))
    (χ : Cyc (p ^ 2) →* MulAut (Cyc (q ^ s))) : χ = 1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hs)
  have : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  have : NeZero (q ^ (n + 1)) := ⟨pow_ne_zero (n + 1) hq.ne_zero⟩
  have : Finite (Cyc (p ^ 2)) := Finite.of_fintype (Multiplicative (ZMod (p ^ 2)))
  have : Finite (Cyc (q ^ (n + 1))) :=
    Finite.of_fintype (Multiplicative (ZMod (q ^ (n + 1))))
  have hpq : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hne
  have hq1 : Nat.Coprime p (q - 1) := hp.coprime_iff_not_dvd.mpr hnd
  have htot : Nat.totient (q ^ (n + 1)) = q ^ n * (q - 1) :=
    Nat.totient_prime_pow_succ hq n
  have hmul : Nat.Coprime p (q ^ n * (q - 1)) := by
    rw [Nat.coprime_mul_iff_right]
    exact ⟨hpq.pow_right n, hq1⟩
  have hcop : Nat.Coprime (Nat.card (Cyc (p ^ 2)))
      (Nat.card (MulAut (Cyc (q ^ (n + 1))))) := by
    rw [card_Cyc, card_mulAut_cyc, htot]
    exact (Nat.coprime_pow_left_iff (by norm_num) p (q ^ n * (q - 1))).mpr hmul
  exact hom_to_mulAut_coprime_eq_one hcop χ

/-- Constructs a multiplicative equivalence from `(A × B) ⋊[φ] C` to `A × (B ⋊[ψ] C)` when the
action satisfies `φ c (a, b) = (a, ψ c b)`. -/
def semidirectProdMulEquiv
    {A B C : Type*} [Group A] [Group B] [Group C]
    (φ : C →* MulAut (A × B)) (ψ : C →* MulAut B)
    (h : ∀ (c : C) (a : A) (b : B), φ c (a, b) = (a, ψ c b)) :
    (A × B) ⋊[φ] C ≃* A × (B ⋊[ψ] C) where
  toFun x := (x.left.1, ⟨x.left.2, x.right⟩)
  invFun y := ⟨(y.1, y.2.left), y.2.right⟩
  left_inv x := by ext <;> simp
  right_inv y := by ext <;> simp
  map_mul' x y := by
    apply Prod.ext
    · show (x.left * φ x.right y.left).1 = x.left.1 * y.left.1
      simp [h]
    · ext
      · show (x.left * φ x.right y.left).2 = x.left.2 * ψ x.right y.left.2
        simp [h]
      · rfl

/-- The action of `C` on `A × B` that fixes the `A` coordinate and acts on the `B` coordinate
through `ψ`. -/
def prodAct {A B C : Type*} [Group A] [Group B] [Group C]
    (ψ : C →* MulAut B) : C →* MulAut (A × B) where
  toFun c := MulEquiv.prodCongr (MulEquiv.refl A) (ψ c)
  map_one' := by
    apply MulEquiv.ext
    rintro ⟨a, b⟩
    simp [MulEquiv.prodCongr, Equiv.prodCongr_apply]
  map_mul' c d := by
    apply MulEquiv.ext
    rintro ⟨a, b⟩
    simp [MulEquiv.prodCongr, Equiv.prodCongr_apply]

/-- The product action evaluates as `prodAct ψ c (a, b) = (a, ψ c b)`. -/
@[simp]
theorem prodAct_apply {A B C : Type*} [Group A] [Group B] [Group C]
    (ψ : C →* MulAut B) (c : C) (a : A) (b : B) :
    prodAct (A := A) ψ c (a, b) = (a, ψ c b) := rfl

/-- For finite groups of coprime orders, any automorphism of `A × B` sends `(1, b)` to an
element with first coordinate one. -/
theorem mulAut_prod_fst_eq_one_of_coprime
    {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (hcop : Nat.Coprime (Nat.card A) (Nat.card B)) (θ : MulAut (A × B))
    (b : B) : (θ (1, b)).1 = 1 := by
  have hord : orderOf (θ (1, b)) = orderOf ((1, b) : A × B) :=
    orderOf_injective θ.toMonoidHom θ.injective (1, b)
  have hdvdB : orderOf (θ (1, b)) ∣ Nat.card B := by
    rw [hord, Prod.orderOf_mk]
    simpa using orderOf_dvd_natCard b
  have hA : orderOf ((θ (1, b)).1) ∣ Nat.card A := orderOf_dvd_natCard _
  have hB : orderOf ((θ (1, b)).1) ∣ Nat.card B :=
    (orderOf_map_dvd (MonoidHom.fst A B) (θ (1, b))).trans hdvdB
  have hg : orderOf ((θ (1, b)).1) ∣
      Nat.gcd (Nat.card A) (Nat.card B) := Nat.dvd_gcd hA hB
  rw [Nat.coprime_iff_gcd_eq_one.mp hcop] at hg
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hg)

/-- For finite groups of coprime orders, any automorphism of `A × B` sends `(a, 1)` to an
element with second coordinate one. -/
theorem mulAut_prod_snd_eq_one_of_coprime
    {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (hcop : Nat.Coprime (Nat.card A) (Nat.card B)) (θ : MulAut (A × B))
    (a : A) : (θ (a, 1)).2 = 1 := by
  have hord : orderOf (θ (a, 1)) = orderOf ((a, 1) : A × B) :=
    orderOf_injective θ.toMonoidHom θ.injective (a, 1)
  have hdvdA : orderOf (θ (a, 1)) ∣ Nat.card A := by
    rw [hord, Prod.orderOf_mk]
    simpa using orderOf_dvd_natCard a
  have hB : orderOf ((θ (a, 1)).2) ∣ Nat.card B := orderOf_dvd_natCard _
  have hA : orderOf ((θ (a, 1)).2) ∣ Nat.card A :=
    (orderOf_map_dvd (MonoidHom.snd A B) (θ (a, 1))).trans hdvdA
  have hg : orderOf ((θ (a, 1)).2) ∣
      Nat.gcd (Nat.card A) (Nat.card B) := Nat.dvd_gcd hA hB
  rw [Nat.coprime_iff_gcd_eq_one.mp hcop] at hg
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hg)

/-- Every automorphism of a product of finite groups of coprime orders acts coordinatewise
through an automorphism of each factor. -/
theorem mulAut_prod_coprime_decomposes
    {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (hcop : Nat.Coprime (Nat.card A) (Nat.card B)) (θ : MulAut (A × B)) :
    ∃ (γ : MulAut A) (η : MulAut B), ∀ a b, θ (a, b) = (γ a, η b) := by
  have : Fintype A := Fintype.ofFinite A
  have : Fintype B := Fintype.ofFinite B
  let gammaFun : A → A := fun a => (θ (a, 1)).1
  let etaFun : B → B := fun b => (θ (1, b)).2
  have hgamma_mul : ∀ a₁ a₂, gammaFun (a₁ * a₂) = gammaFun a₁ * gammaFun a₂ := by
    intro a₁ a₂
    have hm : ((a₁ * a₂, 1) : A × B) = (a₁, 1) * (a₂, 1) := by simp
    show (θ (a₁ * a₂, 1)).1 = (θ (a₁, 1)).1 * (θ (a₂, 1)).1
    rw [hm, map_mul, Prod.fst_mul]
  have heta_mul : ∀ b₁ b₂, etaFun (b₁ * b₂) = etaFun b₁ * etaFun b₂ := by
    intro b₁ b₂
    have hm : ((1, b₁ * b₂) : A × B) = (1, b₁) * (1, b₂) := by simp
    show (θ (1, b₁ * b₂)).2 = (θ (1, b₁)).2 * (θ (1, b₂)).2
    rw [hm, map_mul, Prod.snd_mul]
  let gammaHom : A →* A :=
    { toFun := gammaFun
      map_one' := by
        show (θ ((1, 1) : A × B)).1 = 1
        rw [show ((1, 1) : A × B) = 1 by simp, map_one]
        rfl
      map_mul' := hgamma_mul }
  let etaHom : B →* B :=
    { toFun := etaFun
      map_one' := by
        show (θ ((1, 1) : A × B)).2 = 1
        rw [show ((1, 1) : A × B) = 1 by simp, map_one]
        rfl
      map_mul' := heta_mul }
  have hgamma_inj : Function.Injective gammaHom := by
    intro a₁ a₂ hEq
    have h1 : θ (a₁, 1) = θ (a₂, 1) := by
      have hs₁ : (θ (a₁, 1)).2 = 1 := mulAut_prod_snd_eq_one_of_coprime hcop θ a₁
      have hs₂ : (θ (a₂, 1)).2 = 1 := mulAut_prod_snd_eq_one_of_coprime hcop θ a₂
      exact Prod.ext hEq (hs₁.trans hs₂.symm)
    exact congrArg Prod.fst (θ.injective h1)
  have heta_inj : Function.Injective etaHom := by
    intro b₁ b₂ hEq
    have h1 : θ (1, b₁) = θ (1, b₂) := by
      have hf₁ : (θ (1, b₁)).1 = 1 := mulAut_prod_fst_eq_one_of_coprime hcop θ b₁
      have hf₂ : (θ (1, b₂)).1 = 1 := mulAut_prod_fst_eq_one_of_coprime hcop θ b₂
      exact Prod.ext (hf₁.trans hf₂.symm) hEq
    exact congrArg Prod.snd (θ.injective h1)
  have hgamma_bij : Function.Bijective gammaHom :=
    ⟨hgamma_inj, Finite.surjective_of_injective hgamma_inj⟩
  have heta_bij : Function.Bijective etaHom :=
    ⟨heta_inj, Finite.surjective_of_injective heta_inj⟩
  refine ⟨MulEquiv.ofBijective gammaHom hgamma_bij,
    MulEquiv.ofBijective etaHom heta_bij, ?_⟩
  intro a b
  have hdec : ((a, b) : A × B) = (a, 1) * (1, b) := by simp
  rw [hdec, map_mul]
  have hg : θ (a, 1) = (gammaHom a, 1) :=
    Prod.ext rfl (mulAut_prod_snd_eq_one_of_coprime hcop θ a)
  have he : θ (1, b) = (1, etaHom b) :=
    Prod.ext (mulAut_prod_fst_eq_one_of_coprime hcop θ b) rfl
  rw [hg, he]
  simp

/-- Under the stated prime, positivity, and divisibility assumptions, the semidirect product
with explicit action `prodAct ψ` is multiplicatively equivalent to `Cyc (q ^ s) × (Cyc (p ^
r) ⋊[ψ] Cyc (p ^ 2))` [CosmePortugal2007]. -/
theorem source_isomorphism
    (p q r s : ℕ) (_hp : p.Prime) (_hq : q.Prime) (_hs : 0 < s)
    (_hne : p ≠ q) (_hnd : ¬ p ∣ (q - 1))
    (ψ : Cyc (p ^ 2) →* MulAut (Cyc (p ^ r))) :
    Nonempty ((Cyc (q ^ s) × Cyc (p ^ r)) ⋊[prodAct ψ] Cyc (p ^ 2) ≃*
      Cyc (q ^ s) × (Cyc (p ^ r) ⋊[ψ] Cyc (p ^ 2))) :=
  ⟨semidirectProdMulEquiv (prodAct ψ) ψ (fun c a b => by simp)⟩

end Qatlib.Papers.SemidirectHSP07.MainResults
