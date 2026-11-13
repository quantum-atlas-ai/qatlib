/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CycloSieve26.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Cyclotomic Character Duality, Bilinear Pairing, and Galois Stability

This module formalizes Lemma 4, Proposition 1, and Proposition 2 of Boucher, Fouque,
and Shen on the coordinate trace pairing `coordPair`, Pontryagin character duality
`R_L ≃+ AddChar (R_L) ℂ`, character orthogonality, Galois stability, and level descent.

## Main definitions

* `zmodC`, `chiCircleFun`, `chiCircle`, `chiCoord`, `chiHom`: additive characters on `R_L = (ℤ/pℤ)^L`.
* `coordMul`: coordinatewise multiplication on `R_L`.

## Main statements

* `proposition1_duality`: Proposition 1, isomorphism `R_L ≃+ AddChar (R_L) ℂ`.
* `lemma4_bilinear_form`: Lemma 4, symmetry, bilinearity, and non-degeneracy of `coordPair`.
* `prop2_homomorphism`, `prop2_symmetry`, `prop2_orthogonality`: Proposition 2(1)--(3).
* `prop2_galois_stability`: Proposition 2(4), Galois trace stability of cyclotomic characters.
* `prop2_level_descent`: Proposition 2(5), descent of characters trivial on the level kernel.

## References

* [Boucher, Fouque, and Shen, 2026][BoucherFouqueShen2026], Lemma 4, Propositions 1--2, pp. 11--13.
-/

set_option autoImplicit false

namespace Qatlib.Papers.CycloSieve26.MainResults

open Finset
open scoped BigOperators

/- ## The coordinate characters -/

/-- The circle-valued character on `ZMod p` sending `1` to `e^{2πi a/p}`;
`AddChar.zmod p a` composed with the coercion `Circle → ℂ`. -/
noncomputable def zmodC (p : ℕ) [NeZero p] (a : ZMod p) : AddChar (ZMod p) ℂ :=
  Circle.coeHom.compAddChar (AddChar.zmod p a)

/-- `zmodC a` takes the value `1` at `1` exactly when `a = 0`; this is the
injectivity of the exponential on `p`-th roots of unity. -/
theorem zmodC_one_eq_one {p : ℕ} [Fact p.Prime] (a : ZMod p) :
    zmodC p a 1 = 1 ↔ a = 0 := by
  constructor
  · intro h
    have hc : AddChar.zmod p a 1 = (1 : Circle) := by
      apply Subtype.coe_injective
      simpa [zmodC] using h
    have hchar : AddChar.zmod p a = 1 := by
      by_contra hne
      exact (AddChar.zmod_char_ne_one_iff p (AddChar.zmod p a)).mp hne hc
    exact AddChar.zmod_injective (hchar.trans (AddChar.zmod_zero p).symm)
  · intro h
    subst h
    simp [zmodC]

/-- The underlying function of the circle-valued character
`x ↦ ∏ i, e^{2πi xᵢyᵢ/p}`. -/
noncomputable def chiCircleFun (p L : ℕ) [Fact p.Prime] (y : RL p L) (x : RL p L) :
    Circle :=
  ∏ i, AddChar.zmod p (x i * y i) 1

/-- The **circle-valued coordinate character** `χ_y` of the product group
`R_L = (ℤ/p)^L`: `χ_y(x) = ∏ i, e^{2πi xᵢyᵢ/p}`.  This is the unitary part of
`χ_y(x) = exp(2πi Tr(xy/(pπ^{L-1})))` of Proposition 1. -/
noncomputable def chiCircle (p L : ℕ) [Fact p.Prime] (y : RL p L) :
    AddChar (RL p L) Circle where
  toFun := chiCircleFun p L y
  map_zero_eq_one' := by
    simp only [chiCircleFun, Pi.zero_apply, zero_mul, AddChar.zmod_zero,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    simp
  map_add_eq_mul' x x' := by
    simp only [chiCircleFun, Pi.add_apply, add_mul, AddChar.zmod_add, AddChar.mul_apply,
      Finset.prod_mul_distrib]

/-- `chiCircle` applied is `chiCircleFun`, by definition. -/
theorem chiCircle_apply {p L : ℕ} [Fact p.Prime] (y x : RL p L) :
    chiCircle p L y x = chiCircleFun p L y x := rfl

/-- The **coordinate character** `χ_y`, as a complex-valued additive character:
the coercion `Circle → ℂ` of `chiCircle`. -/
noncomputable def chiCoord (p L : ℕ) [Fact p.Prime] (y : RL p L) :
    AddChar (RL p L) ℂ :=
  Circle.coeHom.compAddChar (chiCircle p L y)

/-- `chiCoord` is the coercion of `chiCircle`, by definition. -/
theorem chiCoord_apply {p L : ℕ} [Fact p.Prime] (y : RL p L) (x : RL p L) :
    chiCoord p L y x = (chiCircle p L y x : ℂ) := rfl

/-- `chiCircle` evaluated on a single coordinate basis vector recovers the
`i`-th coordinate of `y`. -/
theorem chiCircle_single {p : ℕ} [Fact p.Prime] {L : ℕ} (i : Fin L) (y : RL p L) :
    chiCircle p L y (Pi.single i 1) = AddChar.zmod p (y i) 1 := by
  rw [chiCircle_apply]
  simp only [chiCircleFun, Pi.single_apply]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- `chiCoord y` evaluated on a single coordinate basis vector recovers the
`i`-th coordinate of `y`. -/
theorem chiCoord_single {p : ℕ} [Fact p.Prime] {L : ℕ} (i : Fin L) (y : RL p L) :
    chiCoord p L y (Pi.single i 1) = zmodC p (y i) 1 := by
  rw [chiCoord_apply, chiCircle_single]
  rfl

/-- `chiCircle 0` is the trivial character. -/
@[simp] theorem chiCircle_zero {p : ℕ} [Fact p.Prime] (L : ℕ) :
    chiCircle p L (0 : RL p L) = 0 := by
  ext x
  rw [chiCircle_apply]
  simp [chiCircleFun]

/-- `chiCoord 0` is the trivial character. -/
@[simp] theorem chiCoord_zero {p : ℕ} [Fact p.Prime] (L : ℕ) :
    chiCoord p L (0 : RL p L) = 0 := by
  ext x
  simp [chiCoord_apply]

/-- The coercion `Circle → ℂ` commutes with finite products. -/
theorem circle_coe_prod {L : ℕ} (f : Fin L → Circle) :
    ↑(∏ i, f i) = ∏ i, (f i : ℂ) := by
  simpa only [Circle.coeHom_apply] using map_prod Circle.coeHom f Finset.univ

/-- The characters are additive in the label at the circle level:
`χ_{y+y'} = χ_y · χ_{y'}`. -/
theorem chiCircle_add {p L : ℕ} [Fact p.Prime] (y y' : RL p L) :
    chiCircle p L (y + y') = chiCircle p L y + chiCircle p L y' := by
  ext x
  rw [chiCircle_apply, AddChar.add_apply, chiCircle_apply, chiCircle_apply]
  simp only [chiCircleFun, Pi.add_apply, mul_add, AddChar.zmod_add, AddChar.mul_apply,
    Finset.prod_mul_distrib, Circle.coe_mul, circle_coe_prod]

/-- The characters are additive in the label: `χ_{y+y'} = χ_y · χ_{y'}`. -/
theorem chiCoord_add {p L : ℕ} [Fact p.Prime] (y y' : RL p L) :
    chiCoord p L (y + y') = chiCoord p L y + chiCoord p L y' := by
  ext x
  rw [chiCoord_apply, chiCircle_add, AddChar.add_apply, AddChar.add_apply,
    chiCoord_apply, chiCoord_apply]
  simp

/-- The label-to-character map `y ↦ χ_y`, as an additive homomorphism.  This is
the map `Φ_L` of Proposition 1. -/
noncomputable def chiHom (p L : ℕ) [Fact p.Prime] :
    RL p L →+ AddChar (RL p L) ℂ where
  toFun := chiCoord p L
  map_zero' := chiCoord_zero L
  map_add' := chiCoord_add

/-- A label `y` whose character is trivial is zero: evaluating on the coordinate
basis vectors and using `zmodC_one_eq_one`. -/
theorem chiHom_eq_zero {p L : ℕ} [Fact p.Prime] (y : RL p L)
    (h : chiHom p L y = 0) : y = 0 := by
  funext i
  have hs := DFunLike.congr_fun h (Pi.single i 1)
  have h1 : chiCoord p L y (Pi.single i 1) = 1 := by
    simpa [chiHom, AddChar.zero_apply] using hs
  rw [chiCoord_single] at h1
  exact (zmodC_one_eq_one (y i)).mp h1

/-- The character map is injective. -/
theorem chiHom_injective {p L : ℕ} [Fact p.Prime] :
    Function.Injective (chiHom p L) := by
  intro y y' h
  have h' : chiHom p L (y - y') = 0 := by
    rw [map_sub, h, sub_self]
  have hy : y - y' = 0 := chiHom_eq_zero (y - y') h'
  exact sub_eq_zero.mp hy

/-- **Proposition 1 (Duality)** (paper p. 12, Proposition 1):
the character map `Φ_L : R_L → Hom(R_L, ℂ^×)`, `y ↦ χ_y`, is an additive group
isomorphism.  The proof is the paper's: injectivity from the non-degeneracy of
`B_L` (here, from the coordinate characters separating points), and bijectivity
from the equal cardinalities of a finite abelian group and its dual
(`AddChar.card_eq`). -/
theorem proposition1_duality (p L : ℕ) [Fact p.Prime] :
    ∃ Φ : RL p L ≃+ AddChar (RL p L) ℂ, ∀ y, Φ y = chiCoord p L y := by
  refine ⟨AddEquiv.ofBijective (chiHom p L) ?_, fun y => rfl⟩
  rw [Fintype.bijective_iff_injective_and_card, AddChar.card_eq]
  exact ⟨chiHom_injective, rfl⟩

/- ## Lemma 4: the bilinear form -/

/-- The coordinate pairing is **symmetric**. -/
theorem coordPair_symm (p L : ℕ) (x y : RL p L) :
    coordPair p L x y = coordPair p L y x := by
  simp only [coordPair, mul_comm]

/-- The coordinate pairing is **additive in the first argument**. -/
theorem coordPair_add_left (p L : ℕ) (x x' y : RL p L) :
    coordPair p L (x + x') y = coordPair p L x y + coordPair p L x' y := by
  simp only [coordPair, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- The coordinate pairing is **additive in the second argument**. -/
theorem coordPair_add_right (p L : ℕ) (x y y' : RL p L) :
    coordPair p L x (y + y') = coordPair p L x y + coordPair p L x y' := by
  simp only [coordPair, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- The pairing is **left non-degenerate**: a vector pairing to zero against
every vector is zero. -/
theorem coordPair_nondegenerate_left (p L : ℕ) (x : RL p L) :
    (∀ y, coordPair p L x y = 0) ↔ x = 0 := by
  constructor
  · intro h
    funext i
    have hs : coordPair p L x (Pi.single i (1 : ZMod p)) = x i := by
      simp only [coordPair, Pi.single_apply]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj; simp [hj]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    rw [← hs]; exact h _
  · intro hx y
    subst hx
    simp [coordPair]

/-- The pairing is **right non-degenerate**. -/
theorem coordPair_nondegenerate_right (p L : ℕ) (y : RL p L) :
    (∀ x, coordPair p L x y = 0) ↔ y = 0 := by
  constructor
  · intro h
    funext i
    have hs : coordPair p L (Pi.single i (1 : ZMod p)) y = y i := by
      simp only [coordPair, Pi.single_apply]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj; simp [hj]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    rw [← hs]; exact h _
  · intro hy x
    subst hy
    simp [coordPair]

/-- **Lemma 4** (paper p. 11): the trace form `B_L` is a non-degenerate
symmetric `ℤ`-bilinear form.  In the trace-dual coordinate model of
`SourceModel` this is the coordinate pairing `coordPair`: symmetric, additive
in both slots, and non-degenerate on each side. -/
theorem lemma4_bilinear_form (p L : ℕ) :
    (∀ x y : RL p L, coordPair p L x y = coordPair p L y x) ∧
    (∀ x x' y : RL p L,
      coordPair p L (x + x') y = coordPair p L x y + coordPair p L x' y) ∧
    (∀ x y y' : RL p L,
      coordPair p L x (y + y') = coordPair p L x y + coordPair p L x y') ∧
    (∀ x : RL p L, (∀ y, coordPair p L x y = 0) ↔ x = 0) ∧
    (∀ y : RL p L, (∀ x, coordPair p L x y = 0) ↔ y = 0) :=
  ⟨coordPair_symm p L, coordPair_add_left p L, coordPair_add_right p L,
    coordPair_nondegenerate_left p L, coordPair_nondegenerate_right p L⟩

/- ## Proposition 2: properties of the characters -/

/-- **Proposition 2(1), group homomorphism** (paper p. 12):
`χ_y(a+b) = χ_y(a) χ_y(b)`. -/
theorem prop2_homomorphism {p L : ℕ} [Fact p.Prime] (y a b : RL p L) :
    chiCoord p L y (a + b) = chiCoord p L y a * chiCoord p L y b :=
  AddChar.map_add_eq_mul _ _ _

/-- The product of coordinates used for the symmetry property. -/
def coordMul (p L : ℕ) (x y : RL p L) : RL p L := fun i => x i * y i

/-- **Proposition 2(2), symmetry** (paper p. 12):
`χ_y(λx) = χ_1(λxy) = χ_x(λy)`, for the coordinate scalar action
`coordSmul` modelling multiplication by `λ ∈ R_L`. -/
theorem prop2_symmetry {p L : ℕ} [Fact p.Prime] (lam x y : RL p L) :
    chiCircle p L y (coordSmul p L lam x) =
      chiCircle p L 1 (coordSmul p L lam (coordMul p L x y)) ∧
    chiCircle p L 1 (coordSmul p L lam (coordMul p L x y)) =
      chiCircle p L x (coordSmul p L lam y) := by
  constructor
  · rw [chiCircle_apply, chiCircle_apply]
    simp only [chiCircleFun, coordSmul, coordMul, Pi.one_apply]
    apply Finset.prod_congr rfl
    intro i _
    congr 2
    ring
  · rw [chiCircle_apply, chiCircle_apply]
    simp only [chiCircleFun, coordSmul, coordMul, Pi.one_apply]
    apply Finset.prod_congr rfl
    intro i _
    congr 2
    ring

/-- **Proposition 2(3), orthogonality of characters** (paper p. 12):
`(1/p^L) ∑_{y ∈ R_L} χ_y(x) = δ_{0,x}`. -/
theorem prop2_orthogonality {p L : ℕ} [Fact p.Prime] (x : RL p L) :
    ((p ^ L : ℕ) : ℂ)⁻¹ * (∑ y : RL p L, chiCoord p L y x) =
      if x = 0 then 1 else 0 := by
  obtain ⟨Φ, hΦ⟩ := proposition1_duality p L
  have hΦsum : (∑ y : RL p L, (Φ y) x) = ∑ ψ : AddChar (RL p L) ℂ, ψ x :=
    Fintype.sum_equiv Φ.toEquiv (fun y => (Φ y) x) (fun ψ => ψ x) (fun _ => rfl)
  have hsum : (∑ y : RL p L, chiCoord p L y x) =
      ∑ ψ : AddChar (RL p L) ℂ, ψ x := by
    rw [← hΦsum]
    apply Finset.sum_congr rfl
    intro y _
    rw [hΦ y]
  rw [hsum, AddChar.sum_apply_eq_ite]
  have hcard : Fintype.card (RL p L) = p ^ L := by
    simp [RL]
  have hp : ((p : ℂ)) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hpow : ((p ^ L : ℕ) : ℂ) ≠ 0 := by
    rw [Nat.cast_pow]; exact pow_ne_zero _ hp
  by_cases hx : x = 0
  · simp only [hx, ↓reduceIte, hcard]
    exact inv_mul_cancel₀ hpow
  · simp [hx]

/-- **Proposition 2(4), stability under the Galois group** (paper p. 12–13).
For `σ_u ∈ Gal(K/ℚ)` with `σ_u(ζ_p) = ζ_p^u` and `Tr ∘ σ_u = Tr`:
`χ_y(x) = χ_{σ_u(y)}(π^{L-1} σ_u(x/π^{L-1}))`.

Cancel the nonzero power of `π` and use trace invariance.  This exact identity
holds in any field, including when the natural-number cast of `p` is zero. -/
theorem prop2_galois_stability (p L : ℕ) [Fact p.Prime]
    (K : Type) [Field K] (tr : K → ℚ) (σ : K ≃+* K) (π ζ : K)
    (hζ : ζ = 1 + π) (hσ : ∀ x : K, tr (σ x) = tr x) (hπ : π ≠ 0) :
    ∀ x y : K,
      Complex.exp (2 * Real.pi * Complex.I *
          ((tr (x * y / ((p : K) * π ^ (L - 1))) : ℚ) : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I *
          ((tr (((π ^ (L - 1) * σ (x / π ^ (L - 1))) * σ y) /
            ((p : K) * π ^ (L - 1))) : ℚ) : ℂ)) := by
  intro x y
  let a := π ^ (L - 1)
  have ha : a ≠ 0 := pow_ne_zero (L - 1) hπ
  have hπζ : π = ζ - 1 := eq_sub_iff_add_eq'.mpr hζ.symm
  have htrace :
      tr (((a * σ (x / a)) * σ y) / ((p : K) * a)) =
        tr (x * y / ((p : K) * a)) := by
    calc
      tr (((a * σ (x / a)) * σ y) / ((p : K) * a)) =
          tr ((a * (σ (x / a) * σ y)) / (a * (p : K))) := by
            rw [mul_assoc, mul_comm (p : K) a]
      _ = tr ((σ (x / a) * σ y) / (p : K)) := by
        rw [mul_div_mul_left _ _ ha]
      _ = tr ((σ (x / a) * σ y) / σ (p : K)) := by
        rw [map_natCast]
      _ = tr (σ ((x / a * y) / (p : K))) := by
        rw [← map_mul, ← map_div₀]
      _ = tr ((x / a * y) / (p : K)) := hσ _
      _ = tr (x * y / ((p : K) * a)) := by
        rw [div_mul_eq_mul_div, div_div, mul_comm a (p : K)]
  calc
    Complex.exp (2 * Real.pi * Complex.I *
        ((tr (x * y / ((p : K) * π ^ (L - 1))) : ℚ) : ℂ)) =
        Complex.exp ((((p / p : ℕ) : ℂ) * (2 * Real.pi * Complex.I)) *
          ((tr (x * y / ((p : K) * (ζ - 1) ^ (L - 1))) : ℚ) : ℂ)) := by
            rw [Nat.div_self (Fact.out : p.Prime).pos, Nat.cast_one, one_mul, ← hπζ]
    _ = Complex.exp (2 * Real.pi * Complex.I *
        ((tr (x * y / ((p : K) * a)) : ℚ) : ℂ)) := by
          rw [Nat.div_self (Fact.out : p.Prime).pos, Nat.cast_one, one_mul, ← hπζ]
    _ = Complex.exp (2 * Real.pi * Complex.I *
        ((tr (((a * σ (x / a)) * σ y) / ((p : K) * a)) : ℚ) : ℂ)) := by
          rw [htrace]

/-- **Proposition 2(5), characters of `R_{L-1}`** (paper p. 13).
A character of `R_{L+1}` that is trivial on the kernel of the level reduction
`R_{L+1} → R_L` (this is the paper's character `χ_{πy}`, whose kernel
condition is `B_L(πy, π^{L}x) ∈ ℤ`) descends to a character of the lower level. -/
theorem prop2_level_descent {p L : ℕ} [Fact p.Prime] (y : RL p (L + 1))
    (hker : ∀ x : RL p (L + 1), levelReduce p L x = 0 →
      chiCoord p (L + 1) y x = 1) :
    ∃ χ' : AddChar (RL p L) ℂ,
      ∀ x : RL p (L + 1), χ' (levelReduce p L x) = chiCoord p (L + 1) y x := by
  classical
  -- The character of the lower level defined through the zero-padding section.
  refine ⟨{ toFun := fun v => chiCoord p (L + 1) y (levelSection p L v)
            map_zero_eq_one' := ?_
            map_add_eq_mul' := ?_ }, ?_⟩
  · have h0 : levelSection p L 0 = 0 := by
      funext i
      by_cases h : (i : ℕ) < L <;> simp [levelSection, h]
    rw [h0]
    exact AddChar.map_zero_eq_one (chiCoord p (L + 1) y)
  · intro v w
    have hadd : levelSection p L (v + w) = levelSection p L v + levelSection p L w := by
      funext i
      by_cases h : (i : ℕ) < L <;> simp [levelSection, h]
    rw [hadd]
    exact AddChar.map_add_eq_mul (chiCoord p (L + 1) y) _ _
  · intro x
    -- `x` and its section differ by an element of the kernel of the reduction
    have hker' : levelReduce p L (x - levelSection p L (levelReduce p L x)) = 0 := by
      funext i
      simp [levelReduce, levelSection]
    have hx : chiCoord p (L + 1) y x =
        chiCoord p (L + 1) y (levelSection p L (levelReduce p L x)) := by
      set a := levelSection p L (levelReduce p L x) with ha
      set b := x - levelSection p L (levelReduce p L x) with hb
      have hsplit : x = a + b := by rw [ha, hb]; abel
      have hbker : levelReduce p L b = 0 := by rw [hb]; exact hker'
      calc chiCoord p (L + 1) y x
          = chiCoord p (L + 1) y (a + b) := by rw [hsplit]
        _ = chiCoord p (L + 1) y a * chiCoord p (L + 1) y b :=
            AddChar.map_add_eq_mul _ _ _
        _ = chiCoord p (L + 1) y a * 1 := by rw [hker _ hbker]
        _ = chiCoord p (L + 1) y a := mul_one _
    exact hx.symm

end Qatlib.Papers.CycloSieve26.MainResults
