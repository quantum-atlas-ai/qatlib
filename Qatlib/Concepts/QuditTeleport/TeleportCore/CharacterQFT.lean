/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Star.BigOperators
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Qatlib.Concepts.QuditTeleport.TeleportCore.Transform

@[expose] public section

/-!
# Product-character Fourier transforms on multi-register `ZMod N` states

A state on `m` registers of `ZMod N` is an amplitude function on
`Fin m → ZMod N`. Its product character at frequency `k` is the coordinatewise
product `∏ i, ω ^ (x i * k i)` of the standard additive characters. This module
packages those characters as additive characters of the register group, proves
their orthogonality and completeness, and defines the character Fourier
transform with its gate matrix.

The transform uses the positive-character convention of
`Qatlib.Concepts.QuditTeleport.TeleportCore.zmodQFT` (`stdAddChar` rather than its
conjugate), so applying it twice reflects the register vector instead of
returning the input; see `characterQFT_characterQFT`.

## Main statements

* `sum_pi_prod`: a product over a function space factors into coordinatewise sums.
* `sum_prodStdAddChar`: product characters are orthogonal over the register group.
* `prodStdAddCharEquiv`: the frequency vectors label the whole dual group.
* `characterQFTGate_mem_unitaryGroup`: the character Fourier gate is unitary.
* `characterQFT_characterQFT`: two transforms compose to the reflection `x ↦ -x`.
-/

open scoped BigOperators
open Matrix
open Qatlib.Concepts.QuditTeleport.TeleportCore

set_option autoImplicit false

namespace Qatlib.Concepts.QuditTeleport.TeleportCore

variable {N : ℕ} [NeZero N]

/-! ## Product characters -/

/-- The additive character of the register group `Fin m → ZMod N` whose value at `x` is the
product `∏ i, ω ^ (x i * k i)` of the standard characters at the frequency vector `k`. -/
noncomputable def prodStdAddChar {m : ℕ} (k : Fin m → ZMod N) :
    AddChar (Fin m → ZMod N) ℂ where
  toFun x := ∏ i, ZMod.stdAddChar (x i * k i)
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by
    simp only [Pi.add_apply, add_mul, AddChar.map_add_eq_mul, Finset.prod_mul_distrib]

/-- Evaluating a product character is the coordinatewise product of standard characters. -/
theorem prodStdAddChar_apply {m : ℕ} (k x : Fin m → ZMod N) :
    prodStdAddChar k x = ∏ i, ZMod.stdAddChar (x i * k i) := rfl

/-- Product characters are symmetric in the frequency and evaluation vectors. -/
theorem prodStdAddChar_comm {m : ℕ} (k x : Fin m → ZMod N) :
    prodStdAddChar k x = prodStdAddChar x k := by
  simp only [prodStdAddChar_apply, mul_comm]

/-- The zero frequency is the trivial character. -/
@[simp] theorem prodStdAddChar_zero {m : ℕ} :
    prodStdAddChar (0 : Fin m → ZMod N) = 1 := by
  ext x
  simp [prodStdAddChar_apply]

/-- Frequencies add pointwise on product characters. -/
theorem prodStdAddChar_add {m : ℕ} (k l : Fin m → ZMod N) :
    prodStdAddChar (k + l) = prodStdAddChar k * prodStdAddChar l := by
  ext x
  simp only [prodStdAddChar_apply, Pi.add_apply, mul_add, AddChar.mul_apply]
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => (ZMod.stdAddChar).map_add_eq_mul _ _

/-- The character at a negated frequency is the pointwise inverse character. -/
theorem prodStdAddChar_neg_apply {m : ℕ} (k x : Fin m → ZMod N) :
    prodStdAddChar (-k) x = (prodStdAddChar k x)⁻¹ := by
  simp only [prodStdAddChar_apply, Pi.neg_apply, mul_neg]
  rw [← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun i _ => AddChar.map_neg_eq_inv _ _

/-- A frequency and its negation multiply to the trivial character. -/
theorem prodStdAddChar_neg_mul {m : ℕ} (k : Fin m → ZMod N) :
    prodStdAddChar (-k) * prodStdAddChar k = 1 := by
  ext x
  rw [AddChar.mul_apply, AddChar.one_apply]
  simp only [prodStdAddChar_apply, Pi.neg_apply, mul_neg]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [← AddChar.map_add_eq_mul, show -(x i * k i) + x i * k i = 0 by abel,
    AddChar.map_zero_eq_one]

/-- Star conjugation negates the frequency of a product character. -/
theorem star_prodStdAddChar {m : ℕ} (k x : Fin m → ZMod N) :
    star (prodStdAddChar k x) = prodStdAddChar (-k) x := by
  rw [prodStdAddChar_apply, prodStdAddChar_apply, star_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [RCLike.star_def, ← AddChar.map_neg_eq_conj]
  simp only [Pi.neg_apply]
  congr 1
  ring

/-! ## Orthogonality and completeness -/

/-- A product over a function space factors into the product of the coordinatewise sums. -/
theorem sum_pi_prod {m : ℕ} {β : Type*} [CommSemiring β]
    (g : Fin m → ZMod N → β) :
    (∑ x : Fin m → ZMod N, ∏ i, g i (x i)) = ∏ i, ∑ y : ZMod N, g i y := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => ZMod N)).sum_comp, Fintype.sum_prod_type]
    simp only [Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ, Fin.prod_univ_succ]
    calc
      ∑ a : ZMod N, ∑ t : Fin n → ZMod N, g 0 a * ∏ i : Fin n, g i.succ (t i)
          = ∑ a : ZMod N, g 0 a * ∏ i : Fin n, ∑ y : ZMod N, g i.succ y := by
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [← ih (fun i => g i.succ), Finset.mul_sum]
      _ = (∑ a : ZMod N, g 0 a) * ∏ i : Fin n, ∑ y : ZMod N, g i.succ y :=
            (Finset.sum_mul ..).symm

/-- A constant sum over the register group is the group cardinality. -/
theorem sum_one_registerGroup (m : ℕ) :
    (∑ _x : Fin m → ZMod N, (1 : ℂ)) = (N : ℂ) ^ m := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, ZMod.card]
  simp

/-- Product characters are orthogonal: their sum over the register group is the group
cardinality at zero frequency and vanishes at every other frequency. -/
theorem sum_prodStdAddChar {m : ℕ} (k : Fin m → ZMod N) :
    (∑ x : Fin m → ZMod N, prodStdAddChar k x) =
      if k = 0 then (N : ℂ) ^ m else 0 := by
  simp only [prodStdAddChar_apply]
  rw [sum_pi_prod (g := fun i y => ZMod.stdAddChar (y * k i))]
  have hterm : ∀ i : Fin m, (∑ y : ZMod N, ZMod.stdAddChar (y * k i)) =
      if k i = 0 then (N : ℂ) else 0 := by
    intro i
    rw [show (fun y : ZMod N => ZMod.stdAddChar (y * k i)) =
        fun y => ZMod.stdAddChar (k i * y) from by
      funext y
      rw [mul_comm]]
    exact sum_stdAddChar_mul (k i)
  simp_rw [hterm]
  by_cases hk : k = 0
  · subst hk
    simp
  · obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
      by_contra h
      exact hk (funext fun i => not_not.mp (not_exists.mp h i))
    rw [ite_eq_right hk]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- Orthogonality of a product character against a second product character, read in the
evaluation variable of the first one. -/
theorem sum_prodStdAddChar_mul {m : ℕ} (k y : Fin m → ZMod N) :
    (∑ x : Fin m → ZMod N, prodStdAddChar k x * prodStdAddChar x y) =
      if k + y = 0 then (N : ℂ) ^ m else 0 := by
  have hterm : ∀ x : Fin m → ZMod N,
      prodStdAddChar k x * prodStdAddChar x y = prodStdAddChar (k + y) x := by
    intro x
    rw [prodStdAddChar_comm x y, ← AddChar.mul_apply, ← prodStdAddChar_add]
  simp_rw [hterm]
  exact sum_prodStdAddChar (k + y)

/-- The frequency vector is determined by its product character. -/
theorem prodStdAddChar_injective {m : ℕ} :
    Function.Injective (prodStdAddChar (N := N) (m := m)) := by
  intro k l hkl
  have hchar : prodStdAddChar (k - l) = 1 := by
    rw [sub_eq_add_neg, prodStdAddChar_add, hkl]
    exact (mul_comm _ _).trans (prodStdAddChar_neg_mul l)
  have hsum : (∑ x : Fin m → ZMod N, prodStdAddChar (k - l) x) = (N : ℂ) ^ m := by
    have hval : ∀ x : Fin m → ZMod N, prodStdAddChar (k - l) x = 1 := by
      intro x
      rw [hchar, AddChar.one_apply]
    simp_rw [hval]
    exact sum_one_registerGroup m
  by_contra hne
  rw [sum_prodStdAddChar, ite_eq_right (fun h => hne (sub_eq_zero.mp h))] at hsum
  exact pow_ne_zero m (by exact_mod_cast NeZero.ne N) hsum.symm

/-- The product-character labelling of the dual of the register group: every additive character
of `Fin m → ZMod N` is the product character of a unique frequency vector. -/
noncomputable def prodStdAddCharEquiv (m : ℕ) :
    (Fin m → ZMod N) ≃ AddChar (Fin m → ZMod N) ℂ :=
  Equiv.ofBijective prodStdAddChar (by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨prodStdAddChar_injective, by simp [Fintype.card_fin, ZMod.card, AddChar.card_eq]⟩)

/-- The character equivalence evaluates to the product character of the frequency. -/
@[simp] theorem prodStdAddCharEquiv_apply {m : ℕ} (k : Fin m → ZMod N) :
    prodStdAddCharEquiv m k = prodStdAddChar k := rfl

/-! ## The character Fourier transform -/

/-- The `m`-fold character normalisation `N ^ (-m / 2)`. -/
noncomputable def characterScale (N : ℕ) (m : ℕ) : ℂ :=
  (((Real.sqrt (N : ℝ) : ℝ) : ℂ))⁻¹ ^ m

omit [NeZero N] in
/-- The character scale is fixed by star conjugation. -/
@[simp] theorem star_characterScale (m : ℕ) :
    star (characterScale N m) = characterScale N m := by
  simp [characterScale]

/-- The square of the character scale times the group cardinality is one. -/
theorem characterScale_mul_self_mul_card (m : ℕ) :
    characterScale N m * characterScale N m * (N : ℂ) ^ m = 1 := by
  have hsqrt : ((((Real.sqrt (N : ℝ) : ℝ)) : ℂ)) * (((Real.sqrt (N : ℝ) : ℝ) : ℂ)) =
      (N : ℂ) := by
    have h2 : (((Real.sqrt (N : ℝ) : ℝ) : ℂ)) ^ 2 = (N : ℂ) := by
      exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg N)
    rw [← h2, pow_two]
  have hbase : ((((Real.sqrt (N : ℝ) : ℝ) : ℂ))⁻¹ * (((Real.sqrt (N : ℝ) : ℝ) : ℂ))⁻¹) *
      (N : ℂ) = 1 := by
    rw [← hsqrt]
    have hne : (((Real.sqrt (N : ℝ) : ℝ) : ℂ)) ≠ 0 := by
      have hpos : (0 : ℝ) < Real.sqrt (N : ℝ) :=
        Real.sqrt_pos.mpr (by exact_mod_cast NeZero.pos N)
      exact_mod_cast hpos.ne'
    field_simp
  calc
    characterScale N m * characterScale N m * (N : ℂ) ^ m
        = (((((Real.sqrt (N : ℝ) : ℝ) : ℂ))⁻¹ *
            (((Real.sqrt (N : ℝ) : ℝ) : ℂ))⁻¹) * (N : ℂ)) ^ m := by
          rw [characterScale, ← mul_pow, ← mul_pow]
    _ = 1 := by rw [hbase, one_pow]

/-- The Fourier coefficient of a register state at the frequency vector `k`. -/
noncomputable def characterWeight {m : ℕ} (k : Fin m → ZMod N)
    (φ : (Fin m → ZMod N) → ℂ) : ℂ :=
  ∑ x, prodStdAddChar k x * φ x

/-- The `m`-fold character quantum Fourier transform on `ZMod N` registers. -/
noncomputable def characterQFT {m : ℕ} (φ : (Fin m → ZMod N) → ℂ) :
    (Fin m → ZMod N) → ℂ :=
  fun k => characterScale N m * characterWeight k φ

/-- Evaluating the character transform gives the scaled character sum at the frequency. -/
theorem characterQFT_apply {m : ℕ} (φ : (Fin m → ZMod N) → ℂ) (k : Fin m → ZMod N) :
    characterQFT φ k = characterScale N m * ∑ x, prodStdAddChar k x * φ x := rfl

/-- The matrix of the `m`-fold character Fourier transform, with rows indexed by frequencies
and columns by register vectors. -/
noncomputable def characterQFTGate (m : ℕ) :
    Matrix (Fin m → ZMod N) (Fin m → ZMod N) ℂ :=
  fun k x => characterScale N m * prodStdAddChar k x

/-- The character transform is matrix-vector multiplication by the character Fourier gate. -/
theorem characterQFT_eq_mulVec {m : ℕ} (φ : (Fin m → ZMod N) → ℂ) :
    characterQFT φ = characterQFTGate (N := N) m *ᵥ φ := by
  funext k
  rw [characterQFT_apply, Matrix.mulVec_apply_eq_sum, Finset.mul_sum]
  simp only [characterQFTGate]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- The character Fourier gate is unitary. -/
theorem characterQFTGate_mem_unitaryGroup (m : ℕ) :
    characterQFTGate (N := N) m ∈ Matrix.unitaryGroup (Fin m → ZMod N) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  ext k l
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hterm : ∀ x : Fin m → ZMod N,
      (characterQFTGate (N := N) m) k x * (characterQFTGate (N := N) m)ᴴ x l =
        characterScale N m * characterScale N m * prodStdAddChar (k - l) x := by
    intro x
    rw [Matrix.conjTranspose_apply]
    simp only [characterQFTGate]
    rw [star_mul, star_characterScale, star_prodStdAddChar]
    rw [show k - l = k + -l by abel, prodStdAddChar_add, AddChar.mul_apply]
    ring
  simp_rw [hterm]
  rw [← Finset.mul_sum, sum_prodStdAddChar]
  by_cases hkl : k = l
  · subst hkl
    rw [sub_self, ite_eq_left rfl, ite_eq_left rfl, characterScale_mul_self_mul_card]
  · have hne : k - l ≠ 0 := fun h => hkl (sub_eq_zero.mp h)
    rw [ite_eq_right hne, ite_eq_right hkl, mul_zero]

/-- Applying the character transform twice reflects the register vector, because the transform
uses the positive-character convention. -/
theorem characterQFT_characterQFT {m : ℕ} (φ : (Fin m → ZMod N) → ℂ) :
    characterQFT (characterQFT φ) = fun x => φ (-x) := by
  funext k
  rw [characterQFT_apply]
  have h1 : (∑ x : Fin m → ZMod N, prodStdAddChar k x * characterQFT φ x) =
      characterScale N m * (∑ x, ∑ y, (prodStdAddChar k x * prodStdAddChar x y) * φ y) := by
    have hx : ∀ x : Fin m → ZMod N, prodStdAddChar k x * characterQFT φ x =
        characterScale N m *
          ∑ y, (prodStdAddChar k x * prodStdAddChar x y) * φ y := by
      intro x
      rw [characterQFT_apply]
      calc
        prodStdAddChar k x * (characterScale N m * ∑ y, prodStdAddChar x y * φ y)
            = characterScale N m *
                (prodStdAddChar k x * ∑ y, prodStdAddChar x y * φ y) := by ring
        _ = characterScale N m *
              ∑ y, prodStdAddChar k x * (prodStdAddChar x y * φ y) := by
              congr 1
              rw [Finset.mul_sum]
        _ = characterScale N m *
              ∑ y, (prodStdAddChar k x * prodStdAddChar x y) * φ y := by
              congr 1
              exact Finset.sum_congr rfl fun y _ => by ring
    simp_rw [hx]
    rw [Finset.mul_sum]
  rw [h1]
  have h2 : (∑ x : Fin m → ZMod N, ∑ y : Fin m → ZMod N,
      (prodStdAddChar k x * prodStdAddChar x y) * φ y) = (N : ℂ) ^ m * φ (-k) := by
    rw [Finset.sum_comm]
    have hy : ∀ y : Fin m → ZMod N,
        (∑ x : Fin m → ZMod N, (prodStdAddChar k x * prodStdAddChar x y) * φ y) =
          (if k + y = 0 then (N : ℂ) ^ m else 0) * φ y := by
      intro y
      rw [← Finset.sum_mul, sum_prodStdAddChar_mul]
    simp_rw [hy]
    rw [Finset.sum_eq_single (-k)]
    · rw [ite_eq_left (by abel : k + -k = 0)]
    · intro y _ hy'
      rw [ite_eq_right (by
        intro h
        apply hy'
        calc y = y + k - k := by abel
          _ = k + y - k := by rw [add_comm]
          _ = 0 - k := by rw [h]
          _ = -k := by abel), zero_mul]
    · intro h
      simp at h
  rw [h2]
  calc
    characterScale N m * (characterScale N m * ((N : ℂ) ^ m * φ (-k)))
        = (characterScale N m * characterScale N m * (N : ℂ) ^ m) * φ (-k) := by ring
    _ = φ (-k) := by rw [characterScale_mul_self_mul_card, one_mul]

end Qatlib.Concepts.QuditTeleport.TeleportCore
