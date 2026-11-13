/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.SearchAlgorithm.NativeSourceDefs
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Independent binary hashes from finite-field polynomials

This module constructs binary hash families by evaluating polynomials over a finite field and
applying a surjective additive binary coordinate. Interpolation and uniform additive fibers
prove exact independence on distinct inputs, yielding a family with `d * Nat.clog 2 (N + 1)`
seed bits.

The mathematical background is developed in [Ambainis2007ElementDistinctness].

## Main statements

* `sampledPolynomialEvaluation_surjective`: interpolates arbitrary values at at most `d`
  distinct nodes.
* `polynomialBinaryHash_independent`: proves the exact joint output probabilities.
* `logarithmicSeedBinaryHash_exists`: constructs the binary hash family with the stated seed
  count.

## References

* [Ambainis, 2007][Ambainis2007ElementDistinctness]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.WalkFind.SearchAlgorithm

open scoped BigOperators

/-- The linear map evaluating the polynomial with the given `d` coefficients at the specified
`m` field nodes. -/
def sampledPolynomialEvaluation {K : Type*} [Field K] (d m : ℕ)
    (nodes : Fin m → K) : (Fin d → K) →ₗ[K] (Fin m → K) where
  toFun coefficients j := ((Polynomial.degreeLTEquiv K d).symm coefficients).val.eval (nodes j)
  map_add' a b := by
    ext j
    simp
  map_smul' a b := by
    ext j
    simp

/-- Evaluation at `m` distinct nodes is surjective for polynomials with `d` coefficients when `m
≤ d`. -/
theorem sampledPolynomialEvaluation_surjective {K : Type*} [Field K]
    {d m : ℕ} (hmd : m ≤ d) (nodes : Fin m → K)
    (hinj : Function.Injective nodes) :
    Function.Surjective (sampledPolynomialEvaluation d m nodes) := by
  classical
  intro values
  let p := Lagrange.interpolate Finset.univ nodes values
  have hp : p ∈ Polynomial.degreeLT K d := by
    apply Polynomial.mem_degreeLT.mpr
    apply lt_of_lt_of_le (Lagrange.degree_interpolate_lt _ (fun _ _ _ _ h => hinj h))
    simpa using! hmd
  refine ⟨Polynomial.degreeLTEquiv K d ⟨p, hp⟩, ?_⟩
  ext j
  simp only [sampledPolynomialEvaluation, LinearMap.coe_mk, AddHom.coe_mk,
    LinearEquiv.symm_apply_apply]
  exact Lagrange.eval_interpolate_at_node values
    (fun _ _ _ _ h => hinj h) (Finset.mem_univ j)

/-- Every fiber of a surjective additive homomorphism between the stated finite structures has
uniform probability `1 / Fintype.card Y`. -/
theorem uniformAdditiveFiberProbability
    {G Y : Type*} [AddGroup G] [Fintype G] [AddMonoid Y] [Fintype Y] [DecidableEq Y]
    (f : G →+ Y) (hsurj : Function.Surjective f) (y : Y) :
    ((Finset.univ.filter (fun g : G => f g = y)).card : ℝ) / Fintype.card G =
      1 / (Fintype.card Y : ℝ) := by
  classical
  let count := (Finset.univ.filter (fun g : G => f g = y)).card
  have hcount (a : Y) :
      (Finset.univ.filter (fun g : G => f g = a)).card = count :=
    AddMonoidHom.card_fiber_eq_of_mem_range f (hsurj a) (hsurj y)
  have htotalNat : Fintype.card G = Fintype.card Y * count := by
    calc
      Fintype.card G =
          ∑ a : Y, (Finset.univ.filter (fun g : G => f g = a)).card := by
        simpa only [Finset.card_univ] using!
          (Finset.card_eq_sum_card_fiberwise
            (s := (Finset.univ : Finset G)) (t := (Finset.univ : Finset Y))
            (f := fun g => f g) (by intro g _; exact Finset.mem_univ (f g)))
      _ = Fintype.card Y * count := by
        simp only [hcount, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id]
  have htotal : (Fintype.card G : ℝ) = (Fintype.card Y : ℝ) * (count : ℝ) := by
    exact_mod_cast htotalNat
  have hG : (Fintype.card G : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card G ≠ 0)
  have hY : (Fintype.card Y : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card Y ≠ 0)
  change (count : ℝ) / Fintype.card G = 1 / (Fintype.card Y : ℝ)
  field_simp [hG, hY]
  nlinarith [htotal]

/-- Uniform polynomial coefficients give each prescribed value tuple at `m ≤ d` distinct
finite-field nodes probability `1 / card(K)^m`. -/
theorem sampledPolynomialEvaluation_uniform
    {K : Type*} [Field K] [Fintype K] [DecidableEq K] {d m : ℕ} (hmd : m ≤ d)
    (nodes : Fin m → K) (hinj : Function.Injective nodes) (values : Fin m → K) :
    ((Finset.univ.filter (fun coefficients : Fin d → K =>
      sampledPolynomialEvaluation d m nodes coefficients = values)).card : ℝ) /
      Fintype.card (Fin d → K) = 1 / ((Fintype.card K : ℝ)^m) := by
  have h := uniformAdditiveFiberProbability
    (sampledPolynomialEvaluation d m nodes).toAddMonoidHom
    (sampledPolynomialEvaluation_surjective hmd nodes hinj) values
  change ((Finset.univ.filter (fun coefficients : Fin d → K =>
    sampledPolynomialEvaluation d m nodes coefficients = values)).card : ℝ) /
      Fintype.card (Fin d → K) = 1 / (Fintype.card (Fin m → K) : ℝ) at h
  simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] using! h

/-- The additive map obtained by evaluating a polynomial at the given nodes and applying the
binary coordinate to each value. -/
def sampledPolynomialBinaryEvaluation {K : Type*} [Field K] (d m : ℕ)
    (nodes : Fin m → K) (coordinate : K →+ ZMod 2) :
    (Fin d → K) →+ (Fin m → ZMod 2) where
  toFun coefficients j := coordinate (sampledPolynomialEvaluation d m nodes coefficients j)
  map_zero' := by ext j; simp
  map_add' a b := by ext j; simp

/-- For `m ≤ d` distinct nodes and a surjective binary coordinate, the binary polynomial
evaluation map is surjective. -/
theorem sampledPolynomialBinaryEvaluation_surjective {K : Type*} [Field K]
    {d m : ℕ} (hmd : m ≤ d) (nodes : Fin m → K)
    (hinj : Function.Injective nodes) (coordinate : K →+ ZMod 2)
    (hcoordinate : Function.Surjective coordinate) :
    Function.Surjective (sampledPolynomialBinaryEvaluation d m nodes coordinate) := by
  classical
  intro values
  choose preimages hpreimages using fun j => hcoordinate (values j)
  obtain ⟨coefficients, hcoefficients⟩ :=
    sampledPolynomialEvaluation_surjective hmd nodes hinj preimages
  refine ⟨coefficients, ?_⟩
  ext j
  change coordinate (sampledPolynomialEvaluation d m nodes coefficients j) = values j
  rw [hcoefficients, hpreimages]

/-- For `m ≤ d` distinct nodes and a surjective binary coordinate, every prescribed binary
output tuple has probability `1 / 2^m` under uniform coefficients. -/
theorem sampledPolynomialBinaryEvaluation_uniform
    {K : Type*} [Field K] [Fintype K] {d m : ℕ} (hmd : m ≤ d)
    (nodes : Fin m → K) (hinj : Function.Injective nodes)
    (coordinate : K →+ ZMod 2) (hcoordinate : Function.Surjective coordinate)
    (values : Fin m → ZMod 2) :
    ((Finset.univ.filter (fun coefficients : Fin d → K =>
      sampledPolynomialBinaryEvaluation d m nodes coordinate coefficients = values)).card : ℝ) /
      Fintype.card (Fin d → K) = 1 / (2^m : ℝ) := by
  have h := uniformAdditiveFiberProbability
    (sampledPolynomialBinaryEvaluation d m nodes coordinate)
    (sampledPolynomialBinaryEvaluation_surjective hmd nodes hinj coordinate hcoordinate) values
  simpa only [Fintype.card_fun, Fintype.card_fin, ZMod.card, Nat.cast_pow,
    Nat.cast_ofNat] using! h

/-- Every field carrying an algebra structure over `ZMod 2` possesses a surjective additive map
to `ZMod 2`. -/
theorem fieldBinaryCoordinate_exists {K : Type*} [Field K] [Algebra (ZMod 2) K] :
    ∃ coordinate : K →+ ZMod 2, Function.Surjective coordinate := by
  have hinj : Function.Injective (Algebra.linearMap (ZMod 2) K) :=
    (algebraMap (ZMod 2) K).injective
  obtain ⟨coordinate, hcoordinate⟩ := LinearMap.exists_leftInverse_of_injective
    (Algebra.linearMap (ZMod 2) K) (LinearMap.ker_eq_bot.mpr hinj)
  refine ⟨coordinate.toAddMonoidHom, ?_⟩
  intro value
  refine ⟨algebraMap (ZMod 2) K value, ?_⟩
  exact congrArg (fun f : (ZMod 2) →ₗ[ZMod 2] (ZMod 2) => f value) hcoordinate

/-- An equivalence from `Fin R` to a finite type transports seed event probability to the
normalized count on that type. -/
theorem eventProbability_reindex {R : ℕ} {G : Type*} [Fintype G]
    (encoding : Fin R ≃ G) (P : G → Prop) [DecidablePred P] :
    eventProbability (fun s => P (encoding s)) =
      ((Finset.univ.filter P).card : ℝ) / Fintype.card G := by
  classical
  have hcard : (Finset.univ.filter (fun s => P (encoding s))).card =
      (Finset.univ.filter P).card := by
    simpa only [Fintype.card_subtype] using!
      Fintype.card_congr (encoding.subtypeEquivOfSubtype (p := P))
  have hsize : R = Fintype.card G := by
    simpa only [Fintype.card_fin] using! Fintype.card_congr encoding
  unfold eventProbability
  congr 1
  · norm_cast
    convert! hcard using 1
    apply congrArg Finset.card
    ext s
    simp
  · exact_mod_cast hsize

/-- The Boolean hash obtained by decoding a seed into polynomial coefficients, evaluating at the
input node, and applying the binary coordinate and Boolean encoding. -/
def polynomialBinaryHash {K : Type*} [Field K] {R N d : ℕ}
    (seeds : Fin R ≃ (Fin d → K)) (nodes : Fin N → K)
    (coordinate : K →+ ZMod 2) (bits : ZMod 2 ≃ Bool) : Fin R → Fin N → Bool :=
  fun s i => bits (coordinate (sampledPolynomialEvaluation d N nodes (seeds s) i))

/-- With distinct nodes and a surjective binary coordinate, any prescribed outputs at `m ≤ d`
distinct inputs occur with probability exactly `1 / 2^m`. -/
theorem polynomialBinaryHash_independent {K : Type*} [Field K] [Fintype K]
    {R N d : ℕ} (seeds : Fin R ≃ (Fin d → K))
    (nodes : Fin N → K) (hnodes : Function.Injective nodes)
    (coordinate : K →+ ZMod 2) (hcoordinate : Function.Surjective coordinate)
    (bits : ZMod 2 ≃ Bool) (m : ℕ) (hmd : m ≤ d)
    (i : Fin m → Fin N) (hi : Function.Injective i) (values : Fin m → Bool) :
    eventProbability (fun s =>
      ∀ j, polynomialBinaryHash seeds nodes coordinate bits s (i j) = values j) =
        1/(2^m : ℝ) := by
  classical
  have huniform := sampledPolynomialBinaryEvaluation_uniform hmd (nodes ∘ i) (hnodes.comp hi)
    coordinate hcoordinate (fun j => bits.symm (values j))
  have hevent (s : Fin R) :
      (∀ j, polynomialBinaryHash seeds nodes coordinate bits s (i j) = values j) ↔
        sampledPolynomialBinaryEvaluation d m (nodes ∘ i) coordinate (seeds s) =
          (fun j => bits.symm (values j)) := by
    change (∀ j, bits (coordinate (((Polynomial.degreeLTEquiv K d).symm
      (seeds s)).val.eval (nodes (i j)))) = values j) ↔
      (fun j => coordinate (((Polynomial.degreeLTEquiv K d).symm
        (seeds s)).val.eval (nodes (i j)))) = (fun j => bits.symm (values j))
    simp only [funext_iff, Equiv.apply_eq_iff_eq_symm_apply]
  calc
    _ = eventProbability (fun s =>
        sampledPolynomialBinaryEvaluation d m (nodes ∘ i) coordinate (seeds s) =
          (fun j => bits.symm (values j))) := by
      unfold eventProbability
      congr 2
      apply congrArg Finset.card
      ext s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hevent]
    _ = _ := (eventProbability_reindex seeds _).trans huniform

/-- For `N ≥ 2`, there exists a binary `d`-wise independent hash family on `Fin N` with `2^(d *
Nat.clog 2 (N + 1))` seeds [Ambainis2007ElementDistinctness]. -/
theorem logarithmicSeedBinaryHash_exists (N d : ℕ) (hN : 2 ≤ N) :
    ∃ hash : Fin (2^(d * Nat.clog 2 (N+1))) → Fin N → Bool,
      ∀ m : ℕ, m ≤ d → ∀ i : Fin m → Fin N, Function.Injective i →
        ∀ values : Fin m → Bool,
          eventProbability (fun s => ∀ j, hash s (i j) = values j) = 1/(2^m : ℝ) := by
  classical
  let width := Nat.clog 2 (N+1)
  have hwidth : width ≠ 0 := by
    dsimp [width]
    intro hzero
    have hpow := Nat.le_pow_clog (by decide : 1 < 2) (N+1)
    rw [hzero] at hpow
    simp only [pow_zero] at hpow
    omega
  let K := GaloisField 2 width
  letI : Fintype K := Fintype.ofFinite K
  have hK : Fintype.card K = 2^width := by
    simpa only [Nat.card_eq_fintype_card] using! GaloisField.card 2 width hwidth
  let fieldEncoding : K ≃ Fin (2^width) := Fintype.equivFinOfCardEq hK
  have hNwidth : N ≤ 2^width :=
    le_trans (Nat.le_succ N) (Nat.le_pow_clog (by decide : 1 < 2) (N+1))
  let nodes : Fin N → K := fun i => fieldEncoding.symm (Fin.castLE hNwidth i)
  have hnodes : Function.Injective nodes := by
    intro i j hij
    have h := congrArg fieldEncoding hij
    simpa only [nodes, Equiv.apply_symm_apply, Fin.castLE_inj] using! h
  obtain ⟨coordinate, hcoordinate⟩ := fieldBinaryCoordinate_exists (K := K)
  have hcoefficients : Fintype.card (Fin d → K) = 2^(d*width) := by
    simp only [Fintype.card_fun, Fintype.card_fin, hK]
    rw [← pow_mul, Nat.mul_comm width d]
  let seedEncoding : Fin (2^(d*width)) ≃ (Fin d → K) :=
    (Fintype.equivFinOfCardEq hcoefficients).symm
  let bitEncoding : ZMod 2 ≃ Bool :=
    (Fintype.equivFinOfCardEq (ZMod.card 2)).trans finTwoEquiv
  refine ⟨polynomialBinaryHash seedEncoding nodes coordinate bitEncoding, ?_⟩
  intro m hmd i hi values
  exact polynomialBinaryHash_independent seedEncoding nodes hnodes coordinate hcoordinate
    bitEncoding m hmd i hi values

end Qatlib.Concepts.WalkFind.SearchAlgorithm
