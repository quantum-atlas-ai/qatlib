/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.LatticeFilter21.MainResults.Model.Problems
public import Qatlib.Concepts.QuditTeleport.TeleportCore.CharacterQFT

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# The multi-register QFT collapse from the coherent LWE state to the SIS state

Fixed source version: arXiv:2108.11015, §3.1 ([ChenLiuZhandry2021], Proposition 20).

The paper asserts that the SIS state `|φSIS⟩ = ∑_{Az = 0} f(z)|z⟩` is obtained
from the coherent LWE state `|φLWE⟩ = ∑_u ∑_e f̂(e)|uᵀA + e⟩` by a Fourier
transform. This module proves the underlying amplitude identity exactly, with
the paper's positive-character convention and its unnormalised amplitude
summation:

`qftVec (clweState f Aᵀ) = fun y => qⁿ * sisState (fun x => f (-x)) A y`.

Two corrections to a naive rendering are forced by the existing definitions and
are recorded in the statement rather than hidden:

* the source's global normalisation `q^{-n/2}` is omitted, so the identity
  carries the factor `qⁿ` instead of matching the physical states exactly;
* the positive-character transform produces the reflection `x ↦ -x` of the
  error amplitude (the same reflection as `zmodQFT_zmodQFT`), so the SIS state
  is taken with the reflected amplitude. For an even amplitude the reflection
  cancels, as in `qftVec_clweState_transpose_of_even`.

The statement is purely about amplitudes; it does not assert that either state
is normalised, efficiently constructible, or that the transform solves `SIS`.
-/

namespace Qatlib.Papers.LatticeFilter21.MainResults

open scoped BigOperators
open Qatlib.Papers.LatticeFilter21.MainResults
open Qatlib.Concepts.QuditTeleport.TeleportCore

set_option autoImplicit false

/-- The paper's `m`-register transform is the character transform of the concept layer. -/
theorem qftVec_eq_characterQFT {m q : ℕ} [NeZero q] (φ : QState (Fin m → Zq q)) :
    qftVec φ = characterQFT φ := rfl

/-- The product Fourier amplitude expands as the scaled character sum of the coordinatewise
product amplitude. -/
theorem fhatVec_eq_characterWeight {m q : ℕ} [NeZero q] (f : Zq q → ℂ) (e : Fin m → Zq q) :
    fhatVec f e =
      characterScale (N := q) m *
        ∑ x : Fin m → Zq q, prodStdAddChar e x * ∏ i, f (x i) := by
  simp only [fhatVec, fhat, invSqrt, characterScale, prodStdAddChar_apply]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← sum_pi_prod (g := fun i y => ZMod.stdAddChar (y * e i) * f y)]
  refine congrArg _ (Finset.sum_congr rfl fun x _ => ?_)
  rw [Finset.prod_mul_distrib]

/-- Standard characters turn a sum inside the exponent into a product. -/
theorem stdAddChar_mul_sum {ι : Type*} {q : ℕ} [NeZero q] (s : Finset ι) (t : Zq q)
    (c : ι → Zq q) :
    ZMod.stdAddChar (t * ∑ i ∈ s, c i) = ∏ i ∈ s, ZMod.stdAddChar (t * c i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
      rw [Finset.sum_cons, mul_add, AddChar.map_add_eq_mul, ih, Finset.prod_cons]

/-- The product character at the matrix-vector product of the transposed matrix is the
coordinatewise product of standard characters along the original matrix. -/
theorem prodStdAddChar_mulVec_transpose {n m q : ℕ} [NeZero q]
    (A : Matrix (Fin n) (Fin m) (Zq q)) (y : Fin m → Zq q) (u : Fin n → Zq q) :
    prodStdAddChar (A.mulVec y) u =
      ∏ i, ZMod.stdAddChar (y i * (A.transpose.mulVec u) i) := by
  have hleft : prodStdAddChar (A.mulVec y) u =
      ∏ j : Fin n, ∏ i : Fin m, ZMod.stdAddChar (u j * (A j i * y i)) := by
    rw [prodStdAddChar_apply]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Matrix.mulVec_apply_eq_sum, stdAddChar_mul_sum]
  have hright : (∏ i : Fin m, ZMod.stdAddChar (y i * (A.transpose.mulVec u) i)) =
      ∏ i : Fin m, ∏ j : Fin n, ZMod.stdAddChar (u j * (A j i * y i)) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Matrix.mulVec_apply_eq_sum, stdAddChar_mul_sum]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Matrix.transpose_apply, show u j * (A j i * y i) = y i * (A j i * u j) by ring]
  rw [hleft, hright, Finset.prod_comm]

/-- The character sum over the registers of the expanded coherent state collapses to the
kernel indicator of `A` times the reflected product amplitude. -/
theorem sum_character_clweState_expansion {n m q : ℕ} [NeZero q] (f : Zq q → ℂ)
    (A : Matrix (Fin n) (Fin m) (Zq q)) (y : Fin m → Zq q) :
    (∑ x : Fin m → Zq q, prodStdAddChar y x *
        ∑ u : Fin n → Zq q, ∑ v : Fin m → Zq q,
          prodStdAddChar (x - A.transpose.mulVec u) v * ∏ i, f (v i))
      = (q : ℂ) ^ m * (∑ u : Fin n → Zq q, prodStdAddChar (A.mulVec y) u) *
          ∏ i, f ((-y) i) := by
  have hshift : ∀ (x : Fin m → Zq q) (u : Fin n → Zq q) (v : Fin m → Zq q),
      prodStdAddChar (x - A.transpose.mulVec u) v
        = prodStdAddChar x v * prodStdAddChar (-(A.transpose.mulVec u)) v := by
    intro x u v
    rw [sub_eq_add_neg, prodStdAddChar_add, AddChar.mul_apply]
  have hnegneg : ∀ (k z : Fin m → Zq q), prodStdAddChar (-k) (-z) = prodStdAddChar z k := by
    intro k z
    rw [prodStdAddChar_apply, prodStdAddChar_apply]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [Pi.neg_apply]
    congr 1
    ring
  have hchar : ∀ u : Fin n → Zq q,
      prodStdAddChar (-(A.transpose.mulVec u)) (-y) = prodStdAddChar (A.mulVec y) u := by
    intro u
    rw [hnegneg, prodStdAddChar_apply, prodStdAddChar_mulVec_transpose A y u]
    refine Finset.prod_congr rfl fun i _ => ?_
    congr 1
    ring
  simp_rw [hshift]
  calc
    ∑ x : Fin m → Zq q, prodStdAddChar y x *
        ∑ u : Fin n → Zq q, ∑ v : Fin m → Zq q,
          (prodStdAddChar x v * prodStdAddChar (-(A.transpose.mulVec u)) v) * ∏ i, f (v i)
        = ∑ x : Fin m → Zq q, ∑ u : Fin n → Zq q, ∑ v : Fin m → Zq q,
            (prodStdAddChar y x * prodStdAddChar x v) *
              prodStdAddChar (-(A.transpose.mulVec u)) v * ∏ i, f (v i) := by
          simp_rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun u _ =>
            Finset.sum_congr rfl fun v _ => by ring
    _ = ∑ u : Fin n → Zq q, ∑ x : Fin m → Zq q, ∑ v : Fin m → Zq q,
            (prodStdAddChar y x * prodStdAddChar x v) *
              prodStdAddChar (-(A.transpose.mulVec u)) v * ∏ i, f (v i) := by
          rw [Finset.sum_comm]
    _ = ∑ u : Fin n → Zq q, ∑ v : Fin m → Zq q, ∑ x : Fin m → Zq q,
            (prodStdAddChar y x * prodStdAddChar x v) *
              prodStdAddChar (-(A.transpose.mulVec u)) v * ∏ i, f (v i) := by
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [Finset.sum_comm]
    _ = ∑ u : Fin n → Zq q, ∑ v : Fin m → Zq q,
            (∑ x : Fin m → Zq q, prodStdAddChar y x * prodStdAddChar x v) *
              prodStdAddChar (-(A.transpose.mulVec u)) v * ∏ i, f (v i) := by
          refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
          rw [← Finset.sum_mul, ← Finset.sum_mul]
    _ = ∑ u : Fin n → Zq q, ∑ v : Fin m → Zq q,
            (if y + v = 0 then (q : ℂ) ^ m else 0) *
              prodStdAddChar (-(A.transpose.mulVec u)) v * ∏ i, f (v i) := by
          simp_rw [sum_prodStdAddChar_mul]
    _ = ∑ u : Fin n → Zq q,
            ((q : ℂ) ^ m * prodStdAddChar (-(A.transpose.mulVec u)) (-y)) *
              ∏ i, f ((-y) i) := by
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [Finset.sum_eq_single (-y)]
          · rw [ite_eq_left (by abel : y + -y = 0)]
          · intro v _ hv
            rw [ite_eq_right (by
              intro h
              apply hv
              calc v = v + y - y := by abel
                _ = y + v - y := by rw [add_comm]
                _ = 0 - y := by rw [h]
                _ = -y := by abel), zero_mul, zero_mul]
          · intro h
            simp at h
    _ = (q : ℂ) ^ m * (∑ u : Fin n → Zq q, prodStdAddChar (A.mulVec y) u) *
          ∏ i, f ((-y) i) := by
          simp_rw [hchar]
          rw [← Finset.sum_mul, ← Finset.mul_sum]

/-- Proposition 20 at the amplitude level: the `m`-fold Fourier transform of the coherent LWE
state with the transposed matrix is `qⁿ` times the SIS state of the reflected amplitude. -/
theorem qftVec_clweState_transpose {n m q : ℕ} [NeZero q] (f : Zq q → ℂ)
    (A : Matrix (Fin n) (Fin m) (Zq q)) :
    qftVec (clweState f A.transpose) =
      fun y => (q : ℂ) ^ n * sisState (fun x => f (-x)) A y := by
  funext y
  rw [qftVec_eq_characterQFT, characterQFT_apply]
  have hexpanded : ∀ z : Fin m → Zq q, clweState f A.transpose z =
      characterScale (N := q) m * ∑ u : Fin n → Zq q, ∑ v : Fin m → Zq q,
        prodStdAddChar (z - A.transpose.mulVec u) v * ∏ i, f (v i) := by
    intro z
    simp only [clweState, lweState, fhatVec]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    simpa only [fhatVec, Pi.sub_apply] using
      fhatVec_eq_characterWeight f (z - A.transpose.mulVec u)
  simp only [hexpanded]
  have hpull : (∑ x : Fin m → Zq q, prodStdAddChar y x *
        (characterScale (N := q) m * ∑ u : Fin n → Zq q, ∑ v : Fin m → Zq q,
          prodStdAddChar (x - A.transpose.mulVec u) v * ∏ i, f (v i))) =
      characterScale (N := q) m * (∑ x : Fin m → Zq q, prodStdAddChar y x *
        ∑ u : Fin n → Zq q, ∑ v : Fin m → Zq q,
          prodStdAddChar (x - A.transpose.mulVec u) v * ∏ i, f (v i)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => by ring
  rw [hpull, sum_character_clweState_expansion]
  calc
    characterScale (N := q) m *
        (characterScale (N := q) m * ((q : ℂ) ^ m *
          (∑ u : Fin n → Zq q, prodStdAddChar (A.mulVec y) u) * ∏ i, f ((-y) i)))
        = (characterScale (N := q) m * characterScale (N := q) m * (q : ℂ) ^ m) *
            ((∑ u : Fin n → Zq q, prodStdAddChar (A.mulVec y) u) * ∏ i, f ((-y) i)) := by
          ring
    _ = (∑ u : Fin n → Zq q, prodStdAddChar (A.mulVec y) u) * ∏ i, f ((-y) i) := by
          rw [characterScale_mul_self_mul_card, one_mul]
    _ = (if A.mulVec y = 0 then (q : ℂ) ^ n else 0) * ∏ i, f ((-y) i) := by
          rw [sum_prodStdAddChar]
    _ = (q : ℂ) ^ n * sisState (fun x => f (-x)) A y := by
          by_cases h : A.mulVec y = 0 <;> simp [sisState, h]

/-- For an even error amplitude the reflection produced by the positive-character transform
cancels, so the collapse returns the unreflected SIS state. -/
theorem qftVec_clweState_transpose_of_even {n m q : ℕ} [NeZero q] (f : Zq q → ℂ)
    (A : Matrix (Fin n) (Fin m) (Zq q)) (hf : ∀ x, f (-x) = f x) :
    qftVec (clweState f A.transpose) =
      fun y => (q : ℂ) ^ n * sisState f A y := by
  rw [qftVec_clweState_transpose]
  have hfun : (fun x => f (-x)) = f := funext hf
  rw [hfun]

end Qatlib.Papers.LatticeFilter21.MainResults
