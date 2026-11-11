/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.IsingPartit08.MainResults.Defs
import Mathlib.Data.List.Sublists

/-!
# Binary gate products and sublist expansions

This module represents gate coefficients as real functions `PAlg` on binary vectors and defines
the signed convolution `pMul` using the bilinear phase `cocycle`. Products of gates `gate lam b`
expand into sums over sublists, with the omitted-gate power of `lam` and the accumulated sign
`phase`, providing algebraic expansion identities for Theorem 1 of [Geraci2008].

## Main statements

* `pMul_basis`: computes the signed convolution of two basis coefficients.
* `pProdBasis_eq`: reduces a basis product to its total label and phase.
* `product_expansion`: expands a gate product over all sublists.

## References

* [Geraci, 2008][Geraci2008]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical

attribute [local instance] Classical.propDecidable

namespace Qatlib.Papers.IsingPartit08.MainResults

/-- The real coefficient functions on binary vectors with `R` coordinates. -/
abbrev PAlg (R : ℕ) := F2Vec R → ℝ

/-- The coefficient function equal to `1` at `b` and zero at every other binary vector. -/
def pBasis {R : ℕ} (b : F2Vec R) : PAlg R := fun c => if c = b then 1 else 0

/-- The coefficient function supported at the zero binary vector. -/
def pOne (R : ℕ) : PAlg R := pBasis (0 : F2Vec R)

/-- The binary bilinear form `∑ i, ∑ j, a i * C i j * b j` controlling multiplication signs. -/
def cocycle {R : ℕ} (C : Matrix (Fin R) (Fin R) (ZMod 2)) (a b : F2Vec R) : ZMod 2 :=
  ∑ i, ∑ j, a i * C i j * b j

/-- The bilinear phase vanishes when its second vector is zero. -/
@[simp] theorem cocycle_zero_right {R : ℕ} (C : Matrix (Fin R) (Fin R) (ZMod 2))
    (a : F2Vec R) : cocycle C a 0 = 0 := by
  simp [cocycle]

/-- The bilinear phase vanishes when its first vector is zero. -/
@[simp] theorem cocycle_zero_left {R : ℕ} (C : Matrix (Fin R) (Fin R) (ZMod 2))
    (b : F2Vec R) : cocycle C 0 b = 0 := by
  simp [cocycle]

/-- The signed convolution of coefficient functions, with phase given by `cocycle C x (c - x)`. -/
def pMul {R : ℕ} (C : Matrix (Fin R) (Fin R) (ZMod 2)) (f g : PAlg R) : PAlg R :=
  fun c => ∑ x : F2Vec R, f x * g (c - x) * paritySign (cocycle C x (c - x))

/-- The signed convolution of basis functions at `a` and `b` is the basis function at `a + b`
multiplied by the sign of `cocycle C a b`. See [Geraci2008]. -/
theorem pMul_basis {R : ℕ} (C : Matrix (Fin R) (Fin R) (ZMod 2)) (a b : F2Vec R) :
    pMul C (pBasis a) (pBasis b) =
      (fun c => paritySign (cocycle C a b) * pBasis (a + b) c) := by
  funext c
  simp only [pMul, pBasis]
  rw [Finset.sum_eq_single a
      (by intro x _ hx; simp [hx])
      (by intro h; simp at h)]
  by_cases hc : c = a + b
  · subst hc
    have hsub : a + b - a = b := by abel
    simp [hsub]
  · have hne : c - a ≠ b := by
      intro h
      apply hc
      have hsplit : c = (c - a) + a := by abel
      rw [hsplit, h]
      abel
    simp [hc, hne]

/-- A real scalar multiplying the right coefficient function factors out of `pMul`. -/
theorem pMul_scale_right {R : ℕ} (C : Matrix (Fin R) (Fin R) (ZMod 2)) (r : ℝ)
    (f g : PAlg R) :
    pMul C f (fun c => r * g c) = fun c => r * pMul C f g c := by
  funext c
  unfold pMul
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- The accumulated real sign of a list of binary labels, computed recursively from their
bilinear phases. -/
def phase {R : ℕ} (C : Matrix (Fin R) (Fin R) (ZMod 2)) : List (F2Vec R) → ℝ
  | [] => 1
  | b :: rest => paritySign (cocycle C b rest.sum) * phase C rest

/-- The recursive signed-convolution product of the basis functions associated with a list of
labels. -/
def pProdBasis {R : ℕ} (C : Matrix (Fin R) (Fin R) (ZMod 2)) :
    List (F2Vec R) → PAlg R
  | [] => pOne R
  | b :: rest => pMul C (pBasis b) (pProdBasis C rest)

/-- A product of basis functions is the basis function at the sum of their labels multiplied by
`phase C l`. See [Geraci2008]. -/
theorem pProdBasis_eq {R : ℕ} (C : Matrix (Fin R) (Fin R) (ZMod 2))
    (l : List (F2Vec R)) :
    pProdBasis C l = fun c => phase C l * pBasis l.sum c := by
  induction l with
  | nil =>
      funext c
      simp [pProdBasis, phase, pOne, pBasis]
  | cons b rest ih =>
      show pMul C (pBasis b) (pProdBasis C rest) =
        fun c => phase C (b :: rest) * pBasis (b :: rest).sum c
      rw [ih, pMul_scale_right]
      funext c
      rw [pMul_basis]
      simp only [phase, List.sum_cons]
      ring

/-- The gate coefficient function `lam * pOne R + pBasis b`. -/
def gate (lam : ℝ) {R : ℕ} (b : F2Vec R) : PAlg R :=
  fun c => lam * pOne R c + pBasis b c

/-- The recursive signed-convolution product of the gate coefficients for a list of labels. -/
def pProd {R : ℕ} (C : Matrix (Fin R) (Fin R) (ZMod 2)) (lam : ℝ) :
    List (F2Vec R) → PAlg R
  | [] => pOne R
  | b :: rest => pMul C (gate lam b) (pProd C lam rest)

/-- The signed convolution distributes over addition in its left argument. -/
theorem pMul_add_left {R : ℕ} (C : Matrix (Fin R) (Fin R) (ZMod 2))
    (f g h : PAlg R) :
    pMul C (fun c => f c + g c) h = fun c => pMul C f h c + pMul C g h c := by
  funext c
  simp only [pMul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- A real scalar multiplying the left coefficient function factors out of `pMul`. -/
theorem pMul_scale_left {R : ℕ} (C : Matrix (Fin R) (Fin R) (ZMod 2))
    (r : ℝ) (f g : PAlg R) :
    pMul C (fun c => r * f c) g = fun c => r * pMul C f g c := by
  funext c
  simp only [pMul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- The zero-label basis coefficient is a left identity for `pMul`. -/
theorem pMul_one_left {R : ℕ} (C : Matrix (Fin R) (Fin R) (ZMod 2))
    (f : PAlg R) : pMul C (pOne R) f = f := by
  funext c
  simp only [pMul, pOne, pBasis]
  rw [Finset.sum_eq_single (0 : F2Vec R)]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    simp at h

/-- The recursive expansion that chooses either the scalar identity term or the basis term at
each gate. -/
def pExpand {R : ℕ} (C : Matrix (Fin R) (Fin R) (ZMod 2)) (lam : ℝ) :
    List (F2Vec R) → PAlg R
  | [] => pOne R
  | b :: rest => fun c => lam * pExpand C lam rest c + pMul C (pBasis b) (pExpand C lam rest) c

/-- The recursive gate product equals the recursively expanded coefficient function. -/
theorem pProd_eq_pExpand {R : ℕ} (C : Matrix (Fin R) (Fin R) (ZMod 2))
    (lam : ℝ) (l : List (F2Vec R)) :
    pProd C lam l = pExpand C lam l := by
  induction l with
  | nil => simp [pProd, pExpand]
  | cons b rest ih =>
      simp only [pProd, pExpand]
      rw [ih]
      unfold gate
      rw [pMul_add_left, pMul_scale_left, pMul_one_left]

/-- The sum over all sublists of `l`, with each term weighted by the omitted-label power of
`lam`, its phase, and its total-label basis coefficient. -/
def subExp {R : ℕ} (C : Matrix (Fin R) (Fin R) (ZMod 2)) (lam : ℝ)
    (l : List (F2Vec R)) (c : F2Vec R) : ℝ :=
  (l.sublists.map (fun S => lam ^ (l.length - S.length) * phase C S * pBasis S.sum c)).sum

/-- Summing a list mapped by a pointwise sum equals the sum of the two mapped-list sums. -/
theorem sumMapAdd {α : Type} (l : List α) (f g : α → ℝ) :
    (l.map (fun x => f x + g x)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]; ring

/-- A fixed real factor on the left can be moved outside a mapped-list sum. -/
theorem sumMapMul {α : Type} (l : List α) (r : ℝ) (f : α → ℝ) :
    (l.map (fun x => r * f x)).sum = r * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]; ring

/-- A fixed real factor on the right can be moved inside a mapped-list sum. -/
theorem sumMapMulRight {α : Type} (l : List α) (r : ℝ) (f : α → ℝ) :
    (l.map f).sum * r = (l.map (fun x => f x * r)).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [add_mul, ih]

/-- Functions agreeing on every member of a list have equal mapped-list sums. -/
theorem sumMapCongr {α : Type} (l : List α) (f g : α → ℝ)
    (h : ∀ x ∈ l, f x = g x) :
    (l.map f).sum = (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [h a (by simp)]
      rw [ih (fun x hx => h x (List.mem_cons_of_mem a hx))]

/-- Summing the flattened pairs `[f x, g x]` equals summing the pointwise sums `f x + g x`. -/
theorem sumFlatMapPair {α : Type} (l : List α) (f g : α → ℝ) :
    (l.flatMap (fun x => [f x, g x])).sum = (l.map (fun x => f x + g x)).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
      simp only [List.flatMap_cons, List.sum_append, List.map_cons, List.sum_cons,
        List.sum_nil]
      rw [ih]; ring

/-- Left multiplication by the basis coefficient at `b` evaluates the other coefficient at `c -
b` and multiplies by the corresponding bilinear phase sign. -/
theorem pMul_pBasis_apply {R : ℕ} (C : Matrix (Fin R) (Fin R) (ZMod 2))
    (b : F2Vec R) (G : PAlg R) (c : F2Vec R) :
    pMul C (pBasis b) G c = G (c - b) * paritySign (cocycle C b (c - b)) := by
  simp only [pMul]
  rw [Finset.sum_eq_single b]
  · simp [pBasis]
  · intro y _ hy
    simp [pBasis, hy]
  · intro h
    exact absurd (Finset.mem_univ b) h

/-- Rewrites a shifted sublist basis term and its multiplication sign as the basis term at `b +
x.sum` with the accumulated phase. -/
theorem subExpTerm {R : ℕ} (C : Matrix (Fin R) (Fin R) (ZMod 2))
    (b : F2Vec R) (lam : ℝ) (x : List (F2Vec R)) (c : F2Vec R) (n : ℕ) :
    (lam ^ (n - x.length) * phase C x * pBasis x.sum (c - b)) *
        paritySign (cocycle C b (c - b))
      = lam ^ (n - x.length) * (paritySign (cocycle C b x.sum) * phase C x) *
          pBasis (b + x.sum) c := by
  by_cases hx : c - b = x.sum
  · have hpc : pBasis x.sum (c - b) = 1 := by simp [pBasis, hx]
    have hc : c = x.sum + b := sub_eq_iff_eq_add.mp hx
    have hc' : c = b + x.sum := by rw [hc, add_comm]
    have hpt : pBasis (b + x.sum) c = 1 := by simp [pBasis, hc']
    have hcoc : cocycle C b (c - b) = cocycle C b x.sum := by rw [hx]
    rw [hpc, hpt, hcoc]; ring
  · have hpc : pBasis x.sum (c - b) = 0 := by simp [pBasis, hx]
    have hne : c ≠ b + x.sum := by
      intro h
      apply hx
      rw [sub_eq_iff_eq_add]
      rw [h, add_comm]
    have hpt : pBasis (b + x.sum) c = 0 := by simp [pBasis, hne]
    rw [hpc, hpt]; ring

/-- The recursive expansion equals the explicit sublist sum `subExp`. -/
theorem pExpand_eq_subExp {R : ℕ} (C : Matrix (Fin R) (Fin R) (ZMod 2))
    (lam : ℝ) (l : List (F2Vec R)) :
    pExpand C lam l = fun c => subExp C lam l c := by
  induction l with
  | nil =>
      funext c
      simp [pExpand, subExp, pOne, pBasis, phase]
  | cons b rest ih =>
      funext c
      rw [show pExpand C lam (b :: rest) c =
          lam * pExpand C lam rest c + pMul C (pBasis b) (pExpand C lam rest) c from rfl]
      rw [ih]
      rw [show subExp C lam (b :: rest) c =
          (List.map (fun S => lam ^ ((b :: rest).length - S.length) * phase C S *
            pBasis S.sum c) ((b :: rest).sublists)).sum from rfl]
      rw [List.sublists_cons, List.bind_eq_flatMap, List.map_flatMap]
      simp only [List.map_cons, List.map_nil]
      rw [sumFlatMapPair, sumMapAdd]
      have h1 : (List.map (fun S => lam ^ ((b :: rest).length - S.length) * phase C S *
            pBasis S.sum c) rest.sublists).sum = lam * subExp C lam rest c := by
        rw [show subExp C lam rest c =
            (List.map (fun S => lam ^ (rest.length - S.length) * phase C S *
              pBasis S.sum c) rest.sublists).sum from rfl]
        rw [← sumMapMul]
        apply sumMapCongr
        intro x hx
        have hle : x.length ≤ rest.length :=
          (List.mem_sublists.mp hx).length_le
        have hexp : (b :: rest).length - x.length = (rest.length - x.length) + 1 := by
          simp only [List.length_cons]
          exact Nat.succ_sub hle
        rw [hexp, pow_succ']
        ring
      have h2 : (List.map (fun x => lam ^ ((b :: rest).length - (b :: x).length) *
            phase C (b :: x) * pBasis (b :: x).sum c) rest.sublists).sum =
          pMul C (pBasis b) (fun c' => subExp C lam rest c') c := by
        rw [pMul_pBasis_apply]
        rw [show subExp C lam rest (c - b) =
            (List.map (fun S => lam ^ (rest.length - S.length) * phase C S *
              pBasis S.sum (c - b)) rest.sublists).sum from rfl]
        rw [sumMapMulRight]
        apply sumMapCongr
        intro x _
        simp only [List.length_cons, List.sum_cons, phase, Nat.succ_sub_succ]
        exact (subExpTerm C b lam x c rest.length).symm
      rw [h1, h2]

/-- A gate product equals the sum over sublists of the omitted-gate power of `lam` times the
accumulated phase and total-label basis coefficient, as in the expansion underlying [Geraci,
Theorem 1][Geraci2008]. -/
theorem product_expansion {R : ℕ} (C : Matrix (Fin R) (Fin R) (ZMod 2)) (lam : ℝ)
    (gates : List (F2Vec R)) :
    pProd C lam gates =
      fun c => (gates.sublists.map (fun S =>
        lam ^ (gates.length - S.length) * phase C S * pBasis S.sum c)).sum := by
  rw [pProd_eq_pExpand, pExpand_eq_subExp]
  rfl

end Qatlib.Papers.IsingPartit08.MainResults
