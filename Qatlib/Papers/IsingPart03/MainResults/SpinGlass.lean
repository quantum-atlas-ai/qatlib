/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Spin-glass partition sums and signed weight enumerators

This module defines a binary spin-glass partition sum `partition` and the quadratically signed
weight enumerator `qwgt`. Expanding the edge factors and summing binary characters enforces the
zero-parity constraint, yielding the normalized partition-function identity of Theorem 2 in
[Lidar2004].

## Main statements

* `source_prop1_double_fourier`: expands the partition function as a double binary sum.
* `source_eq20_spin_summation`: eliminates spin assignments by character orthogonality.
* `source_theorem2_qwgt`: identifies the normalized partition function with a signed weight
  enumerator.

## References

* [Lidar, 2004][Lidar2004]
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset

namespace Qatlib.Papers.IsingPart03.MainResults

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- The complex sign of a binary value, equal to `1` at zero and `-1` otherwise. -/
def sgn (x : ZMod 2) : ℂ := if x = 0 then 1 else -1

/-- The binary sign at zero equals `1`. -/
@[simp] lemma sgn_zero : sgn (0 : ZMod 2) = 1 := by simp [sgn]

/-- The binary sign at one equals `-1`. -/
@[simp] lemma sgn_one : sgn (1 : ZMod 2) = -1 := by rw [sgn]; exact if_neg (by decide)

/-- Every element of `ZMod 2` equals zero or one. -/
lemma eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  have h : (Finset.univ : Finset (ZMod 2)) = ({0, 1} : Finset (ZMod 2)) := by decide
  have hx : x ∈ ({0, 1} : Finset (ZMod 2)) := by rw [← h]; exact Finset.mem_univ x
  simpa using hx

/-- The binary sign maps addition to multiplication. -/
lemma sgn_add (x y : ZMod 2) : sgn (x + y) = sgn x * sgn y := by
  rcases eq_zero_or_one x with rfl | rfl <;> rcases eq_zero_or_one y with rfl | rfl
  · simp
  · simp
  · simp
  · have h : ((1 : ZMod 2) + 1) = 0 := by decide
    simp [sgn, h]

/-- The sign of a finite binary sum equals the product of its signs. -/
lemma sgn_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 2) :
    sgn (∑ i ∈ s, f i) = ∏ i ∈ s, sgn (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, Finset.prod_insert ha, sgn_add, ih]

/-- The sign of a natural-number multiple of a binary value equals the corresponding power of
its sign. -/
lemma sgn_natCast_mul (x : ZMod 2) (n : ℕ) : sgn ((n : ZMod 2) * x) = sgn x ^ n := by
  induction n with
  | zero => simp
  | succ k ih => rw [Nat.cast_succ, add_mul, sgn_add, ih, one_mul, pow_succ]

/-- Coercing the natural representative of an element of `ZMod 2` back to `ZMod 2` recovers the
element. -/
lemma natCast_val (x : ZMod 2) : ((x.val : ℕ) : ZMod 2) = x := by
  rcases eq_zero_or_one x with rfl | rfl <;> decide

/-- Every element of `ZMod 2` is idempotent under multiplication. -/
lemma mul_self (x : ZMod 2) : x * x = x := by
  rcases eq_zero_or_one x with rfl | rfl <;> decide

/-- A sum over `ZMod 2` is the sum of the values at zero and one. -/
lemma sum_zmod2 (g : ZMod 2 → ℂ) : (∑ x : ZMod 2, g x) = g 0 + g 1 := by
  have h : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  rw [h, Finset.sum_pair (by decide)]

/-- The binary endpoint-incidence matrix, with entry `1` when the vertex is an endpoint of the
edge. -/
def incidence (ends : E → V × V) : Matrix V E (ZMod 2) :=
  fun v e => if (ends e).1 = v ∨ (ends e).2 = v then 1 else 0

/-- The vector of binary vertex parities obtained by multiplying the incidence matrix by `b`. -/
def parity (ends : E → V × V) (b : E → ZMod 2) : V → ZMod 2 := (incidence ends).mulVec b

/-- The support size of a binary edge vector, computed as the sum of its natural
representatives. -/
def suppCard (b : E → ZMod 2) : ℕ := ∑ e, (b e).val

/-- The binary dot product of the edge vectors `b` and `w`. -/
def bDotW (b w : E → ZMod 2) : ZMod 2 := ∑ e, b e * w e

/-- The binary pairing of the vertex parity vector of `b` with the spin assignment `s`. -/
def alphaDotS (ends : E → V × V) (b : E → ZMod 2) (s : V → ZMod 2) : ZMod 2 :=
  ∑ v, parity ends b v * s v

/-- The binary sum of selected edge endpoint-spin sums. -/
def edgeSpinDot (ends : E → V × V) (b : E → ZMod 2) (s : V → ZMod 2) : ZMod 2 :=
  ∑ e, b e * (s (ends e).1 + s (ends e).2)

/-- The complex sign of the edge-sign bit plus the two endpoint-spin bits. -/
def edgeFactor (ends : E → V × V) (w : E → ZMod 2) (s : V → ZMod 2) (e : E) : ℂ :=
  sgn (w e + s (ends e).1 + s (ends e).2)

/-- The scaled product `Θ * ∏ e, (1 + edgeFactor ends w s e * lam)` for a spin assignment. -/
def boltzmann (ends : E → V × V) (w : E → ZMod 2) (Θ lam : ℂ) (s : V → ZMod 2) : ℂ :=
  Θ * ∏ e, (1 + edgeFactor ends w s e * lam)

/-- The sum of `boltzmann` over all binary spin assignments. -/
def partition (ends : E → V × V) (w : E → ZMod 2) (Θ lam : ℂ) : ℂ :=
  ∑ s : V → ZMod 2, boltzmann ends w Θ lam s

omit [Fintype E] [DecidableEq E] in

/-- For an edge with distinct endpoints, the incidence-weighted spin sum equals the sum of the
spins at its endpoints. -/
lemma sum_incidence_mul (ends : E → V × V) (hLoop : ∀ e, (ends e).1 ≠ (ends e).2)
    (s : V → ZMod 2) (e : E) :
    (∑ v, incidence ends v e * s v) = s (ends e).1 + s (ends e).2 := by
  classical
  have happ : ∀ v, incidence ends v e * s v
      = (if v = (ends e).1 then s v else 0) + (if v = (ends e).2 then s v else 0) := by
    intro v
    by_cases h1 : v = (ends e).1
    · by_cases h2 : v = (ends e).2
      · exact absurd (h1.symm.trans h2) (hLoop e)
      · have h1' : (ends e).1 = v := h1.symm
        have hi : incidence ends v e = 1 := by simp [incidence, h1']
        rw [hi, if_pos h1, if_neg h2]; ring
    · by_cases h2 : v = (ends e).2
      · have h2' : (ends e).2 = v := h2.symm
        have hi : incidence ends v e = 1 := by simp [incidence, h2']
        rw [hi, if_neg h1, if_pos h2]; ring
      · have h1' : ¬ (ends e).1 = v := fun h => h1 h.symm
        have h2' : ¬ (ends e).2 = v := fun h => h2 h.symm
        have hi : incidence ends v e = 0 := by
          simp [incidence, h1', h2']
        rw [hi, if_neg h1, if_neg h2]; ring
  rw [Finset.sum_congr rfl (fun v _ => happ v), Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp

omit [DecidableEq E] in

/-- For loop-free endpoints, the selected edge-spin sum equals the pairing of the vertex
parities with the spin assignment. -/
lemma edgeSpinDot_eq_alphaDotS (ends : E → V × V) (hLoop : ∀ e, (ends e).1 ≠ (ends e).2)
    (b : E → ZMod 2) (s : V → ZMod 2) :
    edgeSpinDot ends b s = alphaDotS ends b s := by
  classical
  have hstep : ∀ e : E, b e * (s (ends e).1 + s (ends e).2)
      = b e * (∑ v, incidence ends v e * s v) := by
    intro e; rw [sum_incidence_mul ends hLoop s e]
  calc edgeSpinDot ends b s
      = ∑ e, b e * (∑ v, incidence ends v e * s v) := by
          simp only [edgeSpinDot]
          exact Finset.sum_congr rfl (fun e _ => hstep e)
    _ = ∑ e, ∑ v, b e * (incidence ends v e * s v) := by
          simp [Finset.mul_sum]
    _ = ∑ v, ∑ e, b e * (incidence ends v e * s v) := Finset.sum_comm
    _ = ∑ v, (∑ e, incidence ends v e * b e) * s v := by
          refine Finset.sum_congr rfl (fun v _ => ?_)
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl (fun e _ => by ring)
    _ = alphaDotS ends b s := rfl

/-- The natural representative of zero in `ZMod 2` equals zero. -/
@[simp] lemma val_zero : (0 : ZMod 2).val = 0 := by decide

/-- The natural representative of one in `ZMod 2` equals one. -/
@[simp] lemma val_one : (1 : ZMod 2).val = 1 := by decide

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in

/-- The edge factor is the product of the edge-sign factor and the two endpoint-spin factors. -/
lemma edgeFactor_eq_paper (ends : E → V × V) (w : E → ZMod 2) (s : V → ZMod 2) (e : E) :
    edgeFactor ends w s e
      = sgn (w e) * (sgn (s (ends e).1) * sgn (s (ends e).2)) := by
  simp only [edgeFactor, sgn_add, mul_assoc]

omit [Fintype V] [DecidableEq V] [DecidableEq E] in

/-- The product over selected edge factors equals a power of `lam` times the sign of the
combined edge-spin and edge-sign pairings. -/
lemma prod_edgeFactor_pow (ends : E → V × V) (w : E → ZMod 2) (s : V → ZMod 2)
    (b : E → ZMod 2) (lam : ℂ) :
    (∏ e, (edgeFactor ends w s e * lam) ^ (b e).val)
      = lam ^ suppCard b * sgn (edgeSpinDot ends b s + bDotW b w) := by
  classical
  have hf : ∀ e, edgeFactor ends w s e ^ (b e).val
      = sgn (b e * (w e + s (ends e).1 + s (ends e).2)) := by
    intro e
    rw [edgeFactor, ← sgn_natCast_mul, natCast_val]
  have hsum : (∑ e, b e * (w e + s (ends e).1 + s (ends e).2))
      = bDotW b w + edgeSpinDot ends b s := by
    simp only [bDotW, edgeSpinDot, mul_add, Finset.sum_add_distrib]
    abel
  calc (∏ e, (edgeFactor ends w s e * lam) ^ (b e).val)
      = (∏ e, edgeFactor ends w s e ^ (b e).val) * (∏ e, lam ^ (b e).val) := by
          simp_rw [mul_pow, Finset.prod_mul_distrib]
    _ = (∏ e, sgn (b e * (w e + s (ends e).1 + s (ends e).2))) * lam ^ suppCard b := by
          rw [Finset.prod_pow_eq_pow_sum, suppCard]
          simp only [hf]
    _ = sgn (∑ e, b e * (w e + s (ends e).1 + s (ends e).2)) * lam ^ suppCard b := by
          rw [sgn_sum]
    _ = lam ^ suppCard b * sgn (edgeSpinDot ends b s + bDotW b w) := by
          rw [hsum, sgn_add, sgn_add]
          ring

omit [Fintype V] [DecidableEq V] in

/-- Expands the Boltzmann product into a sum over binary edge selections weighted by support
size and binary sign. -/
lemma boltzmann_expand (ends : E → V × V) (w : E → ZMod 2) (Θ lam : ℂ) (s : V → ZMod 2) :
    boltzmann ends w Θ lam s
      = Θ * ∑ b : E → ZMod 2, lam ^ suppCard b * sgn (edgeSpinDot ends b s + bDotW b w) := by
  classical
  unfold boltzmann
  congr 1
  have h1 : ∀ e : E, (1 + edgeFactor ends w s e * lam)
      = ∑ x : ZMod 2, (edgeFactor ends w s e * lam) ^ x.val := by
    intro e
    rw [sum_zmod2]
    simp
  calc ∏ e, (1 + edgeFactor ends w s e * lam)
      = ∏ e, ∑ x : ZMod 2, (edgeFactor ends w s e * lam) ^ x.val :=
          Finset.prod_congr rfl (fun e _ => h1 e)
    _ = ∑ b ∈ Fintype.piFinset (fun _ : E => (Finset.univ : Finset (ZMod 2))),
          ∏ e, (edgeFactor ends w s e * lam) ^ (b e).val :=
          Finset.prod_univ_sum _ _
    _ = ∑ b : E → ZMod 2, ∏ e, (edgeFactor ends w s e * lam) ^ (b e).val := by
          rw [Fintype.piFinset_univ]
    _ = ∑ b : E → ZMod 2, lam ^ suppCard b * sgn (edgeSpinDot ends b s + bDotW b w) :=
          Finset.sum_congr rfl (fun b _ => prod_edgeFactor_pow ends w s b lam)

/-- For loop-free endpoints, the partition function is the double sum over spins and edge
selections with phase determined by `alphaDotS + bDotW`, as in [Lidar, Proposition
1][Lidar2004]. -/
theorem source_prop1_double_fourier (ends : E → V × V) (hLoop : ∀ e, (ends e).1 ≠ (ends e).2)
    (w : E → ZMod 2) (Θ lam : ℂ) :
    partition ends w Θ lam
      = Θ * ∑ s : V → ZMod 2, ∑ b : E → ZMod 2,
          lam ^ suppCard b * sgn (alphaDotS ends b s + bDotW b w) := by
  classical
  simp only [partition]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [boltzmann_expand]
  congr 1
  exact Finset.sum_congr rfl (fun b _ => by rw [edgeSpinDot_eq_alphaDotS ends hLoop b s])

omit [DecidableEq E] in

/-- The spin-character sum equals `2 ^ card V` when the vertex parity vector vanishes and equals
zero otherwise. -/
theorem source_eq20_spin_summation (ends : E → V × V) (b : E → ZMod 2) :
    (∑ s : V → ZMod 2, sgn (alphaDotS ends b s))
      = if parity ends b = 0 then (2 : ℂ) ^ Fintype.card V else 0 := by
  classical
  have hfac : ∀ s : V → ZMod 2, sgn (alphaDotS ends b s)
      = ∏ v, sgn (parity ends b v * s v) := by
    intro s
    rw [alphaDotS, sgn_sum]
  calc (∑ s : V → ZMod 2, sgn (alphaDotS ends b s))
      = ∑ s : V → ZMod 2, ∏ v, sgn (parity ends b v * s v) :=
          Finset.sum_congr rfl (fun s _ => hfac s)
    _ = ∏ v, ∑ x : ZMod 2, sgn (parity ends b v * x) := by
          rw [Finset.prod_univ_sum]
          simp
    _ = ∏ v, (1 + sgn (parity ends b v)) := by
          apply Finset.prod_congr rfl
          intro v _
          rw [sum_zmod2]
          simp
    _ = if parity ends b = 0 then (2 : ℂ) ^ Fintype.card V else 0 := by
          by_cases hp : parity ends b = 0
          · rw [if_pos hp]
            have h2 : ∀ v, (1 + sgn (parity ends b v)) = (2 : ℂ) := by
              intro v
              have hv : parity ends b v = 0 := by rw [hp]; simp
              rw [hv]
              simp only [sgn_zero]
              norm_num
            rw [Finset.prod_congr rfl (fun v _ => h2 v), Finset.prod_const]
            norm_num
          · rw [if_neg hp]
            obtain ⟨v, hv⟩ := Function.ne_iff.mp hp
            have hv1 : parity ends b v = 1 := by
              rcases eq_zero_or_one (parity ends b v) with h | h
              · exact absurd h hv
              · exact h
            rw [Finset.prod_eq_zero (Finset.mem_univ v)]
            rw [hv1]
            simp

/-- For loop-free endpoints, summing spins leaves `2 ^ card V * Θ` times the signed sum over
zero-parity edge selections. See [Lidar2004]. -/
theorem source_eq23_zero_parity (ends : E → V × V) (hLoop : ∀ e, (ends e).1 ≠ (ends e).2)
    (w : E → ZMod 2) (Θ lam : ℂ) :
    partition ends w Θ lam
      = (2 : ℂ) ^ Fintype.card V * Θ *
          ∑ b : E → ZMod 2,
            if parity ends b = 0 then lam ^ suppCard b * sgn (bDotW b w) else 0 := by
  classical
  rw [source_prop1_double_fourier ends hLoop w Θ lam, Finset.sum_comm]
  have hstep : ∀ b : E → ZMod 2,
      (∑ s : V → ZMod 2, lam ^ suppCard b * sgn (alphaDotS ends b s + bDotW b w))
        = (if parity ends b = 0 then (2 : ℂ) ^ Fintype.card V else 0) *
            (lam ^ suppCard b * sgn (bDotW b w)) := by
    intro b
    have hsplit : (∑ s : V → ZMod 2, lam ^ suppCard b * sgn (alphaDotS ends b s + bDotW b w))
        = ∑ s : V → ZMod 2, sgn (alphaDotS ends b s) * (lam ^ suppCard b * sgn (bDotW b w)) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [sgn_add]
      ring
    rw [hsplit]
    calc (∑ s : V → ZMod 2, sgn (alphaDotS ends b s) * (lam ^ suppCard b * sgn (bDotW b w)))
        = (∑ s : V → ZMod 2, sgn (alphaDotS ends b s)) *
            (lam ^ suppCard b * sgn (bDotW b w)) := (Finset.sum_mul ..).symm
      _ = (if parity ends b = 0 then (2 : ℂ) ^ Fintype.card V else 0) *
            (lam ^ suppCard b * sgn (bDotW b w)) := by
            rw [source_eq20_spin_summation]
  rw [Finset.sum_congr rfl (fun b _ => hstep b)]
  have hfac : ∀ b : E → ZMod 2,
      (if parity ends b = 0 then (2 : ℂ) ^ Fintype.card V else 0) *
          (lam ^ suppCard b * sgn (bDotW b w))
        = (2 : ℂ) ^ Fintype.card V *
            (if parity ends b = 0 then lam ^ suppCard b * sgn (bDotW b w) else 0) := by
    intro b
    by_cases hp : parity ends b = 0 <;> simp [hp]
  rw [Finset.sum_congr rfl (fun b _ => hfac b), ← Finset.mul_sum]
  ring

/-- The quadratically signed homogeneous weight enumerator over binary vectors in the kernel of
`A`, with sign determined by `B`. -/
def qwgt (A : Matrix V E (ZMod 2)) (B : Matrix E E (ZMod 2)) (x y : ℂ) : ℂ :=
  ∑ b : E → ZMod 2,
    if A.mulVec b = 0 then
      sgn (∑ e, b e * (B.mulVec b) e) * x ^ suppCard b * y ^ (Fintype.card E - suppCard b)
    else 0

/-- The diagonal binary matrix with diagonal entries given by the edge-sign vector `w`. -/
def dg (w : E → ZMod 2) : Matrix E E (ZMod 2) := Matrix.diagonal w

/-- For an incidence matrix and diagonal sign matrix, the weight enumerator at `(x, 1)` is the
signed sum of `x ^ suppCard b` over zero-parity edge vectors. -/
lemma qwgt_incidence_dg (ends : E → V × V) (w : E → ZMod 2) (x : ℂ) :
    qwgt (incidence ends) (dg w) x 1
      = ∑ b : E → ZMod 2,
          if parity ends b = 0 then sgn (bDotW b w) * x ^ suppCard b else 0 := by
  classical
  unfold qwgt dg parity
  apply Finset.sum_congr rfl
  intro b _
  have hb : ∀ e : E, b e * ((Matrix.diagonal w).mulVec b) e = b e * w e := by
    intro e
    rw [Matrix.mulVec_diagonal]
    calc b e * (w e * b e) = (b e * b e) * w e := by ring
      _ = b e * w e := by rw [mul_self]
  have hsum : (∑ e, b e * ((Matrix.diagonal w).mulVec b) e) = bDotW b w := by
    rw [bDotW]
    exact Finset.sum_congr rfl (fun e _ => hb e)
  by_cases hp : (incidence ends).mulVec b = 0
  · rw [if_pos hp, if_pos hp, hsum]
    simp
  · rw [if_neg hp, if_neg hp]

/-- Under the normalization `Θ * μ ^ card E = 1`, the partition function scaled by `μ ^ card E /
2 ^ card V` equals the signed weight enumerator, as in [Lidar, Theorem 2][Lidar2004]. -/
theorem source_theorem2_qwgt (ends : E → V × V) (hLoop : ∀ e, (ends e).1 ≠ (ends e).2)
    (w : E → ZMod 2) (Θ lam μ : ℂ) (hΘ : Θ * μ ^ Fintype.card E = 1) :
    μ ^ Fintype.card E / (2 : ℂ) ^ Fintype.card V * partition ends w Θ lam
      = qwgt (incidence ends) (dg w) lam 1 := by
  classical
  set S : ℂ := ∑ b : E → ZMod 2,
    if parity ends b = 0 then lam ^ suppCard b * sgn (bDotW b w) else 0 with hS
  rw [source_eq23_zero_parity ends hLoop w Θ lam]
  · have h2 : ((2 : ℂ) ^ Fintype.card V) ≠ 0 := pow_ne_zero _ (by norm_num)
    have hμΘ : μ ^ Fintype.card E * Θ = 1 := by
      rw [mul_comm]
      exact hΘ
    have hcalc : μ ^ Fintype.card E / (2 : ℂ) ^ Fintype.card V *
        ((2 : ℂ) ^ Fintype.card V * Θ * S) = S := by
      field_simp
      rw [mul_comm (μ ^ Fintype.card E * Θ) S, hμΘ, mul_one]
    rw [hcalc]
    rw [qwgt_incidence_dg]
    rw [hS]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hp : parity ends b = 0 <;> simp [hp, mul_comm]

omit [Fintype V] [DecidableEq V] [DecidableEq E] in

/-- Rewrites the product of the paper's edge-sign and spin factors as the product using
`edgeFactor`. -/
lemma source_boltzmann_paper_form (ends : E → V × V) (w : E → ZMod 2) (s : V → ZMod 2)
    (lam : ℂ) :
    (∏ e, (1 + sgn (w e) * (sgn (s (ends e).1) * sgn (s (ends e).2)) * lam))
      = ∏ e, (1 + edgeFactor ends w s e * lam) := by
  apply Finset.prod_congr rfl
  intro e _
  rw [← edgeFactor_eq_paper]

/-- The hyperbolic parameters satisfy `cosh (β * J)⁻² = 1 - tanh (β * J) ^ 2`, and the `nE`th
powers of `cosh (β * J)` and its inverse multiply to one. See [Lidar2004]. -/
theorem source_cosh_tanh_parameters (β J : ℝ) (nE : ℕ) :
    ((((Real.cosh (β * J))⁻¹ : ℝ) : ℂ) ^ 2 = 1 - ((Real.tanh (β * J) : ℝ) : ℂ) ^ 2) ∧
      (((Real.cosh (β * J) : ℝ) : ℂ) ^ nE *
        ((((Real.cosh (β * J))⁻¹ : ℝ) : ℂ)) ^ nE = 1) := by
  have hc : Real.cosh (β * J) ≠ 0 := (Real.cosh_pos _).ne'
  constructor
  · have hreal : (Real.cosh (β * J))⁻¹ ^ 2 = 1 - (Real.tanh (β * J)) ^ 2 := by
      rw [Real.tanh_eq_sinh_div_cosh]
      field_simp
      nlinarith [Real.cosh_sq_sub_sinh_sq (β * J)]
    rw [← Complex.ofReal_pow, hreal]
    push_cast
    ring
  · rw [← mul_pow, ← Complex.ofReal_mul, mul_inv_cancel₀ hc]
    simp

end Qatlib.Papers.IsingPart03.MainResults
