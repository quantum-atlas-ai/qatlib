/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.CbDegreeBridge.CbForms
import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm

/-!
# Matrix amplification identities for tensor forms

This module develops path expansions and coefficient extraction for the sandwich expressions of
`CbForms`. It constructs finite matrix amplifications, proves contraction bounds for their
products, and identifies the amplified sandwich with a tensor matrix substitution; the operator
norm background is described in [Paulsen2002].

## Main statements

* `cbFiberSum_full`: extract tensor coefficients from fully labelled path patterns.
* `cbNbig_prod_norm_le`: bound an amplified sandwich product of contractions by one.
* `cbAmplified`: identify the tensor substitution inner product with an amplified sandwich inner
  product.

## References

* [Paulsen, 2002][Paulsen2002]
-/

set_option warningAsError false

open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Concepts.QueryComplexity.CbDegreeBridge

open Matrix

set_option linter.unusedSectionVars false

open scoped Classical BigOperators Matrix.Norms.L2Operator

section Paths

variable {R : Type} [Fintype R] [DecidableEq R]

/-- A nonempty ordered matrix product splits into its first matrix times the product of the
remaining matrices. -/
theorem matProdFin_succ_left {k : ℕ} (M : Fin (k + 1) → Matrix R R ℂ) :
    matProdFin (k + 1) M = M 0 * matProdFin k (fun j => M j.succ) := by
  simp only [matProdFin, List.finRange_succ, List.map_cons, List.prod_cons, List.map_map,
    Function.comp_def]

/-- The equivalence between a function on `Fin 1` and its single value. -/
def fin1Equiv (R : Type) : (Fin 1 → R) ≃ R where
  toFun r := r 0
  invFun x := fun _ => x
  left_inv r := by
    funext j
    cases j using Fin.cases with
    | zero => rfl
    | succ j' => exact absurd j'.isLt (Nat.not_lt_zero _)
  right_inv _ := rfl

/-- The equivalence that prepends one value to a function indexed by `Fin k`. -/
def consEquiv {R : Type} [Fintype R] [DecidableEq R] {k : ℕ} : R × (Fin k → R) ≃ (Fin (k + 1) → R) where
  toFun p := Fin.cons (α := fun _ => R) p.1 p.2
  invFun x := (x 0, Fin.tail x)
  left_inv p := by
    obtain ⟨i, r⟩ := p
    have h1 : Fin.tail (Fin.cons (α := fun _ => R) i r) = r := by
      funext j; rfl
    exact Prod.ext rfl h1
  right_inv x := by
    funext j
    show Fin.cons (x 0) (Fin.tail x) j = x j
    cases j using Fin.cases with
    | zero => rfl
    | succ j' => rfl

/-- Expand the inner product of an ordered matrix product into a sum over all intermediate
matrix indices. -/
theorem inner_mulVec_matProdFin {k : ℕ} (M : Fin k → Matrix R R ℂ) (u v : QState R) :
    Inner u (matProdFin k M *ᵥ v) =
      ∑ r : Fin (k + 1) → R, (starRingEnd ℂ) (u (r 0)) *
        (∏ j : Fin k, M j (r j.castSucc) (r j.succ)) * v (r (Fin.last k)) := by
  induction k generalizing u v with
  | zero =>
    have h0 : matProdFin 0 M = 1 := rfl
    rw [h0, Matrix.one_mulVec]
    have heapp : ∀ r : Fin 1 → R, fin1Equiv R r = r 0 := fun _ => rfl
    rw [Fintype.sum_equiv (fin1Equiv R)
      (fun r : Fin 1 → R => (starRingEnd ℂ) (u (r 0)) *
        (∏ j : Fin 0, M j (r j.castSucc) (r j.succ)) * v (r (Fin.last 0)))
      (fun x : R => (starRingEnd ℂ) (u x) * v x)
      (fun r => by rw [heapp r]; simp)]
    rw [inner_apply]

  | succ k ih =>
    rw [matProdFin_succ_left, ← Matrix.mulVec_mulVec]
    have stepW : ∀ i' : R, (matProdFin k (fun j => M j.succ) *ᵥ v) i'
        = Inner (Ket i') (matProdFin k (fun j => M j.succ) *ᵥ v) := by
      intro i'
      rw [inner_apply, Finset.sum_eq_single i']
      · rw [ket_self, map_one, one_mul]
      · intro b _ hb; rw [Ket, if_neg hb, map_zero, zero_mul]
      · simp
    have step1 : ∀ w : QState R, Inner u (M 0 *ᵥ w)
        = ∑ i : R, ∑ i' : R, (starRingEnd ℂ) (u i) * M 0 i i' * w i' := by
      intro w
      rw [inner_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i' _ => by ring
    rw [step1 (matProdFin k (fun j => M j.succ) *ᵥ v)]
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun i' _ => by
      rw [stepW i', ih (fun j => M j.succ) (Ket i') v]))]

    have hket : ∀ (i : R) (r : Fin (k + 1) → R),
        (∑ i' : R, (starRingEnd ℂ) (u i) * M 0 i i' *
            ((starRingEnd ℂ) (Ket i' (r 0)) * (∏ j : Fin k,
              M j.succ (r j.castSucc) (r j.succ)) * v (r (Fin.last k))))
          = (starRingEnd ℂ) (u i) * M 0 i (r 0) * (∏ j : Fin k,
              M j.succ (r j.castSucc) (r j.succ)) * v (r (Fin.last k)) := by
      intro i r
      have h1 : ∀ i' : R, (starRingEnd ℂ) (u i) * M 0 i i' *
          ((starRingEnd ℂ) (Ket i' (r 0)) * (∏ j : Fin k,
            M j.succ (r j.castSucc) (r j.succ)) * v (r (Fin.last k)))
          = (starRingEnd ℂ) (u i) * ((∏ j : Fin k,
            M j.succ (r j.castSucc) (r j.succ)) * v (r (Fin.last k))) *
              (M 0 i i' * (starRingEnd ℂ) (Ket i' (r 0))) := by
        intro i'; rw [ket_apply]; ring
      rw [Finset.sum_congr rfl (fun i' _ => h1 i'), ← Finset.mul_sum]
      have h2 : ∑ i' : R, M 0 i i' * (starRingEnd ℂ) (Ket i' (r 0)) = M 0 i (r 0) := by
        rw [Finset.sum_eq_single (r 0)]
        · rw [ket_apply, if_pos rfl, map_one, mul_one]
        · intro b _ hb
          rw [ket_apply, if_neg (Ne.symm hb), map_zero, mul_zero]
        · intro h; exact absurd (Finset.mem_univ (r 0)) h
      rw [h2]; ring
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun i' _ => by rw [Finset.mul_sum]))]
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun r _ => hket i r))]
    rw [Finset.sum_comm]
    have h3 : (∑ r : Fin (k + 1) → R, ∑ i : R, (starRingEnd ℂ) (u i) * M 0 i (r 0) *
          (∏ j : Fin k, M j.succ (r j.castSucc) (r j.succ)) * v (r (Fin.last k)))
        = ∑ p : R × (Fin (k + 1) → R), (starRingEnd ℂ) (u p.1) * M 0 p.1 (p.2 0) *
          (∏ j : Fin k, M j.succ (p.2 j.castSucc) (p.2 j.succ)) * v (p.2 (Fin.last k)) := by
      rw [Finset.sum_comm]
      exact (Fintype.sum_prod_type (fun p : R × (Fin (k + 1) → R) =>
        (starRingEnd ℂ) (u p.1) * M 0 p.1 (p.2 0) *
          (∏ j : Fin k, M j.succ (p.2 j.castSucc) (p.2 j.succ)) * v (p.2 (Fin.last k)))).symm
    rw [h3]
    have h4 : ∀ (i : R) (r : Fin (k + 1) → R),
        ((starRingEnd ℂ) (u i) * M 0 i (r 0) *
            (∏ j : Fin k, M j.succ (r j.castSucc) (r j.succ))) * v (r (Fin.last k))
        = (starRingEnd ℂ) (u (Fin.cons (α := fun _ => R) i r 0)) *
            (∏ j : Fin (k + 1), M j (Fin.cons (α := fun _ => R) i r j.castSucc)
              (Fin.cons (α := fun _ => R) i r j.succ)) *
            v (Fin.cons (α := fun _ => R) i r (Fin.last (k + 1))) := by
      intro i r
      have prodEq : (∏ j : Fin (k + 1), M j (Fin.cons (α := fun _ => R) i r j.castSucc)
            (Fin.cons (α := fun _ => R) i r j.succ))
          = M 0 i (r 0) * ∏ j : Fin k, M j.succ (r j.castSucc) (r j.succ) := by
        rw [Fin.prod_univ_succ]
        have h2 : ∀ j : Fin k,
            Fin.cons (α := fun _ => R) i r ((j.succ : Fin (k + 1)).castSucc) = r j.castSucc := by
          intro j; rw [← Fin.succ_castSucc]; rfl
        have h3 : ∀ j : Fin k,
            Fin.cons (α := fun _ => R) i r ((j.succ : Fin (k + 1)).succ) = r j.succ :=
          fun _ => rfl
        rw [show Fin.cons (α := fun _ => R) i r ((0 : Fin (k + 1)).castSucc) = i from rfl,
          show Fin.cons (α := fun _ => R) i r ((0 : Fin (k + 1)).succ) = r 0 from rfl,
          Finset.prod_congr rfl (fun j _ => by rw [h2 j, h3 j])]
      have e4 : Fin.cons (α := fun _ => R) i r (Fin.last (k + 1)) = r (Fin.last k) := by
        rw [show Fin.last (k + 1) = (Fin.last k).succ from rfl]
        rfl
      show ((starRingEnd ℂ) (u i) * M 0 i (r 0) *
          (∏ j : Fin k, M j.succ (r j.castSucc) (r j.succ))) * v (r (Fin.last k))
        = (starRingEnd ℂ) (u (Fin.cons (α := fun _ => R) i r 0)) *
            (∏ j : Fin (k + 1), M j (Fin.cons (α := fun _ => R) i r j.castSucc)
              (Fin.cons (α := fun _ => R) i r j.succ)) *
            v (Fin.cons (α := fun _ => R) i r (Fin.last (k + 1)))
      rw [show Fin.cons (α := fun _ => R) i r 0 = i from rfl, prodEq, e4]
      ring
    exact Fintype.sum_equiv consEquiv
      (fun p : R × (Fin (k + 1) → R) => (starRingEnd ℂ) (u p.1) * M 0 p.1 (p.2 0) *
        (∏ j : Fin k, M j.succ (p.2 j.castSucc) (p.2 j.succ)) * v (p.2 (Fin.last k)))
      (fun x : Fin (k + 2) → R => (starRingEnd ℂ) (u (x 0)) *
        (∏ j : Fin (k + 1), M j (x j.castSucc) (x j.succ)) * v (x (Fin.last (k + 1))))
      (fun p => h4 p.1 p.2)

/-- The ordered product of a family indexed by `Fin 0` is the identity matrix. -/
theorem matProdFin_zero (M : Fin 0 → Matrix R R ℂ) : matProdFin 0 M = 1 := by
  simp [matProdFin, List.finRange_zero]

/-- A nonempty ordered matrix product splits into the product of its initial matrices times its
last matrix. -/
theorem matProdFin_succ_right {k : ℕ} (M : Fin (k + 1) → Matrix R R ℂ) :
    matProdFin (k + 1) M = matProdFin k (fun j => M j.castSucc) * M (Fin.last k) := by
  induction k with
  | zero =>
    simp only [matProdFin_succ_left, matProdFin_zero, one_mul, mul_one]
    rfl
  | succ k ih =>
    rw [matProdFin_succ_left, ih, matProdFin_succ_left, mul_assoc]
    rfl

end Paths

section Sandwich

variable {κ : Type} [Fintype κ] {R : Type} [Fintype R] [DecidableEq R] {s : ℕ}

/-- The diagonal substitution value at `r`, equal to one when `δ r` is `none` and to `w k` when
it is `some k`. -/
def dzval (δ : R → Option κ) (w : κ → ℂ) (r : R) : ℂ :=
  match δ r with | none => 1 | some k => w k

/-- Extend a complex coordinate vector to optional indices by assigning one to `none`. -/
def dzO (w : κ → ℂ) : Option κ → ℂ :=
  fun o => match o with | none => 1 | some k => w k

/-- The diagonal substitution value is the optional coordinate evaluation at the label `δ r`. -/
theorem dzval_eq_dzO (δ : R → Option κ) (w : κ → ℂ) (r : R) : dzval δ w r = dzO w (δ r) := rfl

/-- The entries of `cbDelta` are its substitution values on the diagonal and zero elsewhere. -/
theorem cbDelta_apply (δ : R → Option κ) (w : κ → ℂ) (r r' : R) :
    cbDelta δ w r r' = if r = r' then dzval δ w r else 0 := by
  rw [cbDelta, Matrix.diagonal_apply]; rfl

/-- Right multiplication by `cbDelta` multiplies each column by its diagonal substitution value. -/
theorem mul_cbDelta_apply (M : Matrix R R ℂ) (δ : R → Option κ) (w : κ → ℂ) (i j : R) :
    (M * cbDelta δ w) i j = M i j * dzval δ w j := by
  rw [cbDelta]
  exact Matrix.mul_diagonal (fun r => match δ r with | none => 1 | some k => w k) M i j

/-- The factors of the matrix sandwich product, combining each initial matrix with its
coordinate diagonal and retaining the final matrix. -/
noncomputable def cbSlot (W : Fin (s + 1) → Matrix R R ℂ) (δ : R → Option κ) (z : Fin s → κ → ℂ)
    (j : Fin (s + 1)) : Matrix R R ℂ :=
  if h : (j : ℕ) < s then W ⟨j, by omega⟩ * cbDelta δ (z ⟨j, h⟩) else W ⟨j, by omega⟩

/-- An initial slot of the sandwich product is the corresponding matrix times its coordinate
diagonal. -/
theorem cbSlot_castSucc (W : Fin (s + 1) → Matrix R R ℂ) (δ : R → Option κ) (z : Fin s → κ → ℂ)
    (j : Fin s) : cbSlot W δ z j.castSucc = W j.castSucc * cbDelta δ (z j) := by
  rw [cbSlot, dif_pos (show ((j.castSucc : Fin (s + 1)) : ℕ) < s by
    rw [Fin.val_castSucc]; exact j.isLt)]
  rfl

/-- The last slot of the sandwich product is the final matrix `W`. -/
theorem cbSlot_last (W : Fin (s + 1) → Matrix R R ℂ) (δ : R → Option κ) (z : Fin s → κ → ℂ) :
    cbSlot W δ z (Fin.last s) = W (Fin.last s) := by
  rw [cbSlot, dif_neg (by simp)]

/-- The matrix sandwich equals the ordered product of all its slots. -/
theorem cbSandwichMatrix_eq (W : Fin (s + 1) → Matrix R R ℂ) (δ : R → Option κ)
    (z : Fin s → κ → ℂ) :
    cbSandwichMatrix W δ z = matProdFin (s + 1) (cbSlot W δ z) := by
  rw [cbSandwichMatrix, matProdFin_succ_right, cbSlot_last]
  congr 1
  refine congrArg List.prod (List.map_congr_left fun j _ => ?_)
  exact (cbSlot_castSucc W δ z j).symm

/-- The coefficient of a matrix index path, formed from the conjugated initial boundary
amplitude, all matrix entries, and the final boundary amplitude. -/
def cbPathVal (W : Fin (s + 1) → Matrix R R ℂ) (u v : QState R) (r : Fin (s + 2) → R) : ℂ :=
  (starRingEnd ℂ) (u (r 0)) *
    (∏ i : Fin s, W i.castSucc (r i.castSucc.castSucc) (r i.castSucc.succ)) *
    W (Fin.last s) (r (Fin.last s).castSucc) (r (Fin.last s).succ) *
    v (r (Fin.last (s + 1)))

/-- The optional coordinate labels encountered at the internal vertices of a matrix index path. -/
def cbPattern (δ : R → Option κ) (r : Fin (s + 2) → R) : Fin s → Option κ :=
  fun j => δ (r j.castSucc.succ)

/-- Expand a matrix sandwich into a sum of path coefficients times their diagonal substitution
products. -/
theorem cbSandwich_eq_sum (W : Fin (s + 1) → Matrix R R ℂ) (δ : R → Option κ)
    (u v : QState R) (z : Fin s → κ → ℂ) :
    cbSandwich W δ u v z =
      ∑ r : Fin (s + 2) → R, cbPathVal W u v r * ∏ j, dzval δ (z j) (r j.castSucc.succ) := by
  rw [cbSandwich, cbSandwichMatrix_eq, inner_mulVec_matProdFin]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Fin.prod_univ_castSucc]
  have h1 : ∀ i : Fin s,
      cbSlot W δ z i.castSucc (r i.castSucc.castSucc) (r i.castSucc.succ)
        = W i.castSucc (r i.castSucc.castSucc) (r i.castSucc.succ)
            * dzval δ (z i) (r i.castSucc.succ) := by
    intro i
    rw [cbSlot_castSucc, mul_cbDelta_apply]
  have h2 : cbSlot W δ z (Fin.last s) (r (Fin.last s).castSucc) (r (Fin.last s).succ)
      = W (Fin.last s) (r (Fin.last s).castSucc) (r (Fin.last s).succ) := by
    rw [cbSlot_last]
  rw [Finset.prod_congr rfl (fun i _ => h1 i), h2, Finset.prod_mul_distrib]
  simp only [dzval_eq_dzO]
  unfold cbPathVal
  ring

/-- Regroup a finite weighted sum by the fibers of a pattern map. -/
theorem sum_pattern_distrib {X P : Type} [Fintype X] [Fintype P] [DecidableEq P]
    (pat : X → P) (c : X → ℂ) (g : P → ℂ) :
    ∑ x, c x * g (pat x)
      = ∑ p, (∑ x, (if pat x = p then (1 : ℂ) else 0) * c x) * g p := by
  have step1 : ∀ p : P, (∑ x : X, (if pat x = p then (1 : ℂ) else 0) * c x) * g p
      = ∑ x : X, (if pat x = p then c x else 0) * g p := by
    intro p
    calc (∑ x : X, (if pat x = p then (1 : ℂ) else 0) * c x) * g p
        = ∑ x : X, ((if pat x = p then (1 : ℂ) else 0) * c x) * g p :=
          Finset.sum_mul Finset.univ (fun x : X => (if pat x = p then (1 : ℂ) else 0) * c x) (g p)
      _ = ∑ x : X, (if pat x = p then c x else 0) * g p :=
          Finset.sum_congr rfl (fun x _ => by
            by_cases hx : pat x = p
            · rw [if_pos hx, if_pos hx, one_mul]
            · rw [if_neg hx, if_neg hx, zero_mul])
  rw [Finset.sum_congr rfl (fun p _ => step1 p), Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_congr rfl (fun p _ => by rw [ite_mul, zero_mul]), Finset.sum_ite_eq,
    if_pos (Finset.mem_univ _)]

/-- The sum of matrix path coefficients whose optional label pattern equals `p`. -/
noncomputable def cbFiberSum (W : Fin (s + 1) → Matrix R R ℂ) (δ : R → Option κ) (u v : QState R)
    (p : Fin s → Option κ) : ℂ :=
  ∑ r : Fin (s + 2) → R, (if cbPattern δ r = p then (1 : ℂ) else 0) * cbPathVal W u v r

/-- A matrix sandwich is the sum over optional label patterns of their fiber coefficients times
their coordinate products. -/
theorem cbSandwich_eq_fiber (W : Fin (s + 1) → Matrix R R ℂ) (δ : R → Option κ)
    (u v : QState R) (z : Fin s → κ → ℂ) :
    cbSandwich W δ u v z = ∑ p : Fin s → Option κ,
      cbFiberSum W δ u v p * ∏ j, dzO (z j) (p j) := by
  rw [cbSandwich_eq_sum]
  have hconv : ∀ r : Fin (s + 2) → R,
      cbPathVal W u v r * ∏ j, dzval δ (z j) (r j.castSucc.succ)
        = cbPathVal W u v r * (fun p => ∏ j, dzO (z j) (p j)) (cbPattern δ r) := by
    intro r
    exact congrArg (cbPathVal W u v r * ·) (Finset.prod_congr rfl fun j _ => rfl)
  rw [Finset.sum_congr rfl (fun r _ => hconv r),
    sum_pattern_distrib (cbPattern δ) (cbPathVal W u v)
      (fun p => ∏ j, dzO (z j) (p j))]
  rfl

/-- If a linear combination of the optional coordinate monomials vanishes for every complex
substitution, every coefficient is zero. -/
theorem mono_indep {s : ℕ} (g : (Fin s → Option κ) → ℂ)
    (h : ∀ z : Fin s → κ → ℂ, ∑ p, g p * ∏ j, dzO (z j) (p j) = 0) :
    ∀ p, g p = 0 := by
  induction s with
  | zero =>
    intro p
    have hp : p = fun j => isEmptyElim j := Subsingleton.elim _ _
    subst hp
    simpa using! h (fun j => isEmptyElim j)
  | succ s ih =>
    have hsplit : ∀ (w : κ → ℂ) (z' : Fin s → κ → ℂ),
        ∑ q : Option κ, ∑ p' : Fin s → Option κ,
            g (Fin.cons (α := fun _ => Option κ) q p') *
              (dzO w q * ∏ j, dzO (z' j) (p' j)) = 0 := by
      intro w z'
      have hz := h (Fin.cons (α := fun _ => κ → ℂ) w z')
      have hconv : (∑ p : Fin (s + 1) → Option κ,
            g p * ∏ j, dzO (Fin.cons (α := fun _ => κ → ℂ) w z' j) (p j))
          = ∑ pp : Option κ × (Fin s → Option κ),
              g (Fin.cons (α := fun _ => Option κ) pp.1 pp.2) *
                (dzO w pp.1 * ∏ j, dzO (z' j) (pp.2 j)) :=
        (Fintype.sum_equiv consEquiv
          (fun pp : Option κ × (Fin s → Option κ) =>
            g (Fin.cons (α := fun _ => Option κ) pp.1 pp.2) *
              (dzO w pp.1 * ∏ j, dzO (z' j) (pp.2 j)))
          (fun p : Fin (s + 1) → Option κ =>
            g p * ∏ j, dzO (Fin.cons (α := fun _ => κ → ℂ) w z' j) (p j))
          (fun pp => by
            obtain ⟨q, p'⟩ := pp
            show g (Fin.cons (α := fun _ => Option κ) q p') * (dzO w q *
                ∏ j, dzO (z' j) (p' j))
                = g (Fin.cons (α := fun _ => Option κ) q p') *
                  ∏ j, dzO (Fin.cons (α := fun _ => κ → ℂ) w z' j)
                    (Fin.cons (α := fun _ => Option κ) q p' j)
            rw [Fin.prod_univ_succ]
            simp [Fin.cons_zero, Fin.cons_succ])).symm
      rw [hconv, Fintype.sum_prod_type] at hz
      exact hz
    have hgw : ∀ (w : κ → ℂ) (p' : Fin s → Option κ),
        ∑ q : Option κ, g (Fin.cons (α := fun _ => Option κ) q p') * dzO w q = 0 := by
      intro w p'
      refine ih (fun p' => ∑ q, g (Fin.cons (α := fun _ => Option κ) q p') * dzO w q) ?_ p'
      intro z'
      calc ∑ p', (∑ q, g (Fin.cons (α := fun _ => Option κ) q p') * dzO w q) *
            ∏ j, dzO (z' j) (p' j)
          = ∑ p', ∑ q, g (Fin.cons (α := fun _ => Option κ) q p') *
              (dzO w q * ∏ j, dzO (z' j) (p' j)) :=
            Finset.sum_congr rfl (fun p' _ => by
              rw [Finset.sum_mul]
              exact Finset.sum_congr rfl (fun q _ => by ring))
        _ = ∑ q, ∑ p', g (Fin.cons (α := fun _ => Option κ) q p') *
              (dzO w q * ∏ j, dzO (z' j) (p' j)) := Finset.sum_comm
        _ = 0 := hsplit w z'
    intro p
    have hp : p = Fin.cons (α := fun _ => Option κ) (p 0) (Fin.tail p) :=
      (Fin.cons_self_tail p).symm
    have e0 : ∀ p' : Fin s → Option κ,
        g (Fin.cons (α := fun _ => Option κ) none p') = 0 := by
      intro p'
      have h1 := hgw (fun _ => 0) p'
      rw [Fintype.sum_option] at h1
      simp only [dzO, mul_zero, Finset.sum_const, nsmul_eq_mul, mul_one, add_zero] at h1
      exact h1
    cases hq : p 0 with
    | none => rw [hp, hq]; exact e0 _
    | some k =>
      rw [hp, hq]
      have h1 := hgw (fun k' => if k' = k then (1 : ℂ) else 0) (Fin.tail p)
      rw [Fintype.sum_option] at h1
      rw [e0] at h1
      rw [Finset.sum_eq_single k] at h1
      · simp only [dzO] at h1
        simp at h1
        exact h1
      · intro b _ hb
        simp only [dzO]
        rw [if_neg hb, mul_zero]
      · intro hmem
        exact absurd (Finset.mem_univ k) hmem

/-- When a sandwich represents a tensor evaluation, the fiber coefficient of a fully labelled
pattern is the corresponding tensor coefficient. -/
theorem cbFiberSum_full {T : RealTensor κ s} {W : Fin (s + 1) → Matrix R R ℂ}
    {δ : R → Option κ} {u v : QState R}
    (hcert : ∀ z : Fin s → κ → ℂ, tensorEval T z = cbSandwich W δ u v z) :
    ∀ i : Fin s → κ, cbFiberSum W δ u v (fun j => some (i j)) = (T i : ℂ) := by
  classical
  have hvanish : ∀ z : Fin s → κ → ℂ,
      ∑ p : Fin s → Option κ,
        (cbFiberSum W δ u v p - ∑ i : Fin s → κ,
          (if (fun j => some (i j)) = p then (1 : ℂ) else 0) * (T i : ℂ)) *
        ∏ j, dzO (z j) (p j) = 0 := by
    intro z
    have h1 := cbSandwich_eq_fiber W δ u v z
    have h2 : ∑ p : Fin s → Option κ,
        (∑ i : Fin s → κ, (if (fun j => some (i j)) = p then (1 : ℂ) else 0) * (T i : ℂ)) *
        ∏ j, dzO (z j) (p j) = tensorEval T z := by
      rw [← sum_pattern_distrib (fun i : Fin s → κ => fun j => some (i j))
        (fun i => (T i : ℂ)) (fun p => ∏ j, dzO (z j) (p j))]
      simp [tensorEval, dzO]
    have hsplit : (∑ p : Fin s → Option κ, (cbFiberSum W δ u v p -
          ∑ i : Fin s → κ, (if (fun j => some (i j)) = p then (1 : ℂ) else 0) * (T i : ℂ)) *
        ∏ j, dzO (z j) (p j))
        = (∑ p : Fin s → Option κ, cbFiberSum W δ u v p * ∏ j, dzO (z j) (p j)) -
          (∑ p : Fin s → Option κ,
            (∑ i : Fin s → κ, (if (fun j => some (i j)) = p then (1 : ℂ) else 0) * (T i : ℂ)) *
            ∏ j, dzO (z j) (p j)) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun p _ => by ring
    rw [hsplit, ← h1, h2, hcert z]
    ring
  have hall := mono_indep (fun p => cbFiberSum W δ u v p - ∑ i : Fin s → κ,
    (if (fun j => some (i j)) = p then (1 : ℂ) else 0) * (T i : ℂ)) hvanish
  intro i
  have h : cbFiberSum W δ u v (fun j => some (i j)) -
      ∑ i' : Fin s → κ,
        (if (fun j => some (i' j)) = (fun j => some (i j)) then (1 : ℂ) else 0) *
        (T i' : ℂ) = 0 := hall (fun j => some (i j))
  rw [Finset.sum_eq_single i] at h
  · rw [if_pos rfl, one_mul] at h
    exact sub_eq_zero.mp h
  · intro b _ hb
    rw [if_neg (fun hbe => hb (by
          funext j
          exact Option.some.inj (congrFun hbe j))), zero_mul]
  · intro hmem; exact absurd (Finset.mem_univ i) hmem

/-- When a sandwich represents a tensor evaluation, every pattern containing an unlabelled slot
has zero fiber coefficient. -/
theorem cbFiberSum_partial {T : RealTensor κ s} {W : Fin (s + 1) → Matrix R R ℂ}
    {δ : R → Option κ} {u v : QState R}
    (hcert : ∀ z : Fin s → κ → ℂ, tensorEval T z = cbSandwich W δ u v z)
    (p : Fin s → Option κ) (j : Fin s) (hj : p j = none) :
    cbFiberSum W δ u v p = 0 := by
  classical
  have hvanish : ∀ z : Fin s → κ → ℂ,
      ∑ p : Fin s → Option κ,
        (cbFiberSum W δ u v p - ∑ i : Fin s → κ,
          (if (fun j => some (i j)) = p then (1 : ℂ) else 0) * (T i : ℂ)) *
        ∏ j, dzO (z j) (p j) = 0 := by
    intro z
    have h1 := cbSandwich_eq_fiber W δ u v z
    have h2 : ∑ p : Fin s → Option κ,
        (∑ i : Fin s → κ, (if (fun j => some (i j)) = p then (1 : ℂ) else 0) * (T i : ℂ)) *
        ∏ j, dzO (z j) (p j) = tensorEval T z := by
      rw [← sum_pattern_distrib (fun i : Fin s → κ => fun j => some (i j))
        (fun i => (T i : ℂ)) (fun p => ∏ j, dzO (z j) (p j))]
      simp [tensorEval, dzO]
    have hsplit : (∑ p : Fin s → Option κ, (cbFiberSum W δ u v p -
          ∑ i : Fin s → κ, (if (fun j => some (i j)) = p then (1 : ℂ) else 0) * (T i : ℂ)) *
        ∏ j, dzO (z j) (p j))
        = (∑ p : Fin s → Option κ, cbFiberSum W δ u v p * ∏ j, dzO (z j) (p j)) -
          (∑ p : Fin s → Option κ,
            (∑ i : Fin s → κ, (if (fun j => some (i j)) = p then (1 : ℂ) else 0) * (T i : ℂ)) *
            ∏ j, dzO (z j) (p j)) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun p _ => by ring
    rw [hsplit, ← h1, h2, hcert z]
    ring
  have hall := mono_indep (fun p => cbFiberSum W δ u v p - ∑ i : Fin s → κ,
    (if (fun j => some (i j)) = p then (1 : ℂ) else 0) * (T i : ℂ)) hvanish
  have h : cbFiberSum W δ u v p -
      ∑ i : Fin s → κ,
        (if (fun j => some (i j)) = p then (1 : ℂ) else 0) * (T i : ℂ) = 0 := hall p
  have hzero : ∑ i : Fin s → κ,
      (if (fun j => some (i j)) = p then (1 : ℂ) else 0) * (T i : ℂ) = 0 := by
    have hfalse : ∀ i : Fin s → κ, ¬ ((fun j => some (i j)) = p) := by
      intro i hbe
      have hcc := congrFun hbe j
      rw [hj] at hcc
      exact absurd hcc (by simp)
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [if_neg (hfalse i), zero_mul]
  rw [hzero, sub_zero] at h
  exact h

end Sandwich

section Norms

variable {m : Type} [Fintype m] [DecidableEq m]

/-- Squaring preserves an inequality between nonnegative real numbers. -/
theorem sq_le_sq_nn {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ≤ b) : a ^ 2 ≤ b ^ 2 :=
  sq_le_sq.mpr (by rwa [abs_of_nonneg ha, abs_of_nonneg hb])

/-- The Euclidean operator norm of the identity matrix is at most one. -/
theorem l2_opNorm_one_le : ‖(1 : Matrix m m ℂ)‖ ≤ 1 := by
  refine l2_opNorm_le_of_mulVec_le zero_le_one _ fun v => ?_
  rw [Matrix.one_mulVec, one_mul]

/-- The Euclidean operator norm of an ordered matrix product is at most the product of the
factor norms. -/
theorem l2_opNorm_matProdFin_le {k : ℕ} (M : Fin k → Matrix m m ℂ) :
    ‖matProdFin k M‖ ≤ ∏ j, ‖M j‖ := by
  induction k with
  | zero =>
    rw [matProdFin_zero]
    have h1 : (∏ j : Fin 0, ‖M j‖) = 1 := by simp
    rw [h1]
    exact l2_opNorm_one_le
  | succ k ih =>
    have hM : M = Fin.cons (α := fun _ => Matrix m m ℂ) (M 0) (Fin.tail M) :=
      (Fin.cons_self_tail M).symm
    rw [hM]
    have htail : (fun j : Fin k =>
        (Fin.cons (α := fun _ => Matrix m m ℂ) (M 0) (Fin.tail M)) j.succ) = Fin.tail M := by
      funext j; rfl
    rw [matProdFin_succ_left, Fin.prod_univ_succ, htail]
    refine le_trans (l2_opNorm_mul _ _) ?_
    exact mul_le_mul (le_refl _) (ih (Fin.tail M)) (norm_nonneg _) (norm_nonneg _)

/-- The inner product is additive over a finite sum in its second argument. -/
theorem inner_sum_right {ι : Type} [Fintype ι] (ξ : QState m) (w : ι → QState m) :
    Inner ξ (∑ i, w i) = ∑ i, Inner ξ (w i) := by
  rw [inner_apply]
  simp only [Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => (inner_apply ξ (w i)).symm

/-- Matrix application distributes over a finite sum of matrices. -/
theorem mulVec_sum_left {ι : Type} [Fintype ι] (M : ι → Matrix m m ℂ) (η : QState m) :
    (∑ i, M i) *ᵥ η = ∑ i, (M i *ᵥ η) :=
  Matrix.sum_mulVec Finset.univ M η

end Norms

section Amplified

variable {κ : Type} [Fintype κ] {R : Type} [Fintype R] [DecidableEq R] {s : ℕ}

/-- The matrix acting as `M` on the `R` coordinate and as the identity on the finite
amplification coordinate. -/
def cbBigW {d : ℕ} (M : Matrix R R ℂ) : Matrix (R × Fin d) (R × Fin d) ℂ :=
  Matrix.kroneckerMap (· * ·) M (1 : Matrix (Fin d) (Fin d) ℂ)

/-- The entry of `cbBigW M` is the corresponding entry of `M` when amplification coordinates
agree, and zero otherwise. -/
theorem cbBigW_apply {d : ℕ} (M : Matrix R R ℂ) (x y : R × Fin d) :
    cbBigW M x y = if x.2 = y.2 then M x.1 y.1 else 0 := by
  simp [cbBigW, Matrix.one_apply]

/-- Amplifying a matrix by a finite identity factor does not increase its Euclidean operator
norm. -/
theorem cbBigW_norm_le {d : ℕ} {M : Matrix R R ℂ} : ‖cbBigW (d := d) M‖ ≤ ‖M‖ := by
  refine le_trans (l2_norm_kronecker_le M (1 : Matrix (Fin d) (Fin d) ℂ)) ?_
  calc ‖M‖ * ‖(1 : Matrix (Fin d) (Fin d) ℂ)‖ ≤ ‖M‖ * 1 :=
        mul_le_mul_of_nonneg_left l2_opNorm_one_le (norm_nonneg _)
    _ = ‖M‖ := mul_one _

/-- The matrix selected by the optional label of `r`, with the zero matrix assigned to `none`. -/
def cbBlock {d : ℕ} (δ : R → Option κ) (Bj : κ → Matrix (Fin d) (Fin d) ℂ) (r : R) :
    Matrix (Fin d) (Fin d) ℂ :=
  match δ r with | none => 0 | some k => Bj k

/-- The block diagonal matrix whose block at `r` is the coordinate matrix selected by `δ r` for
slot `j`. -/
def cbBigD {d : ℕ} (δ : R → Option κ) (B : Fin s → κ → Matrix (Fin d) (Fin d) ℂ) (j : Fin s) :
    Matrix (R × Fin d) (R × Fin d) ℂ :=
  Matrix.of fun x y => if x.1 = y.1 then cbBlock δ (B j) x.1 x.2 y.2 else 0

/-- Applying `cbBigD` to a vector acts independently on each `R` slice by the selected block. -/
theorem cbBigD_mulVec_apply {d : ℕ} (δ : R → Option κ)
    (B : Fin s → κ → Matrix (Fin d) (Fin d) ℂ) (j : Fin s)
    (z : QState (R × Fin d)) (x : R × Fin d) :
    (cbBigD δ B j *ᵥ z) x = (cbBlock δ (B j) x.1 *ᵥ (fun a => z (x.1, a))) x.2 := by
  simp only [Matrix.mulVec, dotProduct, cbBigD, Matrix.of_apply]
  rw [Fintype.sum_prod_type]
  have h1 : ∀ q : R, ∑ b : Fin d,
      (if x.1 = q then cbBlock δ (B j) x.1 x.2 b else 0) * z (q, b)
      = (if x.1 = q then ∑ b : Fin d, cbBlock δ (B j) x.1 x.2 b * z (q, b) else 0) := by
    intro q
    by_cases hq : x.1 = q
    · rw [if_pos hq]
      exact Finset.sum_congr rfl (fun b _ => by rw [if_pos hq])
    · simp [hq]
  rw [Finset.sum_congr rfl (fun q _ => h1 q), Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]

/-- If all coordinate matrices in a slot are contractions, the corresponding block diagonal
matrix has operator norm at most one. -/
theorem cbBigD_norm_le {d : ℕ} (δ : R → Option κ)
    (B : Fin s → κ → Matrix (Fin d) (Fin d) ℂ) (j : Fin s) (hB : ∀ k, ‖B j k‖ ≤ 1) :
    ‖cbBigD δ B j‖ ≤ 1 := by
  have hblock : ∀ r : R, ‖cbBlock δ (B j) r‖ ≤ 1 := by
    intro r; cases hr : δ r with
    | none => simp only [cbBlock, hr]; exact norm_zero.trans_le zero_le_one
    | some k => rw [cbBlock, hr]; exact hB k
  refine l2_opNorm_le_of_mulVec_le zero_le_one _ fun z => ?_
  have hsq : ‖toEuclidean_fromVec (cbBigD δ B j *ᵥ z)‖ ^ 2
      ≤ (1 * ‖toEuclidean_fromVec z‖) ^ 2 := by
    have hsplit : ‖toEuclidean_fromVec (cbBigD δ B j *ᵥ z)‖ ^ 2
        = ∑ r : R, ∑ a : Fin d, ‖(cbBigD δ B j *ᵥ z) (r, a)‖ ^ 2 := by
      rw [norm_toEuclidean_fromVec_sq, Fintype.sum_prod_type]
    rw [hsplit]
    have hle : ∀ r : R, ∑ a : Fin d, ‖(cbBigD δ B j *ᵥ z) (r, a)‖ ^ 2
        ≤ ∑ a : Fin d, ‖z (r, a)‖ ^ 2 := by
      intro r
      have h1 := l2_norm_mulVec_fromVec_le (cbBlock δ (B j) r) (fun a => z (r, a))
      have hconv : ∀ a : Fin d, ‖(cbBigD δ B j *ᵥ z) (r, a)‖ ^ 2
          = ‖(cbBlock δ (B j) r *ᵥ (fun a => z (r, a))) a‖ ^ 2 :=
        fun a => by rw [cbBigD_mulVec_apply δ B j z (r, a)]
      rw [Finset.sum_congr rfl (fun a _ => hconv a), ← norm_toEuclidean_fromVec_sq]
      calc ‖toEuclidean_fromVec (cbBlock δ (B j) r *ᵥ (fun a => z (r, a)))‖ ^ 2
          ≤ (‖cbBlock δ (B j) r‖ * ‖toEuclidean_fromVec (fun a => z (r, a))‖) ^ 2 :=
            sq_le_sq_nn (norm_nonneg _)
              (mul_nonneg (norm_nonneg _) (norm_nonneg _)) h1
        _ ≤ (1 * ‖toEuclidean_fromVec (fun a => z (r, a))‖) ^ 2 := by
            refine sq_le_sq_nn (mul_nonneg (norm_nonneg _) (norm_nonneg _))
              (mul_nonneg zero_le_one (norm_nonneg _)) ?_
            exact mul_le_mul_of_nonneg_right (hblock r) (norm_nonneg _)
        _ = ∑ a : Fin d, ‖z (r, a)‖ ^ 2 := by rw [one_mul, norm_toEuclidean_fromVec_sq]
    calc ∑ r : R, ∑ a : Fin d, ‖(cbBigD δ B j *ᵥ z) (r, a)‖ ^ 2
        ≤ ∑ r : R, ∑ a : Fin d, ‖z (r, a)‖ ^ 2 := Finset.sum_le_sum (fun r _ => hle r)
      _ = ‖toEuclidean_fromVec z‖ ^ 2 := by
            rw [norm_toEuclidean_fromVec_sq]
            exact (Fintype.sum_prod_type (fun x : R × Fin d => ‖z x‖ ^ 2)).symm
      _ ≤ (1 * ‖toEuclidean_fromVec z‖) ^ 2 := by rw [one_mul]
  calc ‖toEuclidean_fromVec (cbBigD δ B j *ᵥ z)‖
      = Real.sqrt (‖toEuclidean_fromVec (cbBigD δ B j *ᵥ z)‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((1 * ‖toEuclidean_fromVec z‖) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = 1 * ‖toEuclidean_fromVec z‖ := by rw [Real.sqrt_sq (mul_nonneg zero_le_one (norm_nonneg _))]

/-- The entries of an amplified matrix followed by a block diagonal substitution factor as the
original matrix entry times the selected block entry. -/
theorem cbBigW_mul_cbBigD_apply {d : ℕ} (M : Matrix R R ℂ) (δ : R → Option κ)
    (B : Fin s → κ → Matrix (Fin d) (Fin d) ℂ) (j : Fin s) (x y : R × Fin d) :
    (cbBigW (d := d) M * cbBigD δ B j) x y = M x.1 y.1 * cbBlock δ (B j) y.1 x.2 y.2 := by
  simp only [Matrix.mul_apply, cbBigW_apply, cbBigD, Matrix.of_apply,
    Fintype.sum_prod_type]
  have h1 : ∀ q : R, ∑ b : Fin d,
      (if x.2 = b then M x.1 q else 0) *
        (if q = y.1 then cbBlock δ (B j) q b y.2 else 0)
      = (if q = y.1 then M x.1 q * cbBlock δ (B j) q x.2 y.2 else 0) := by
    intro q
    rw [Finset.sum_congr rfl (fun b _ => by rw [ite_mul, zero_mul]), Finset.sum_ite_eq,
      if_pos (Finset.mem_univ x.2)]
    by_cases hq : q = y.1
    · rw [if_pos hq, if_pos hq]
    · simp [hq]
  rw [Finset.sum_congr rfl (fun q _ => h1 q), Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]

/-- The block selected by an unlabelled index is zero. -/
theorem cbBlock_none {d : ℕ} (δ : R → Option κ) (Bj : κ → Matrix (Fin d) (Fin d) ℂ)
    {r : R} (h : δ r = none) : cbBlock δ Bj r = 0 := by
  rw [cbBlock, h]

/-- The block at an index labelled by `some k` is the coordinate matrix `Bj k`. -/
theorem cbBlock_some {d : ℕ} (δ : R → Option κ) (Bj : κ → Matrix (Fin d) (Fin d) ℂ)
    {r : R} {k : κ} (h : δ r = some k) : cbBlock δ Bj r = Bj k := by
  rw [cbBlock, h]

/-- The factors of the amplified sandwich product, using amplified matrices and block diagonal
coordinate substitutions. -/
noncomputable def cbNbig {d : ℕ} (W : Fin (s + 1) → Matrix R R ℂ) (δ : R → Option κ)
    (B : Fin s → κ → Matrix (Fin d) (Fin d) ℂ) (j : Fin (s + 1)) :
    Matrix (R × Fin d) (R × Fin d) ℂ :=
  if h : (j : ℕ) < s then cbBigW (W ⟨j, by omega⟩) * cbBigD δ B ⟨j, h⟩
  else cbBigW (W ⟨j, by omega⟩)

/-- An initial amplified sandwich factor has entries equal to a matrix entry times the
appropriate coordinate block entry. -/
theorem cbNbig_castSucc {d : ℕ} (W : Fin (s + 1) → Matrix R R ℂ) (δ : R → Option κ)
    (B : Fin s → κ → Matrix (Fin d) (Fin d) ℂ) (j : Fin s) (x y : R × Fin d) :
    cbNbig W δ B j.castSucc x y = W j.castSucc x.1 y.1 * cbBlock δ (B j) y.1 x.2 y.2 := by
  rw [cbNbig, dif_pos (show ((j.castSucc : Fin (s + 1)) : ℕ) < s by
    rw [Fin.val_castSucc]; exact j.isLt)]
  exact cbBigW_mul_cbBigD_apply (W j.castSucc) δ B j x y

/-- The final amplified sandwich factor has entries of the last matrix when amplification
coordinates agree and zero otherwise. -/
theorem cbNbig_last {d : ℕ} (W : Fin (s + 1) → Matrix R R ℂ) (δ : R → Option κ)
    (B : Fin s → κ → Matrix (Fin d) (Fin d) ℂ) (x y : R × Fin d) :
    cbNbig W δ B (Fin.last s) x y = if x.2 = y.2 then W (Fin.last s) x.1 y.1 else 0 := by
  rw [cbNbig, dif_neg (by simp), cbBigW_apply]

/-- If every matrix and coordinate substitution is a contraction, each amplified sandwich factor
has operator norm at most one. -/
theorem cbNbig_norm_le {d : ℕ} (W : Fin (s + 1) → Matrix R R ℂ) (δ : R → Option κ)
    (B : Fin s → κ → Matrix (Fin d) (Fin d) ℂ)
    (hW : ∀ j, ‖W j‖ ≤ 1) (hB : ∀ j k, ‖B j k‖ ≤ 1) (j : Fin (s + 1)) :
    ‖cbNbig W δ B j‖ ≤ 1 := by
  by_cases hj : (j : ℕ) < s
  · rw [cbNbig, dif_pos hj]
    calc ‖cbBigW (W ⟨j, by omega⟩) * cbBigD δ B ⟨j, hj⟩‖
        ≤ ‖cbBigW (W ⟨j, by omega⟩)‖ * ‖cbBigD δ B ⟨j, hj⟩‖ := l2_opNorm_mul _ _
      _ ≤ ‖W ⟨j, by omega⟩‖ * 1 := by
          refine mul_le_mul cbBigW_norm_le (cbBigD_norm_le δ B ⟨j, hj⟩ fun k => hB _ k)
            (norm_nonneg _) (norm_nonneg _)
      _ = ‖W ⟨j, by omega⟩‖ := mul_one _
      _ ≤ 1 := hW _
  · rw [cbNbig, dif_neg hj]
    calc ‖cbBigW (W ⟨j, by omega⟩)‖ ≤ ‖W ⟨j, by omega⟩‖ := cbBigW_norm_le
      _ ≤ 1 := hW _

/-- If all matrices and coordinate substitutions are contractions, their amplified sandwich
product has operator norm at most one. -/
theorem cbNbig_prod_norm_le {d : ℕ} (W : Fin (s + 1) → Matrix R R ℂ) (δ : R → Option κ)
    (B : Fin s → κ → Matrix (Fin d) (Fin d) ℂ)
    (hW : ∀ j, ‖W j‖ ≤ 1) (hB : ∀ j k, ‖B j k‖ ≤ 1) :
    ‖matProdFin (s + 1) (cbNbig W δ B)‖ ≤ 1 := by
  refine le_trans (l2_opNorm_matProdFin_le (cbNbig W δ B)) ?_
  calc (∏ j : Fin (s + 1), ‖cbNbig W δ B j‖)
      ≤ (∏ j : Fin (s + 1), (1 : ℝ)) :=
        Finset.prod_le_prod₀ (fun j _ => norm_nonneg _)
          (fun j _ => cbNbig_norm_le W δ B hW hB j)
    _ = 1 := by simp

end Amplified

/-- The inner product with a scalar multiple in its second argument equals that scalar times the
inner product. -/
theorem inner_smul_right {m : Type} [Fintype m] [DecidableEq m]
    (ξ : QState m) (c : ℂ) (w : QState m) :
    Inner ξ (c • w) = c * Inner ξ w := by
  rw [inner_apply, inner_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- The equivalence that appends one value to a function indexed by `Fin k`. -/
def snocEquiv {k d : ℕ} : (Fin k → Fin d) × Fin d ≃ (Fin (k + 1) → Fin d) where
  toFun p := Fin.snoc p.1 p.2
  invFun a := (Fin.init a, a (Fin.last k))
  left_inv p := Prod.ext (Fin.init_snoc (α := fun _ => Fin d) p.2 p.1)
    (Fin.snoc_last (α := fun _ => Fin d) p.2 p.1)
  right_inv a := Fin.snoc_init_self a

/-- A sum restricted to paths whose final two coordinates coincide reduces to a sum over shorter
paths with the final coordinate repeated. -/
theorem sum_snoc_collapse {k d : ℕ} (F : (Fin (k + 2) → Fin d) → ℂ) :
    ∑ a : Fin (k + 2) → Fin d,
        (if a (Fin.last k).castSucc = a (Fin.last (k + 1)) then (1 : ℂ) else 0) * F a
      = ∑ a' : Fin (k + 1) → Fin d, F (Fin.snoc a' (a' (Fin.last k))) := by
  have h1 : ∑ a : Fin (k + 2) → Fin d,
        (if a (Fin.last k).castSucc = a (Fin.last (k + 1)) then (1 : ℂ) else 0) * F a
      = ∑ p : (Fin (k + 1) → Fin d) × Fin d,
          (if p.1 (Fin.last k) = p.2 then (1 : ℂ) else 0) * F (Fin.snoc p.1 p.2) :=
    (Fintype.sum_equiv snocEquiv
      (fun p : (Fin (k + 1) → Fin d) × Fin d =>
        (if p.1 (Fin.last k) = p.2 then (1 : ℂ) else 0) * F (Fin.snoc p.1 p.2))
      (fun a : Fin (k + 2) → Fin d =>
        (if a (Fin.last k).castSucc = a (Fin.last (k + 1)) then (1 : ℂ) else 0) * F a)
      (fun p => by
        obtain ⟨a', c⟩ := p
        show (if a' (Fin.last k) = c then (1 : ℂ) else 0) * F (Fin.snoc (α := fun _ => Fin d) a' c)
            = (if (Fin.snoc (α := fun _ => Fin d) a' c) (Fin.last k).castSucc
                  = (Fin.snoc (α := fun _ => Fin d) a' c) (Fin.last (k + 1))
                then (1 : ℂ) else 0) * F (Fin.snoc (α := fun _ => Fin d) a' c)
        rw [show (Fin.snoc (α := fun _ => Fin d) a' c) (Fin.last k).castSucc = a' (Fin.last k) from
              Fin.snoc_castSucc (α := fun i => Fin d) c a' (Fin.last k),
          show (Fin.snoc (α := fun _ => Fin d) a' c) (Fin.last (k + 1)) = c from
              Fin.snoc_last (α := fun i => Fin d) c a'])).symm
  rw [h1, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a' _ => ?_
  show ∑ y : Fin d, (if a' (Fin.last k) = y then (1 : ℂ) else 0) *
      F (Fin.snoc (α := fun _ => Fin d) a' y)
      = F (Fin.snoc (α := fun _ => Fin d) a' (a' (Fin.last k)))
  rw [Finset.sum_eq_single (a' (Fin.last k))]
  · rw [if_pos rfl, one_mul]
  · intro b _ hb
    rw [if_neg (Ne.symm hb), zero_mul]
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

/-- The equivalence between a pair of finite indexed functions and the function of their
pointwise pairs. -/
def piProdEquiv {X Y : Type} (k : ℕ) : ((Fin k → X) × (Fin k → Y)) ≃ (Fin k → X × Y) where
  toFun p := fun i => (p.1 i, p.2 i)
  invFun f := (fun i => (f i).1, fun i => (f i).2)
  left_inv p := by
    obtain ⟨r, a⟩ := p
    exact Prod.ext (funext fun i => rfl) (funext fun i => rfl)
  right_inv f := by
    funext i
    exact Prod.ext rfl rfl

section AmplifiedIdentity

variable {κ : Type} [Fintype κ] {R : Type} [Fintype R] [DecidableEq R] {s : ℕ}

set_option maxHeartbeats 1000000 in

/-- If the fully labelled fiber coefficients equal the tensor coefficients, the inner product of
any matrix substitution equals the corresponding amplified sandwich inner product on product
boundary vectors. -/
theorem cbAmplified {d : ℕ} (W : Fin (s + 1) → Matrix R R ℂ) (δ : R → Option κ)
    (u v : QState R) (T : RealTensor κ s)
    (hT : ∀ i : Fin s → κ, cbFiberSum W δ u v (fun j => some (i j)) = (T i : ℂ))
    (B : Fin s → κ → Matrix (Fin d) (Fin d) ℂ) (ξ η : Fin d → ℂ) :
    Inner ξ ((∑ i : Fin s → κ, (T i : ℂ) • matProdFin s (fun j => B j (i j))) *ᵥ η)
      = Inner (fun x : R × Fin d => u x.1 * ξ x.2)
          ((matProdFin (s + 1) (cbNbig W δ B)) *ᵥ (fun x : R × Fin d => v x.1 * η x.2)) := by
  classical

  have hL : Inner ξ ((∑ i : Fin s → κ, (T i : ℂ) • matProdFin s (fun j => B j (i j))) *ᵥ η)
      = ∑ i : Fin s → κ, cbFiberSum W δ u v (fun j => some (i j)) *
          (∑ a : Fin (s + 1) → Fin d, (starRingEnd ℂ) (ξ (a 0)) *
            (∏ j : Fin s, B j (i j) (a j.castSucc) (a j.succ)) * η (a (Fin.last s))) := by
    rw [mulVec_sum_left, inner_sum_right]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.smul_mulVec, inner_smul_right, inner_mulVec_matProdFin, ← hT i]

  have hR2 : Inner (fun x : R × Fin d => u x.1 * ξ x.2)
          ((matProdFin (s + 1) (cbNbig W δ B)) *ᵥ (fun x : R × Fin d => v x.1 * η x.2))
      = ∑ p : (Fin (s + 2) → R) × (Fin (s + 2) → Fin d),
          (starRingEnd ℂ) (u (p.1 0) * ξ (p.2 0)) *
          (∏ j : Fin (s + 1),
            cbNbig W δ B j (p.1 j.castSucc, p.2 j.castSucc) (p.1 j.succ, p.2 j.succ)) *
          (v (p.1 (Fin.last (s + 1))) * η (p.2 (Fin.last (s + 1)))) := by
    rw [inner_mulVec_matProdFin]
    exact (Fintype.sum_equiv (piProdEquiv (X := R) (Y := Fin d) (s + 2))
      (fun p : (Fin (s + 2) → R) × (Fin (s + 2) → Fin d) =>
        (starRingEnd ℂ) (u (p.1 0) * ξ (p.2 0)) *
        (∏ j : Fin (s + 1),
          cbNbig W δ B j (p.1 j.castSucc, p.2 j.castSucc) (p.1 j.succ, p.2 j.succ)) *
        (v (p.1 (Fin.last (s + 1))) * η (p.2 (Fin.last (s + 1)))))
      (fun x : Fin (s + 2) → R × Fin d =>
        (starRingEnd ℂ) ((fun y : R × Fin d => u y.1 * ξ y.2) (x 0)) *
        (∏ j : Fin (s + 1), cbNbig W δ B j (x j.castSucc) (x j.succ)) *
        (fun y : R × Fin d => v y.1 * η y.2) (x (Fin.last (s + 1))))
      (fun p => rfl)).symm

  have hR3 : (∑ p : (Fin (s + 2) → R) × (Fin (s + 2) → Fin d),
          (starRingEnd ℂ) (u (p.1 0) * ξ (p.2 0)) *
          (∏ j : Fin (s + 1),
            cbNbig W δ B j (p.1 j.castSucc, p.2 j.castSucc) (p.1 j.succ, p.2 j.succ)) *
          (v (p.1 (Fin.last (s + 1))) * η (p.2 (Fin.last (s + 1)))))
      = ∑ r : Fin (s + 2) → R, ∑ a : Fin (s + 2) → Fin d,
          (starRingEnd ℂ) (u (r 0) * ξ (a 0)) *
          (∏ j : Fin (s + 1), cbNbig W δ B j (r j.castSucc, a j.castSucc) (r j.succ, a j.succ)) *
          (v (r (Fin.last (s + 1))) * η (a (Fin.last (s + 1)))) :=
    Fintype.sum_prod_type _

  have hProd : ∀ (r : Fin (s + 2) → R) (a : Fin (s + 2) → Fin d),
      (∏ j : Fin (s + 1), cbNbig W δ B j (r j.castSucc, a j.castSucc) (r j.succ, a j.succ))
      = (∏ j : Fin s, W j.castSucc (r j.castSucc.castSucc) (r j.castSucc.succ) *
            cbBlock δ (B j) (r j.castSucc.succ) (a j.castSucc.castSucc) (a j.castSucc.succ)) *
          (if a (Fin.last s).castSucc = a (Fin.last (s + 1)) then
            W (Fin.last s) (r (Fin.last s).castSucc) (r (Fin.last (s + 1))) else 0) := by
    intro r a
    rw [Fin.prod_univ_castSucc]
    have hWj : ∀ j : Fin s, cbNbig W δ B j.castSucc
          (r j.castSucc.castSucc, a j.castSucc.castSucc) (r j.castSucc.succ, a j.castSucc.succ)
        = W j.castSucc (r j.castSucc.castSucc) (r j.castSucc.succ) *
            cbBlock δ (B j) (r j.castSucc.succ) (a j.castSucc.castSucc) (a j.castSucc.succ) := by
      intro j
      rw [cbNbig_castSucc]
    have hLast : cbNbig W δ B (Fin.last s)
          (r (Fin.last s).castSucc, a (Fin.last s).castSucc) (r (Fin.last s).succ, a (Fin.last s).succ)
        = if a (Fin.last s).castSucc = a (Fin.last (s + 1)) then
            W (Fin.last s) (r (Fin.last s).castSucc) (r (Fin.last (s + 1))) else 0 := by
      rw [cbNbig_last, show (Fin.last s).succ = Fin.last (s + 1) from rfl]
    rw [Finset.prod_congr rfl (fun j _ => hWj j), hLast]

  have hMark : ∀ (r : Fin (s + 2) → R) (a : Fin (s + 2) → Fin d),
      (starRingEnd ℂ) (u (r 0) * ξ (a 0)) *
          (∏ j : Fin (s + 1), cbNbig W δ B j (r j.castSucc, a j.castSucc) (r j.succ, a j.succ)) *
          (v (r (Fin.last (s + 1))) * η (a (Fin.last (s + 1))))
      = (if a (Fin.last s).castSucc = a (Fin.last (s + 1)) then (1 : ℂ) else 0) *
          ((starRingEnd ℂ) (u (r 0)) * (starRingEnd ℂ) (ξ (a 0)) *
            ((∏ j : Fin s, W j.castSucc (r j.castSucc.castSucc) (r j.castSucc.succ) *
                cbBlock δ (B j) (r j.castSucc.succ) (a j.castSucc.castSucc) (a j.castSucc.succ)) *
              W (Fin.last s) (r (Fin.last s).castSucc) (r (Fin.last (s + 1)))) *
            (v (r (Fin.last (s + 1))) * η (a (Fin.last (s + 1))))) := by
    intro r a
    rw [map_mul, hProd r a]
    by_cases hc : a (Fin.last s).castSucc = a (Fin.last (s + 1))
    · rw [if_pos hc, if_pos hc]; ring
    · rw [if_neg hc, if_neg hc]; ring

  have hSnoc : ∀ (r : Fin (s + 2) → R),
      (∑ a : Fin (s + 2) → Fin d,
          (if a (Fin.last s).castSucc = a (Fin.last (s + 1)) then (1 : ℂ) else 0) *
            ((starRingEnd ℂ) (u (r 0)) * (starRingEnd ℂ) (ξ (a 0)) *
              ((∏ j : Fin s, W j.castSucc (r j.castSucc.castSucc) (r j.castSucc.succ) *
                  cbBlock δ (B j) (r j.castSucc.succ) (a j.castSucc.castSucc) (a j.castSucc.succ)) *
                W (Fin.last s) (r (Fin.last s).castSucc) (r (Fin.last (s + 1)))) *
              (v (r (Fin.last (s + 1))) * η (a (Fin.last (s + 1))))))
      = ∑ a' : Fin (s + 1) → Fin d,
          (starRingEnd ℂ) (u (r 0)) * (starRingEnd ℂ) (ξ (a' 0)) *
            ((∏ j : Fin s, W j.castSucc (r j.castSucc.castSucc) (r j.castSucc.succ) *
                cbBlock δ (B j) (r j.castSucc.succ) (a' j.castSucc) (a' j.succ)) *
              W (Fin.last s) (r (Fin.last s).castSucc) (r (Fin.last (s + 1)))) *
            (v (r (Fin.last (s + 1))) * η (a' (Fin.last s))) := by
    intro r
    rw [sum_snoc_collapse (F := fun a =>
          (starRingEnd ℂ) (u (r 0)) * (starRingEnd ℂ) (ξ (a 0)) *
            ((∏ j : Fin s, W j.castSucc (r j.castSucc.castSucc) (r j.castSucc.succ) *
                cbBlock δ (B j) (r j.castSucc.succ) (a j.castSucc.castSucc) (a j.castSucc.succ)) *
              W (Fin.last s) (r (Fin.last s).castSucc) (r (Fin.last (s + 1)))) *
            (v (r (Fin.last (s + 1))) * η (a (Fin.last (s + 1)))))]
    refine Finset.sum_congr rfl fun a' _ => ?_
    have e0 : (Fin.snoc (α := fun _ => Fin d) a' (a' (Fin.last s))) 0 = a' 0 :=
      Fin.snoc_apply_zero (α := fun _ => Fin d) _ a'
    have eC : ∀ j : Fin s,
        (Fin.snoc (α := fun _ => Fin d) a' (a' (Fin.last s))) j.castSucc.castSucc = a' j.castSucc :=
      fun j => Fin.snoc_castSucc (α := fun i => Fin d) _ a' j.castSucc
    have eS : ∀ j : Fin s,
        (Fin.snoc (α := fun _ => Fin d) a' (a' (Fin.last s))) j.castSucc.succ = a' j.succ :=
      fun j => Fin.snoc_castSucc (α := fun i => Fin d) _ a' j.succ
    have eL : (Fin.snoc (α := fun _ => Fin d) a' (a' (Fin.last s))) (Fin.last (s + 1))
        = a' (Fin.last s) :=
      Fin.snoc_last (α := fun i => Fin d) _ a'
    have hpc : (∏ j : Fin s, W j.castSucc (r j.castSucc.castSucc) (r j.castSucc.succ) *
            cbBlock δ (B j) (r j.castSucc.succ)
              ((Fin.snoc (α := fun _ => Fin d) a' (a' (Fin.last s))) j.castSucc.castSucc)
              ((Fin.snoc (α := fun _ => Fin d) a' (a' (Fin.last s))) j.castSucc.succ))
        = (∏ j : Fin s, W j.castSucc (r j.castSucc.castSucc) (r j.castSucc.succ) *
            cbBlock δ (B j) (r j.castSucc.succ) (a' j.castSucc) (a' j.succ)) :=
      Finset.prod_congr rfl fun j _ => by rw [eC j, eS j]
    rw [e0, hpc, eL]

  have hPath : ∀ (r : Fin (s + 2) → R) (a' : Fin (s + 1) → Fin d),
      (starRingEnd ℂ) (u (r 0)) * (starRingEnd ℂ) (ξ (a' 0)) *
          ((∏ j : Fin s, W j.castSucc (r j.castSucc.castSucc) (r j.castSucc.succ) *
              cbBlock δ (B j) (r j.castSucc.succ) (a' j.castSucc) (a' j.succ)) *
            W (Fin.last s) (r (Fin.last s).castSucc) (r (Fin.last (s + 1)))) *
          (v (r (Fin.last (s + 1))) * η (a' (Fin.last s)))
      = cbPathVal W u v r *
          ((starRingEnd ℂ) (ξ (a' 0)) *
            (∏ j : Fin s, cbBlock δ (B j) (r j.castSucc.succ) (a' j.castSucc) (a' j.succ)) *
            η (a' (Fin.last s))) := by
    intro r a'
    rw [Finset.prod_mul_distrib]
    unfold cbPathVal
    rw [show Fin.last (s + 1) = (Fin.last s).succ from rfl]
    ring

  have hPat : ∀ (r : Fin (s + 2) → R) (a' : Fin (s + 1) → Fin d),
      cbPathVal W u v r *
          ((starRingEnd ℂ) (ξ (a' 0)) *
            (∏ j : Fin s, cbBlock δ (B j) (r j.castSucc.succ) (a' j.castSucc) (a' j.succ)) *
            η (a' (Fin.last s)))
      = (∑ i : Fin s → κ, (if cbPattern δ r = (fun j => some (i j)) then (1 : ℂ) else 0)) *
          (cbPathVal W u v r *
            ((starRingEnd ℂ) (ξ (a' 0)) *
              (∏ j : Fin s, cbBlock δ (B j) (r j.castSucc.succ) (a' j.castSucc) (a' j.succ)) *
              η (a' (Fin.last s)))) := by
    intro r a'
    by_cases hall : ∀ j : Fin s, δ (r j.castSucc.succ) ≠ none
    · have hsum :
          (∑ i : Fin s → κ, (if cbPattern δ r = (fun j => some (i j)) then (1 : ℂ) else 0))
            = 1 := by
        have hget : ∀ j : Fin s, (δ (r j.castSucc.succ)).isSome :=
          fun j => Option.isSome_iff_ne_none.mpr (hall j)
        have hpat : cbPattern δ r
            = fun j => some ((δ (r j.castSucc.succ)).get (hget j)) := by
          funext j
          exact (Option.some_get _).symm
        rw [Finset.sum_eq_single (fun j => (δ (r j.castSucc.succ)).get (hget j))]
        · show (if cbPattern δ r = (fun j => some ((δ (r j.castSucc.succ)).get (hget j)))
              then (1 : ℂ) else 0) = 1
          rw [if_pos hpat]
        · intro b _ hne
          show (if cbPattern δ r = (fun j => some (b j)) then (1 : ℂ) else 0) = 0
          refine if_neg (fun hbe => hne ?_)
          funext j
          have h1 : δ (r j.castSucc.succ) = some (b j) := congrFun hbe j
          rw [← Option.some_get (hget j)] at h1
          exact (Option.some.inj h1).symm
        · intro hmem
          exact absurd (Finset.mem_univ _) hmem
      rw [hsum, one_mul]
    · obtain ⟨j₀, hj₀⟩ : ∃ j₀ : Fin s, δ (r j₀.castSucc.succ) = none := by
        by_contra hcon
        exact hall (fun j hj => hcon ⟨j, hj⟩)
      have hz : cbBlock δ (B j₀) (r j₀.castSucc.succ) (a' j₀.castSucc) (a' j₀.succ) = 0 :=
        congrFun (congrFun (cbBlock_none δ (B j₀) hj₀) (a' j₀.castSucc)) (a' j₀.succ)
      rw [Finset.prod_eq_zero (Finset.mem_univ j₀) hz]
      ring

  have hIB : ∀ (i : Fin s → κ) (a' : Fin (s + 1) → Fin d) (r : Fin (s + 2) → R),
      (if cbPattern δ r = (fun j => some (i j)) then (1 : ℂ) else 0) *
          (cbPathVal W u v r *
            ((starRingEnd ℂ) (ξ (a' 0)) *
              (∏ j : Fin s, cbBlock δ (B j) (r j.castSucc.succ) (a' j.castSucc) (a' j.succ)) *
              η (a' (Fin.last s))))
      = (if cbPattern δ r = (fun j => some (i j)) then (1 : ℂ) else 0) *
          (cbPathVal W u v r *
            ((starRingEnd ℂ) (ξ (a' 0)) *
              (∏ j : Fin s, B j (i j) (a' j.castSucc) (a' j.succ)) * η (a' (Fin.last s)))) := by
    intro i a' r
    by_cases hc : cbPattern δ r = (fun j => some (i j))
    · rw [if_pos hc]
      have hdelta : ∀ j : Fin s, δ (r j.castSucc.succ) = some (i j) := fun j => congrFun hc j
      have hpeq : (∏ j : Fin s, cbBlock δ (B j) (r j.castSucc.succ) (a' j.castSucc) (a' j.succ))
          = (∏ j : Fin s, B j (i j) (a' j.castSucc) (a' j.succ)) :=
        Finset.prod_congr rfl fun j _ => by rw [cbBlock_some δ (B j) (hdelta j)]
      rw [hpeq]
    · rw [if_neg hc, zero_mul, zero_mul]

  have hFac : ∀ (i : Fin s → κ) (a' : Fin (s + 1) → Fin d),
      (∑ r : Fin (s + 2) → R,
          (if cbPattern δ r = (fun j => some (i j)) then (1 : ℂ) else 0) *
            (cbPathVal W u v r *
              ((starRingEnd ℂ) (ξ (a' 0)) *
                (∏ j : Fin s, cbBlock δ (B j) (r j.castSucc.succ) (a' j.castSucc) (a' j.succ)) *
                η (a' (Fin.last s)))))
      = cbFiberSum W δ u v (fun j => some (i j)) *
          ((starRingEnd ℂ) (ξ (a' 0)) *
            (∏ j : Fin s, B j (i j) (a' j.castSucc) (a' j.succ)) * η (a' (Fin.last s))) := by
    intro i a'
    have hstep : ∀ r : Fin (s + 2) → R,
        (if cbPattern δ r = (fun j => some (i j)) then (1 : ℂ) else 0) *
            (cbPathVal W u v r *
              ((starRingEnd ℂ) (ξ (a' 0)) *
                (∏ j : Fin s, cbBlock δ (B j) (r j.castSucc.succ) (a' j.castSucc) (a' j.succ)) *
                η (a' (Fin.last s))))
        = ((if cbPattern δ r = (fun j => some (i j)) then (1 : ℂ) else 0) *
              cbPathVal W u v r) *
            ((starRingEnd ℂ) (ξ (a' 0)) *
              (∏ j : Fin s, B j (i j) (a' j.castSucc) (a' j.succ)) * η (a' (Fin.last s))) := by
      intro r
      rw [hIB i a' r]
      ring
    rw [Finset.sum_congr rfl fun r _ => hstep r, ← Finset.sum_mul]
    rfl

  have hDist : ∀ (a' : Fin (s + 1) → Fin d) (r : Fin (s + 2) → R),
      (∑ i : Fin s → κ, (if cbPattern δ r = (fun j => some (i j)) then (1 : ℂ) else 0)) *
          (cbPathVal W u v r *
            ((starRingEnd ℂ) (ξ (a' 0)) *
              (∏ j : Fin s, cbBlock δ (B j) (r j.castSucc.succ) (a' j.castSucc) (a' j.succ)) *
              η (a' (Fin.last s))))
      = ∑ i : Fin s → κ, (if cbPattern δ r = (fun j => some (i j)) then (1 : ℂ) else 0) *
          (cbPathVal W u v r *
            ((starRingEnd ℂ) (ξ (a' 0)) *
              (∏ j : Fin s, cbBlock δ (B j) (r j.castSucc.succ) (a' j.castSucc) (a' j.succ)) *
              η (a' (Fin.last s)))) := by
    intro a' r
    rw [Finset.sum_mul]

  have hR : Inner (fun x : R × Fin d => u x.1 * ξ x.2)
          ((matProdFin (s + 1) (cbNbig W δ B)) *ᵥ (fun x : R × Fin d => v x.1 * η x.2))
      = ∑ i : Fin s → κ, cbFiberSum W δ u v (fun j => some (i j)) *
          (∑ a : Fin (s + 1) → Fin d, (starRingEnd ℂ) (ξ (a 0)) *
            (∏ j : Fin s, B j (i j) (a j.castSucc) (a j.succ)) * η (a (Fin.last s))) := by
    rw [hR2, hR3]
    rw [Finset.sum_congr rfl fun r _ =>
      (Finset.sum_congr rfl fun a _ => hMark r a).trans (hSnoc r)]
    rw [Finset.sum_congr rfl fun r _ =>
      Finset.sum_congr rfl fun a' _ => (hPath r a').trans (hPat r a')]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun r _ => hDist a' r]
    rw [Finset.sum_congr rfl fun a' _ => Finset.sum_comm]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a' _ => hFac i a']
    exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm

  exact hL.trans hR.symm

end AmplifiedIdentity

end Qatlib.Concepts.QueryComplexity.CbDegreeBridge
