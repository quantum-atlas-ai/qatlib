/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.NonUnitalHom
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Hom
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.IsEmpty.Defs
import Mathlib.Basic.Logic.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Qatlib.Papers.LinearDiseq07.MainResults.CarryPolynomial

/-!
# Polynomial representation of digits of sums

`pdigit`, `partSum`, and `carry` describe digit extraction and the successive carries in finite
natural sums. The polynomial constructions `carryAtPoly` and `stepSubst` encode one digit step,
while substitution lemmas control evaluation and degree. For prime `p`,
`source_lemma5_digit_polynomials` constructs polynomials for all digits of a sum modulo `p ^ k`
with the stated degree bounds. See [Ivanyos2008] for the paper context.

## Main statements

* `carry_sum_eq`: For positive `p`, the quotient by `p` of the sum of all entry residues equals
  the sum of the successive carry indicators.
* `totalDegree_bind₁_le`: Substituting polynomials of total degree at most `B` into `φ` gives
  total degree at most `B * φ.totalDegree`.
* `source_lemma5_digit_polynomials`: For prime `p`, the digits of any sum modulo `p ^ k` are
  represented by polynomials in the input digits, with the polynomial for position `i` having
  total degree at most `(2 * p - 2) ^ i`.

## References

* [Ivanyos, 2008][Ivanyos2008]
-/

set_option autoImplicit false

noncomputable section

open Finset
open scoped BigOperators

namespace Qatlib.Papers.LinearDiseq07.MainResults

open MvPolynomial

section Numeric

/-- The natural quotient-and-remainder expression `x / p ^ i % p` for the digit at position `i`. -/
def pdigit (p x i : ℕ) : ℕ := x / p ^ i % p

/-- The sum of the entries of `A` with indices strictly smaller than `t`. -/
def partSum {T : ℕ} (A : Fin T → ℕ) (t : Fin T) : ℕ :=
  ∑ i : Fin t.val, A ⟨i.val, lt_trans i.isLt t.isLt⟩

/-- The zero-or-one carry indicator for adding the current entry's residue to the preceding
partial sum's residue modulo `p`. -/
def carry (p : ℕ) {T : ℕ} (A : Fin T → ℕ) (t : Fin T) : ℕ :=
  if partSum A t % p + A t % p < p then 0 else 1

/-- If `p > 0` and `r < 2 * p`, then `r / p` is zero below `p` and one otherwise. -/
lemma div_eq_zero_or_one {p r : ℕ} (hp : 0 < p) (hr : r < 2 * p) :
    r / p = if r < p then 0 else 1 := by
  by_cases h : r < p
  · rw [if_pos h, Nat.div_eq_of_lt h]
  · rw [if_neg h]
    have hge : p ≤ r := by omega
    have hlt : r / p < 2 := (Nat.div_lt_iff_lt_mul hp).mpr (by omega)
    have hle : 1 ≤ r / p := (Nat.one_le_div_iff hp).mpr hge
    omega

/-- For positive `p`, dividing `S + A` by `p` gives the sum of the individual quotients plus the
carry from adding their residues. -/
lemma add_div_carry {p S A : ℕ} (hp : 0 < p) :
    (S + A) / p = S / p + A / p + (if S % p + A % p < p then 0 else 1) := by
  have hSA : S + A = p * (S / p + A / p) + (S % p + A % p) := by
    calc S + A = (p * (S / p) + S % p) + (p * (A / p) + A % p) := by
          rw [Nat.div_add_mod S p, Nat.div_add_mod A p]
      _ = p * (S / p + A / p) + (S % p + A % p) := by ring
  have hr : S % p + A % p < 2 * p := by
    have := Nat.mod_lt S hp
    have := Nat.mod_lt A hp
    omega
  rw [hSA, Nat.mul_add_div hp]
  congr 1
  exact div_eq_zero_or_one hp hr

/-- If `p > 0` and `s < p`, reducing `p * X + s` modulo `p ^ (k + 1)` and dividing by `p` gives
`X % p ^ k`. -/
lemma low_digit_shift {p k X s : ℕ} (hp : 0 < p) (hs : s < p) :
    (p * X + s) % p ^ (k + 1) / p = X % p ^ k := by
  have hpk : 0 < p ^ k := pow_pos hp k
  have hr : X % p ^ k < p ^ k := Nat.mod_lt _ hpk
  have hsplit : p * X + s = p ^ (k + 1) * (X / p ^ k) + (p * (X % p ^ k) + s) := by
    calc p * X + s = p * (p ^ k * (X / p ^ k) + X % p ^ k) + s := by
          conv_lhs => rw [show X = p ^ k * (X / p ^ k) + X % p ^ k from
            (Nat.div_add_mod X (p ^ k)).symm]
      _ = p ^ (k + 1) * (X / p ^ k) + (p * (X % p ^ k) + s) := by
          rw [pow_succ']
          ring
  have hsmall : p * (X % p ^ k) + s < p ^ (k + 1) := by
    have hr1 : X % p ^ k + 1 ≤ p ^ k := hr
    have hle : p * (X % p ^ k) + p ≤ p * p ^ k := by
      calc p * (X % p ^ k) + p = p * (X % p ^ k + 1) := by ring
        _ ≤ p * p ^ k := Nat.mul_le_mul_left p hr1
    have hlt : p * (X % p ^ k) + s < p * (X % p ^ k) + p := by omega
    calc p * (X % p ^ k) + s < p * (X % p ^ k) + p := hlt
      _ ≤ p * p ^ k := hle
      _ = p ^ (k + 1) := by rw [pow_succ']
  have hmod : (p * X + s) % p ^ (k + 1) = p * (X % p ^ k) + s := by
    rw [hsplit, Nat.mul_add_mod, Nat.mod_eq_of_lt hsmall]
  rw [hmod, show p * (X % p ^ k) + s = s + (X % p ^ k) * p by ring,
    Nat.add_mul_div_right s (X % p ^ k) hp, Nat.div_eq_of_lt hs, Nat.zero_add]

/-- Reducing a finite sum modulo `p` is unchanged by first reducing every summand modulo `p`. -/
lemma sum_mod_eq {α : Type*} (s : Finset α) (f : α → ℕ) (p : ℕ) :
    (∑ x ∈ s, f x) % p = (∑ x ∈ s, f x % p) % p :=
  Nat.ModEq.sum (fun x _ => (Nat.mod_modEq (f x) p).symm)

/-- A partial sum before a nonfinal index is unchanged by restricting a family on `Fin (T + 1)`
to its first `T` entries. -/
lemma partSum_castSucc {T : ℕ} (A : Fin (T+1) → ℕ) (t : Fin T) :
    partSum A (Fin.castSucc t) = partSum (fun s => A (Fin.castSucc s)) t := by
  unfold partSum
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1

/-- The partial sum before the last index of `Fin (T + 1)` is the sum of its first `T` entries. -/
lemma partSum_last {T : ℕ} (A : Fin (T+1) → ℕ) :
    partSum A (Fin.last T) = ∑ s : Fin T, A (Fin.castSucc s) := by
  unfold partSum
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1

/-- For positive `p`, the quotient by `p` of the sum of all entry residues equals the sum of the
successive carry indicators [Ivanyos, Lemma 5][Ivanyos2008]. -/
lemma carry_sum_eq {p : ℕ} (hp : 0 < p) {T : ℕ} (A : Fin T → ℕ) :
    (∑ t : Fin T, A t % p) / p = ∑ t : Fin T, carry p A t := by
  induction T with
  | zero => simp [carry]
  | succ T ih =>
      have hsplit : (∑ t : Fin (T+1), A t % p)
          = (∑ s : Fin T, A s.castSucc % p) + A (Fin.last T) % p := by
        rw [Fin.sum_univ_castSucc]
      have hlast : carry p A (Fin.last T)
          = if (∑ s : Fin T, A s.castSucc % p) % p + (A (Fin.last T) % p) % p < p
              then 0 else 1 := by
        unfold carry
        rw [partSum_last, sum_mod_eq, Nat.mod_mod]
      have hc : (∑ t : Fin T, carry p (fun s => A s.castSucc) t)
          = ∑ i : Fin T, carry p A i.castSucc := by
        refine Finset.sum_congr rfl fun t _ => ?_
        unfold carry
        rw [partSum_castSucc]
      rw [hsplit, add_div_carry hp, Fin.sum_univ_castSucc,
        ih (fun s => A s.castSucc), Nat.div_eq_of_lt (Nat.mod_lt _ hp), Nat.add_zero,
        hlast, hc]

end Numeric

/-- Substituting polynomials of total degree at most `B` into `φ` gives total degree at most `B
* φ.totalDegree` [Ivanyos, Lemma 5][Ivanyos2008]. -/
theorem totalDegree_bind₁_le {σ τ R : Type*} [CommSemiring R]
    (f : σ → MvPolynomial τ R) (φ : MvPolynomial σ R) (B : ℕ)
    (hf : ∀ i, (f i).totalDegree ≤ B) :
    (MvPolynomial.bind₁ f φ).totalDegree ≤ B * φ.totalDegree := by
  have hsum : MvPolynomial.bind₁ f φ
      = ∑ v ∈ φ.support, C (φ.coeff v) * ∏ i ∈ v.support, f i ^ v i := by
    conv_lhs => rw [MvPolynomial.as_sum φ]
    rw [map_sum]
    exact Finset.sum_congr rfl fun v _ => MvPolynomial.bind₁_monomial f v _
  rw [hsum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro v hv
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  have hC : (C (φ.coeff v) : MvPolynomial τ R).totalDegree = 0 := MvPolynomial.totalDegree_C _
  have hprod : (∏ i ∈ v.support, f i ^ v i).totalDegree ≤ B * (v.sum fun x e => e) := by
    refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
    have hterm : ∀ i ∈ v.support, (f i ^ v i).totalDegree ≤ B * v i := by
      intro i _
      refine (MvPolynomial.totalDegree_pow _ _).trans ?_
      calc v i * (f i).totalDegree ≤ v i * B := Nat.mul_le_mul_left _ (hf i)
        _ = B * v i := Nat.mul_comm _ _
    calc (∑ i ∈ v.support, (f i ^ v i).totalDegree) ≤ ∑ i ∈ v.support, B * v i :=
          Finset.sum_le_sum hterm
      _ = B * (∑ i ∈ v.support, v i) := by rw [Finset.mul_sum]
      _ = B * (v.sum fun x e => e) := by rfl
  rw [hC, Nat.zero_add]
  exact hprod.trans (Nat.mul_le_mul_left B (MvPolynomial.le_totalDegree hv))

/-- Evaluating a polynomial after substitution equals evaluating it at the values of the
substituted polynomials. -/
theorem eval_bind₁ {σ τ R : Type*} [CommSemiring R]
    (f : σ → MvPolynomial τ R) (g : τ → R) (φ : MvPolynomial σ R) :
    MvPolynomial.eval g (MvPolynomial.bind₁ f φ)
      = MvPolynomial.eval (fun i => MvPolynomial.eval g (f i)) φ :=
  MvPolynomial.eval₂Hom_bind₁ (RingHom.id R) g f φ

/-- The assignment of each entry-position pair to the corresponding base-`p` digit of `b`,
viewed in `ZMod p`. -/
def digitEval (p : ℕ) {T k : ℕ} (b : Fin T → ℕ) : Fin T × Fin k → ZMod p :=
  fun z => ((b z.1 / p ^ z.2.val) % p : ℕ)

/-- The sum of the variables representing the lowest digits of all `T` entries. -/
def lowDigitPoly (p T k : ℕ) : MvPolynomial (Fin T × Fin (k + 1)) (ZMod p) :=
  ∑ t : Fin T, X (t, (0 : Fin (k + 1)))

/-- The sum of the lowest-digit variables with entry index strictly smaller than `t`. -/
def partsumPoly (p : ℕ) {T k : ℕ} (t : Fin T) :
    MvPolynomial (Fin T × Fin (k + 1)) (ZMod p) :=
  ∑ i : Fin t.val, X (⟨i.val, lt_trans i.isLt t.isLt⟩, (0 : Fin (k + 1)))

/-- The carry polynomial with its inputs replaced by the preceding lowest-digit partial sum and
the current lowest-digit variable. -/
def carryAtPoly (p : ℕ) {T k : ℕ} (t : Fin T) :
    MvPolynomial (Fin T × Fin (k + 1)) (ZMod p) :=
  MvPolynomial.bind₁ (fun s : Fin 2 =>
    if s = 0 then partsumPoly p t else X (t, (0 : Fin (k + 1)))) (carryPoly p)

/-- The digit-step substitution using shifted digit variables for the first `T` entries and
lowest-position carry polynomials, with higher positions zero, for the second `T` entries. -/
def stepSubst (p : ℕ) (T k : ℕ) :
    Fin (T + T) × Fin k → MvPolynomial (Fin T × Fin (k + 1)) (ZMod p) :=
  fun z => Fin.addCases
    (fun t => X (t, Fin.succ z.2))
    (fun t => if z.2.val = 0 then carryAtPoly p t else 0)
    z.1

section Lemma5

variable {p : ℕ} [hp : Fact p.Prime]

/-- Every successive carry indicator is at most one. -/
lemma carry_le_one (p : ℕ) {T : ℕ} (A : Fin T → ℕ) (t : Fin T) :
    carry p A t ≤ 1 := by
  unfold carry
  split_ifs <;> omega

/-- Summing the initial entries after casting to `ZMod p` equals casting their natural partial
sum. -/
lemma sum_zmod_digit {T : ℕ} (b : Fin T → ℕ) (t : Fin T) :
    (∑ i : Fin t.val, ((b ⟨i.val, lt_trans i.isLt t.isLt⟩ : ℕ) : ZMod p))
      = ((partSum b t : ℕ) : ZMod p) := by
  rw [show partSum b t = ∑ i : Fin t.val, b ⟨i.val, lt_trans i.isLt t.isLt⟩ from rfl,
    Nat.cast_sum]

/-- Evaluating the partial-sum polynomial at the digit assignment gives the preceding natural
partial sum modulo `p`, cast to `ZMod p`. -/
lemma eval_partsumPoly {T k : ℕ} (b : Fin T → ℕ) (t : Fin T) :
    MvPolynomial.eval (digitEval (k := k + 1) p b) (partsumPoly (k := k) p t)
      = ((partSum b t % p : ℕ) : ZMod p) := by
  unfold partsumPoly
  rw [map_sum]
  have hterm : ∀ i : Fin t.val, MvPolynomial.eval (digitEval p b)
      (X (⟨i.val, lt_trans i.isLt t.isLt⟩, (0 : Fin (k + 1))))
        = ((b ⟨i.val, lt_trans i.isLt t.isLt⟩ : ℕ) : ZMod p) := by
    intro i
    rw [MvPolynomial.eval_X]
    show (((b ⟨i.val, lt_trans i.isLt t.isLt⟩ / p ^ (0 : Fin (k + 1)).val) % p : ℕ)
        : ZMod p) = ((b ⟨i.val, lt_trans i.isLt t.isLt⟩ : ℕ) : ZMod p)
    simp only [Fin.val_zero, pow_zero, Nat.div_one, ZMod.natCast_mod]
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  rw [ZMod.natCast_mod]
  exact sum_zmod_digit b t

/-- For prime `p`, evaluating the local carry polynomial at the digit assignment gives the
natural carry indicator cast to `ZMod p` [Ivanyos, Lemma 5][Ivanyos2008]. -/
lemma eval_carryAtPoly {T k : ℕ} (b : Fin T → ℕ) (t : Fin T) :
    MvPolynomial.eval (digitEval (k := k + 1) p b) (carryAtPoly (k := k) p t)
      = ((carry p b t : ℕ) : ZMod p) := by
  unfold carryAtPoly
  rw [eval_bind₁]
  have hpoint : (fun s : Fin 2 => MvPolynomial.eval (digitEval p b)
        (if s = 0 then partsumPoly p t else X (t, (0 : Fin (k + 1)))))
      = ![((partSum b t % p : ℕ) : ZMod p), ((b t % p : ℕ) : ZMod p)] := by
    funext s
    fin_cases s
    · simp only [Fin.mk_zero, if_true, eval_partsumPoly, Matrix.cons_val_zero]
    · have h10 : (1 : Fin 2) ≠ 0 := by decide
      simp only [Fin.mk_one, h10, if_false, Matrix.cons_val_one]
      rw [MvPolynomial.eval_X]
      show (((b t / p ^ (0 : Fin (k + 1)).val) % p : ℕ) : ZMod p)
          = ((b t % p : ℕ) : ZMod p)
      simp only [Fin.val_zero, pow_zero, Nat.div_one]
  rw [hpoint]
  have ha : partSum b t % p < p := Nat.mod_lt _ hp.out.pos
  have hb : b t % p < p := Nat.mod_lt _ hp.out.pos
  rw [carryPoly_eval (p := p) (partSum b t % p) (b t % p) ha hb]
  unfold carry
  by_cases h : partSum b t % p + b t % p < p
  · rw [if_pos h, if_pos h]
    norm_num
  · rw [if_neg h, if_neg h]
    norm_num

/-- For prime `p`, every local carry polynomial has total degree at most `2 * p - 2`. -/
lemma totalDegree_carryAtPoly {T k : ℕ} (t : Fin T) :
    (carryAtPoly (p := p) (k := k) t).totalDegree ≤ 2 * p - 2 := by
  unfold carryAtPoly
  have hf : ∀ s : Fin 2,
      ((if s = 0 then partsumPoly (p := p) (k := k) t
        else X (t, (0 : Fin (k + 1))))).totalDegree ≤ 1 := by
    intro s
    by_cases hs : s = 0
    · rw [if_pos hs]
      unfold partsumPoly
      apply MvPolynomial.totalDegree_finsetSum_le
      intro i _
      rw [MvPolynomial.totalDegree_X]
    · rw [if_neg hs, MvPolynomial.totalDegree_X]
  calc (MvPolynomial.bind₁ (fun s : Fin 2 =>
          if s = 0 then partsumPoly (p := p) (k := k) t
          else X (t, (0 : Fin (k + 1)))) (carryPoly p)).totalDegree
      ≤ 1 * (carryPoly p).totalDegree := totalDegree_bind₁_le _ _ 1 hf
    _ = (carryPoly p).totalDegree := Nat.one_mul _
    _ ≤ 2 * p - 2 := carryPoly_totalDegree_le hp.out.two_le

/-- For prime `p`, the digits of any sum modulo `p ^ k` are represented by polynomials in the
input digits, with the polynomial for position `i` having total degree at most `(2 * p - 2)
^ i` [Ivanyos, Lemma 5][Ivanyos2008]. -/
theorem source_lemma5_digit_polynomials (p : ℕ) [hp : Fact p.Prime] (k T : ℕ) :
    ∃ Q : Fin k → MvPolynomial (Fin T × Fin k) (ZMod p),
      (∀ i, (Q i).totalDegree ≤ (2 * p - 2) ^ (i.val)) ∧
      ∀ (b : Fin T → ℕ) (i : Fin k),
        MvPolynomial.eval (digitEval p b) (Q i)
          = (((∑ t, b t) % p ^ k / p ^ i.val % p : ℕ) : ZMod p) := by
  induction k generalizing T with
  | zero =>
      refine ⟨fun i => i.elim0, ?_, ?_⟩
      · intro i; exact i.elim0
      · intro b i; exact i.elim0
  | succ k ih =>
      obtain ⟨Qih, hdegih, hevalih⟩ := ih (T + T)
      let Q : Fin (k + 1) → MvPolynomial (Fin T × Fin (k + 1)) (ZMod p) :=
        Fin.cases (lowDigitPoly p T k)
          (fun j => MvPolynomial.bind₁ (stepSubst p T k) (Qih j))
      refine ⟨Q, ?_, ?_⟩
      · intro i
        induction i using Fin.cases with
        | zero =>
            have hQ0 : Q 0 = lowDigitPoly p T k := by
              show Fin.cases (lowDigitPoly p T k)
                (fun j => MvPolynomial.bind₁ (stepSubst p T k) (Qih j)) (0 : Fin (k+1))
                = lowDigitPoly p T k
              rw [Fin.cases_zero]
            rw [hQ0]
            have hdeg : (lowDigitPoly p T k).totalDegree ≤ 1 := by
              unfold lowDigitPoly
              apply MvPolynomial.totalDegree_finsetSum_le
              intro t _
              rw [MvPolynomial.totalDegree_X]
            have hgoal : (lowDigitPoly p T k).totalDegree ≤ (2 * p - 2) ^ (0 : Fin (k+1)).val := by
              have hz : ((0 : Fin (k+1)).val) = 0 := rfl
              rw [hz, pow_zero]
              exact hdeg
            exact hgoal
        | succ j =>
            have hQ : Q j.succ = MvPolynomial.bind₁ (stepSubst p T k) (Qih j) := by
              show Fin.cases (lowDigitPoly p T k)
                (fun j => MvPolynomial.bind₁ (stepSubst p T k) (Qih j)) (Fin.succ j)
                = MvPolynomial.bind₁ (stepSubst p T k) (Qih j)
              rw [Fin.cases_succ]
            rw [hQ]
            have hstep : ∀ z : Fin (T + T) × Fin k,
                (stepSubst (p := p) T k z).totalDegree ≤ 2 * p - 2 := by
              intro z
              obtain ⟨u, jj⟩ := z
              revert jj
              refine Fin.addCases (motive := fun u => ∀ jj : Fin k,
                  (stepSubst (p := p) T k (u, jj)).totalDegree ≤ 2 * p - 2) ?_ ?_ u
              · intro t jj
                have hsimp : stepSubst (p := p) T k (Fin.castAdd T t, jj)
                    = X (t, Fin.succ jj) := by
                  unfold stepSubst
                  rw [Fin.addCases_left]
                rw [hsimp, MvPolynomial.totalDegree_X]
                have := hp.out.two_le
                omega
              · intro t jj
                have hsimp : stepSubst (p := p) T k (Fin.natAdd T t, jj)
                    = if jj.val = 0 then carryAtPoly p t else 0 := by
                  unfold stepSubst
                  rw [Fin.addCases_right]
                rw [hsimp]
                split_ifs with h
                · exact totalDegree_carryAtPoly (p := p) (k := k) t
                · rw [MvPolynomial.totalDegree_zero]
                  exact Nat.zero_le _
            calc (MvPolynomial.bind₁ (stepSubst p T k) (Qih j)).totalDegree
                ≤ (2 * p - 2) * (Qih j).totalDegree :=
                  totalDegree_bind₁_le _ _ (2 * p - 2) hstep
              _ ≤ (2 * p - 2) * (2 * p - 2) ^ (j.val) :=
                  Nat.mul_le_mul_left _ (hdegih j)
              _ = (2 * p - 2) ^ (j.succ : Fin (k+1)).val := by
                  rw [Fin.val_succ, pow_succ']
      · intro b i
        induction i using Fin.cases with
        | zero =>
            have hQ0 : Q 0 = lowDigitPoly p T k := by
              show Fin.cases (lowDigitPoly p T k)
                (fun j => MvPolynomial.bind₁ (stepSubst p T k) (Qih j)) (0 : Fin (k+1))
                = lowDigitPoly p T k
              rw [Fin.cases_zero]
            rw [hQ0]
            unfold lowDigitPoly
            rw [map_sum]
            have hterm : ∀ t : Fin T, MvPolynomial.eval (digitEval p b)
                (X (t, (0 : Fin (k + 1)))) = ((b t : ℕ) : ZMod p) := by
              intro t
              rw [MvPolynomial.eval_X]
              show (((b t / p ^ (0 : Fin (k + 1)).val) % p : ℕ) : ZMod p)
                  = ((b t : ℕ) : ZMod p)
              simp only [Fin.val_zero, pow_zero, Nat.div_one, ZMod.natCast_mod]
            rw [Finset.sum_congr rfl (fun t _ => hterm t)]
            have hsumcast : (∑ t : Fin T, ((b t : ℕ) : ZMod p))
                = ((∑ t, b t : ℕ) : ZMod p) := by
              rw [Nat.cast_sum]
            rw [hsumcast]
            have hrhs : (((∑ t, b t) % p ^ (k + 1) / p ^ (0 : Fin (k+1)).val % p : ℕ)
                : ZMod p) = ((∑ t, b t : ℕ) : ZMod p) := by
              have hmod : (∑ t, b t) % p ^ (k + 1) % p = (∑ t, b t) % p := by
                apply Nat.mod_mod_of_dvd
                exact ⟨p ^ k, by rw [pow_succ']⟩
              simp only [Fin.val_zero, pow_zero, Nat.div_one]
              rw [ZMod.natCast_mod]
              calc (((∑ t, b t) % p ^ (k + 1) : ℕ) : ZMod p)
                  = ((((∑ t, b t) % p ^ (k + 1)) % p : ℕ) : ZMod p) :=
                    (ZMod.natCast_mod _ p).symm
                _ = (((∑ t, b t) % p : ℕ) : ZMod p) := by rw [hmod]
                _ = ((∑ t, b t : ℕ) : ZMod p) := ZMod.natCast_mod _ p
            rw [hrhs]
        | succ j =>
            have hQ : Q j.succ = MvPolynomial.bind₁ (stepSubst p T k) (Qih j) := by
              show Fin.cases (lowDigitPoly p T k)
                (fun j => MvPolynomial.bind₁ (stepSubst p T k) (Qih j)) (Fin.succ j)
                = MvPolynomial.bind₁ (stepSubst p T k) (Qih j)
              rw [Fin.cases_succ]
            rw [hQ, eval_bind₁]
            set b' : Fin (T + T) → ℕ :=
              Fin.addCases (fun t => b t / p) (fun t => carry p b t) with hb'def
            have hb'L : ∀ t : Fin T, b' (Fin.castAdd T t) = b t / p := by
              intro t
              rw [hb'def]
              exact Fin.addCases_left t
            have hb'R : ∀ t : Fin T, b' (Fin.natAdd T t) = carry p b t := by
              intro t
              rw [hb'def]
              exact Fin.addCases_right t
            have hfun : (fun z => MvPolynomial.eval (digitEval p b) (stepSubst p T k z))
                = digitEval p b' := by
              funext z
              obtain ⟨u, jj⟩ := z
              revert jj
              refine Fin.addCases (motive := fun u => ∀ jj : Fin k,
                  MvPolynomial.eval (digitEval p b) (stepSubst p T k (u, jj))
                    = digitEval p b' (u, jj)) ?_ ?_ u
              · intro t jj
                have hsimp : stepSubst (p := p) T k (Fin.castAdd T t, jj)
                    = X (t, Fin.succ jj) := by
                  unfold stepSubst
                  rw [Fin.addCases_left]
                rw [hsimp, MvPolynomial.eval_X]
                show (((b t / p ^ (jj.succ).val) % p : ℕ) : ZMod p)
                    = (((b' (Fin.castAdd T t) / p ^ jj.val) % p : ℕ) : ZMod p)
                rw [hb'L t]
                show (((b t / p ^ (jj.succ).val) % p : ℕ) : ZMod p)
                    = (((b t / p / p ^ jj.val) % p : ℕ) : ZMod p)
                rw [Fin.val_succ, pow_succ', Nat.div_div_eq_div_mul]
              · intro t jj
                have hsimp : stepSubst (p := p) T k (Fin.natAdd T t, jj)
                    = if jj.val = 0 then carryAtPoly p t else 0 := by
                  unfold stepSubst
                  rw [Fin.addCases_right]
                rw [hsimp]
                by_cases h0 : jj.val = 0
                · rw [if_pos h0, eval_carryAtPoly]
                  show ((carry p b t : ℕ) : ZMod p)
                      = (((b' (Fin.natAdd T t) / p ^ jj.val) % p : ℕ) : ZMod p)
                  rw [hb'R t, h0, pow_zero, Nat.div_one,
                    Nat.mod_eq_of_lt (lt_of_le_of_lt (carry_le_one p b t)
                      (by have := hp.out.two_le; omega))]
                · rw [if_neg h0]
                  rw [show MvPolynomial.eval (digitEval p b)
                      (0 : MvPolynomial (Fin T × Fin (k + 1)) (ZMod p)) = 0 from by simp]
                  show (0 : ZMod p)
                      = (((b' (Fin.natAdd T t) / p ^ jj.val) % p : ℕ) : ZMod p)
                  rw [hb'R t]
                  have hlt : carry p b t < p ^ jj.val := by
                    have h1 : carry p b t ≤ 1 := carry_le_one p b t
                    have h2 : 1 < p := by have := hp.out.two_le; omega
                    have h3 : p ≤ p ^ jj.val :=
                      Nat.le_self_pow (n := jj.val) h0 p
                    omega
                  rw [Nat.div_eq_of_lt hlt, Nat.zero_mod]
                  simp
            rw [hfun, hevalih b' j]
            have hsum : (∑ z : Fin (T + T), b' z) = (∑ t, b t) / p := by
              rw [Fin.sum_univ_add]
              have h1 : (∑ t : Fin T, b' (Fin.castAdd T t)) = ∑ t : Fin T, b t / p :=
                Finset.sum_congr rfl fun t _ => hb'L t
              have h2 : (∑ t : Fin T, b' (Fin.natAdd T t)) = ∑ t : Fin T, carry p b t :=
                Finset.sum_congr rfl fun t _ => hb'R t
              rw [h1, h2, ← carry_sum_eq hp.out.pos]
              have hsplit : (∑ t : Fin T, b t)
                  = p * (∑ t : Fin T, b t / p) + ∑ t : Fin T, b t % p := by
                rw [Finset.mul_sum, ← Finset.sum_add_distrib]
                exact Finset.sum_congr rfl fun t _ => (Nat.div_add_mod (b t) p).symm
              rw [hsplit, Nat.mul_add_div hp.out.pos]
            rw [hsum]
            have hdigit : ((∑ t, b t) % p ^ (k+1) / p ^ (j.succ : Fin (k+1)).val % p)
                = ((∑ t, b t) / p % p ^ k / p ^ j.val % p) := by
              have hs : (∑ t, b t) % p < p := Nat.mod_lt _ hp.out.pos
              have hshift : (∑ t, b t) % p ^ (k+1) / p
                  = ((∑ t, b t) / p) % p ^ k := by
                nth_rewrite 1 [show (∑ t, b t)
                    = p * ((∑ t, b t) / p) + (∑ t, b t) % p from
                  (Nat.div_add_mod (∑ t, b t) p).symm]
                rw [low_digit_shift hp.out.pos hs]
              have hdiv : (∑ t, b t) % p ^ (k+1) / p ^ (j.val + 1)
                  = ((∑ t, b t) % p ^ (k+1) / p) / p ^ j.val := by
                rw [show p ^ (j.val + 1) = p * p ^ j.val from by rw [pow_succ']]
                rw [← Nat.div_div_eq_div_mul]
              calc (∑ t, b t) % p ^ (k+1) / p ^ (j.succ : Fin (k+1)).val % p
                  = (∑ t, b t) % p ^ (k+1) / p ^ (j.val + 1) % p := by
                      rw [Fin.val_succ]
                _ = ((∑ t, b t) % p ^ (k+1) / p) / p ^ j.val % p := by rw [hdiv]
                _ = (((∑ t, b t) / p) % p ^ k) / p ^ j.val % p := by rw [hshift]
            congr 1
            exact hdigit.symm

end Lemma5

end Qatlib.Papers.LinearDiseq07.MainResults
