/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Action.Pi
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.FunLike.Equiv
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Int.Order.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Prod.Basic
import Mathlib.Data.Subtype
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Function.Defs
import Mathlib.Order.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Tactic.Zify

/-!
# Feistel Simon periods and permutation counting

`feistelSimonFun` derives a binary-periodic function from the first half of a three-round
Feistel network, with explicit nonzero period `feistelPeriod`. The module also counts
permutations satisfying a fixed first-half difference condition by extending bijections between
two-point complements. See [SantoliSchaffner2017] for the source development.

## Main statements

* `feistel3_simon_period`: verifies invariance under the explicit Feistel period.
* `random_permutation_bad_count`: bounds the number of permutations with a prescribed first-half
  difference at two distinct inputs.
* `period_and_fixed_pair_count`: combines the period-existence and fixed-pair counting
  statements.

## References

* [Santoli and Schaffner, 2017][SantoliSchaffner2017]
-/

set_option autoImplicit false

namespace Qatlib.Papers.SimonSymKey16.FeistelPeriod

/-- The type of `n`-coordinate binary blocks, with coordinatewise addition in `ZMod 2`. -/
abbrev Block (n : ℕ) := Fin n → ZMod 2

variable {n : ℕ}

/-- Adding a binary block to itself gives zero. -/
lemma block_add_self (x : Block n) : x + x = 0 := by
  calc x + x = (1 : ZMod 2) • x + (1 : ZMod 2) • x := by simp
    _ = ((1 : ZMod 2) + 1) • x := (add_smul (1 : ZMod 2) (1 : ZMod 2) x).symm
    _ = 0 := by
        have h2 : (1 : ZMod 2) + 1 = 0 := by decide
        rw [h2, zero_smul]

/-- For binary blocks, `x + y + x = y`. -/
lemma block_add_add_self (x y : Block n) : x + y + x = y := by
  rw [add_comm (x + y) x, ← add_assoc, block_add_self, zero_add]

/-- For binary blocks, `x + y + y = x`. -/
lemma block_add_self_add (x y : Block n) : x + y + y = x := by
  rw [add_assoc, block_add_self, add_zero]

/-- Adding `q` after the shift `p + q` reduces the shift to `p`. -/
lemma add_shift_cancel_right (a p q : Block n) : (a + (p + q)) + q = a + p := by
  rw [add_assoc, block_add_self_add]

/-- Adding `p` after the shift `p + q` reduces the shift to `q`. -/
lemma add_shift_cancel_left (a p q : Block n) : (a + (p + q)) + p = a + q := by
  rw [add_assoc, block_add_add_self]

/-- Two binary blocks whose sum is zero are equal. -/
lemma eq_of_add_eq_zero {x y : Block n} (h : x + y = 0) : x = y := by
  have h1 : x + (y + y) = x := by rw [block_add_self, add_zero]
  calc x = x + (y + y) := h1.symm
    _ = (x + y) + y := (add_assoc x y y).symm
    _ = 0 + y := by rw [h]
    _ = y := zero_add y

/-- The first output half `c + P2 (a + P1 c)` of the three-round Feistel formula. -/
def feistelFirstHalf (P1 P2 : Block n → Block n) (a c : Block n) : Block n :=
  c + P2 (a + P1 c)

/-- The pair of output blocks obtained from the three-round Feistel formula with round functions
`P1`, `P2`, and `P3`. -/
def feistel3 (P1 P2 P3 : Block n → Block n) (a c : Block n) : Block n × Block n :=
  (feistelFirstHalf P1 P2 a c,
    (a + P1 c) + P3 (feistelFirstHalf P1 P2 a c))

/-- The first component of the three-round Feistel output equals `feistelFirstHalf P1 P2 a c`.
See [SantoliSchaffner2017]. -/
lemma feistel3_fst (P1 P2 P3 : Block n → Block n) (a c : Block n) :
    (feistel3 P1 P2 P3 a c).1 = feistelFirstHalf P1 P2 a c := rfl

/-- The function that selects prefix block `α` or `β` by a Boolean input and adds that prefix to
the first Feistel output half. -/
def feistelSimonFun (P1 P2 : Block n → Block n) (α β : Block n)
    (u : Bool × Block n) : Block n :=
  match u.1 with
  | false => feistelFirstHalf P1 P2 u.2 α + α
  | true => feistelFirstHalf P1 P2 u.2 β + β

/-- The shift on a Boolean and binary-block pair, toggling the Boolean when the shift bit is
true and adding the shift block. -/
def bxorShift (u s : Bool × Block n) : Bool × Block n :=
  (if s.1 then !u.1 else u.1, u.2 + s.2)

/-- The proposed Feistel period consisting of the true selector bit and block `P1 α + P1 β`. -/
def feistelPeriod (P1 : Block n → Block n) (α β : Block n) : Bool × Block n :=
  (true, P1 α + P1 β)

/-- The Feistel period differs from `(false, 0)` because its selector bit is true. -/
lemma feistelPeriod_ne_zero (P1 : Block n → Block n) (α β : Block n) :
    feistelPeriod P1 α β ≠ (false, 0) := by
  intro h
  exact Bool.noConfusion (congrArg Prod.fst h)

/-- The function `feistelSimonFun` is invariant under shifting by `feistelPeriod P1 α β`. -/
theorem feistel3_simon_period (P1 P2 : Block n → Block n) (α β : Block n) :
    ∀ u : Bool × Block n,
      feistelSimonFun P1 P2 α β (bxorShift u (feistelPeriod P1 α β)) =
        feistelSimonFun P1 P2 α β u := by
  intro u
  rcases u with ⟨b, a⟩
  cases b
  · simp only [feistelSimonFun, bxorShift, feistelPeriod, feistelFirstHalf, if_true,
      Bool.not_false]
    rw [block_add_add_self, block_add_add_self, add_shift_cancel_right]
  · simp only [feistelSimonFun, bxorShift, feistelPeriod, feistelFirstHalf, if_true,
      Bool.not_true]
    rw [block_add_add_self, block_add_add_self, add_shift_cancel_left]

/-- The predicate that shifting every input by `s` leaves the function value unchanged. -/
def PassesPeriodTest (f : Bool × Block n → Block n) (s : Bool × Block n) : Prop :=
  ∀ u, f (bxorShift u s) = f u

/-- The Feistel-derived function possesses a nonzero shift satisfying `PassesPeriodTest`. -/
theorem feistel3_passes_period_test (P1 P2 : Block n → Block n) (α β : Block n) :
    ∃ s : Bool × Block n, s ≠ (false, 0) ∧
      PassesPeriodTest (feistelSimonFun P1 P2 α β) s :=
  ⟨feistelPeriod P1 α β, feistelPeriod_ne_zero P1 α β,
    feistel3_simon_period P1 P2 α β⟩

/-- The finite set of permutations whose first output halves at `p` and `q` sum to the specified
block `c`. -/
noncomputable def badPerms (p q : Block n × Block n) (c : Block n) :
    Finset ((Block n × Block n) ≃ (Block n × Block n)) :=
  Finset.univ.filter (fun V => (V p).1 + (V q).1 = c)

section PermCount

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The type of bijections between the complements of the designated source and target point
pairs. -/
abbrev ComplementEquiv (p q y z : X) :=
  {x // x ≠ p ∧ x ≠ q} ≃ {x // x ≠ y ∧ x ≠ z}

/-- The permutation extending a complement bijection by mapping the distinct points `p, q` to
the distinct points `y, z`. -/
noncomputable def extendComplement (p q y z : X) (hpq : p ≠ q) (hyz : y ≠ z)
    (φ : ComplementEquiv p q y z) : X ≃ X where
  toFun x :=
    if hx : x = p then y
    else if hx' : x = q then z
    else (φ ⟨x, ⟨hx, hx'⟩⟩ : X)
  invFun w :=
    if hw : w = y then p
    else if hw' : w = z then q
    else (φ.symm ⟨w, ⟨hw, hw'⟩⟩ : X)
  left_inv := by
    intro x
    by_cases hx : x = p
    · subst hx
      simp
    · by_cases hx' : x = q
      · subst hx'
        simp [Ne.symm hpq, Ne.symm hyz]
      · have hval : (φ ⟨x, ⟨hx, hx'⟩⟩ : X) ≠ y := (φ ⟨x, ⟨hx, hx'⟩⟩).2.1
        have hval' : (φ ⟨x, ⟨hx, hx'⟩⟩ : X) ≠ z := (φ ⟨x, ⟨hx, hx'⟩⟩).2.2
        simp only [dif_neg hx, dif_neg hx', dif_neg hval, dif_neg hval']
        simp [φ.symm_apply_apply]
  right_inv := by
    intro w
    by_cases hw : w = y
    · subst hw
      simp
    · by_cases hw' : w = z
      · subst hw'
        simp [Ne.symm hpq, Ne.symm hyz]
      · have hval : (φ.symm ⟨w, ⟨hw, hw'⟩⟩ : X) ≠ p := (φ.symm ⟨w, ⟨hw, hw'⟩⟩).2.1
        have hval' : (φ.symm ⟨w, ⟨hw, hw'⟩⟩ : X) ≠ q := (φ.symm ⟨w, ⟨hw, hw'⟩⟩).2.2
        simp only [dif_neg hw, dif_neg hw', dif_neg hval, dif_neg hval']
        simp [φ.apply_symm_apply]

/-- The equivalence between permutations mapping `p` to `y` and `q` to `z` and bijections of
their two-point complements. -/
noncomputable def fiberEquiv (p q y z : X) (hpq : p ≠ q) (hyz : y ≠ z) :
    {V : X ≃ X // V p = y ∧ V q = z} ≃ ComplementEquiv p q y z where
  toFun V :=
    { toFun := fun x =>
        ⟨V.1 x, by
          constructor
          · intro h
            have h1 : V.1 x = V.1 p := by rw [h]; exact V.2.1.symm
            exact x.2.1 (V.1.injective h1)
          · intro h
            have h1 : V.1 x = V.1 q := by rw [h]; exact V.2.2.symm
            exact x.2.2 (V.1.injective h1)⟩
      invFun := fun w =>
        ⟨V.1.symm w, by
          constructor
          · intro h
            have h1 : (w : X) = V.1 p := by
              calc (w : X) = V.1 (V.1.symm w) := (V.1.apply_symm_apply w).symm
                _ = V.1 p := by rw [h]
            exact w.2.1 (by rw [h1, V.2.1])
          · intro h
            have h1 : (w : X) = V.1 q := by
              calc (w : X) = V.1 (V.1.symm w) := (V.1.apply_symm_apply w).symm
                _ = V.1 q := by rw [h]
            exact w.2.2 (by rw [h1, V.2.2])⟩
      left_inv := fun x => Subtype.ext (V.1.symm_apply_apply x)
      right_inv := fun w => Subtype.ext (V.1.apply_symm_apply w) }
  invFun φ :=
    ⟨extendComplement p q y z hpq hyz φ, by
      constructor
      · simp [extendComplement]
      · simp [extendComplement, Ne.symm hpq]⟩
  left_inv V := by
    refine Subtype.ext ?_
    ext x
    by_cases hx : x = p
    · subst hx
      simp [extendComplement, V.2.1]
    · by_cases hx' : x = q
      · subst hx'
        simp [extendComplement, Ne.symm hpq, V.2.2]
      · simp [extendComplement, hx, hx']
  right_inv φ := by
    ext x
    simp [extendComplement, x.2.1, x.2.2]

/-- Removing two distinct points from a finite type leaves cardinality `Fintype.card X - 2`. -/
lemma card_complement_two (p q : X) (hpq : p ≠ q) :
    Fintype.card {x // x ≠ p ∧ x ≠ q} = Fintype.card X - 2 := by
  rw [Fintype.card_subtype]
  have hset : (Finset.univ.filter (fun x : X => x ≠ p ∧ x ≠ q)) = Finset.univ \ {p, q} := by
    ext x
    simp
  rw [hset, Finset.card_sdiff_of_subset (by simp), Finset.card_univ,
    Finset.card_pair_eq_two_iff.mpr hpq]

/-- The number of bijections between the two-point complements is `(Fintype.card X - 2)!`. -/
lemma card_complement_equiv (p q y z : X) (hpq : p ≠ q) (hyz : y ≠ z) :
    Fintype.card (ComplementEquiv p q y z) = Nat.factorial (Fintype.card X - 2) := by
  have hα : Fintype.card {x // x ≠ p ∧ x ≠ q} = Fintype.card X - 2 := card_complement_two p q hpq
  have hβ : Fintype.card {x // x ≠ y ∧ x ≠ z} = Fintype.card X - 2 := card_complement_two y z hyz
  have e : {x // x ≠ p ∧ x ≠ q} ≃ {x // x ≠ y ∧ x ≠ z} :=
    Fintype.equivOfCardEq (hα.trans hβ.symm)
  simpa [ComplementEquiv, hα] using Fintype.card_equiv e

/-- The number of permutations with two specified distinct input-output pairs is `(Fintype.card
X - 2)!`. -/
lemma card_fiber (p q y z : X) (hpq : p ≠ q) (hyz : y ≠ z) :
    Fintype.card {V : X ≃ X // V p = y ∧ V q = z} = Nat.factorial (Fintype.card X - 2) := by
  rw [Fintype.card_congr (fiberEquiv p q y z hpq hyz)]
  exact card_complement_equiv p q y z hpq hyz

end PermCount

/-- For distinct inputs and a block space of size at least two, the block-space cardinality
times the number of permutations with a prescribed first-half difference is at most twice
the total permutation count. -/
theorem random_permutation_bad_count (hcard : 2 ≤ Fintype.card (Block n))
    (p q : Block n × Block n) (hpq : p ≠ q) (c : Block n) :
    Fintype.card (Block n) * (badPerms p q c).card
      ≤ 2 * Fintype.card ((Block n × Block n) ≃ (Block n × Block n)) := by
  classical
  set N := Fintype.card (Block n) with hN
  set s : Finset ((Block n × Block n) ≃ (Block n × Block n)) :=
    Finset.univ.filter (fun V => (V p).1 + (V q).1 = c) with hs
  have hs_eq : s = badPerms p q c := rfl
  have hcardX : Fintype.card (Block n × Block n) = N * N := by
    simp [N, Fintype.card_prod]
  have hNpos : 1 ≤ N * N := by nlinarith [hcard]
  set g : ((Block n × Block n) ≃ (Block n × Block n)) →
      Block n × Block n × Block n :=
    fun V => ((V p).1, (V p).2, (V q).2) with hg
  have hfiber : ∀ b ∈ s.image g,
      (s.filter (fun V => g V = b)).card ≤ Nat.factorial (N * N - 2) := by
    intro b hb
    let a : Block n := b.1
    let u : Block n := b.2.1
    let v : Block n := b.2.2
    set y : Block n × Block n := (a, u)
    set z : Block n × Block n := (c + a, v)
    by_cases hyz : y = z
    · have hempty : s.filter (fun V => g V = b) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro V hV
        simp only [s, Finset.mem_filter, Finset.mem_univ, true_and] at hV
        obtain ⟨hVs, hVg⟩ := hV
        have hVp : V p = y := by
          have := congrArg
            (fun t : Block n × Block n × Block n => ((t.1, t.2.1) : Block n × Block n)) hVg
          simpa [g, y, a, u] using this
        have hpa : (V p).1 = a := by
          have := congrArg (fun t : Block n × Block n × Block n => t.1) hVg
          simpa [g, a] using this
        have hfirst : (V q).1 = c + a := by
          have hxx : (V p).1 + (V p).1 = 0 := by
            ext i
            exact CharTwo.add_self_eq_zero ((V p).1 i)
          have h1 : (V q).1 = c + (V p).1 := by
            rw [← hVs, add_comm (V p).1 (V q).1, add_assoc, hxx, add_zero]
          rwa [hpa] at h1
        have hsecond : (V q).2 = v := by
          have := congrArg (fun t : Block n × Block n × Block n => t.2.2) hVg
          simpa [g, v] using this
        have hVq : V q = z := Prod.ext hfirst hsecond
        exact hpq (V.injective (hVp.trans (hyz.trans hVq.symm)))
      rw [hempty, Finset.card_empty]
      exact Nat.zero_le _
    · have hsub : s.filter (fun V => g V = b) ⊆
          Finset.univ.filter (fun V : (Block n × Block n) ≃ (Block n × Block n) =>
            V p = y ∧ V q = z) := by
        intro V hV
        simp only [s, Finset.mem_filter, Finset.mem_univ, true_and] at hV ⊢
        obtain ⟨hVs, hVg⟩ := hV
        constructor
        · have := congrArg
            (fun t : Block n × Block n × Block n => ((t.1, t.2.1) : Block n × Block n)) hVg
          simpa [g, y, a, u] using this
        · have hpa : (V p).1 = a := by
            have := congrArg (fun t : Block n × Block n × Block n => t.1) hVg
            simpa [g, a] using this
          have hfirst : (V q).1 = c + a := by
            have hxx : (V p).1 + (V p).1 = 0 := by
              ext i
              exact CharTwo.add_self_eq_zero ((V p).1 i)
            have h1 : (V q).1 = c + (V p).1 := by
              rw [← hVs, add_comm (V p).1 (V q).1, add_assoc, hxx, add_zero]
            rwa [hpa] at h1
          have hsecond : (V q).2 = v := by
            have := congrArg (fun t : Block n × Block n × Block n => t.2.2) hVg
            simpa [g, v] using this
          exact Prod.ext hfirst hsecond
      have hle := Finset.card_le_card hsub
      have hcard_eq : (Finset.univ.filter
          (fun V : (Block n × Block n) ≃ (Block n × Block n) => V p = y ∧ V q = z)).card
          = Nat.factorial (N * N - 2) := by
        rw [← Fintype.card_subtype]
        have h := card_fiber (X := Block n × Block n) p q y z hpq hyz
        simpa [hcardX] using h
      exact hle.trans_eq hcard_eq
  have hsum : s.card ≤ (s.image g).card * Nat.factorial (N * N - 2) := by
    rw [Finset.card_eq_sum_card_image (f := g) (s := s)]
    simpa [nsmul_eq_mul] using
      Finset.sum_le_card_nsmul (s.image g)
        (fun b => (s.filter (fun V => g V = b)).card)
        (Nat.factorial (N * N - 2)) (fun b hb => hfiber b hb)
  have himage : (s.image g).card ≤ N * N * N := by
    calc (s.image g).card ≤ Fintype.card (Block n × Block n × Block n) := Finset.card_le_univ _
      _ = N * N * N := by simp [N, Fintype.card_prod, mul_assoc]
  have hsbound : s.card ≤ N * N * N * Nat.factorial (N * N - 2) :=
    hsum.trans (Nat.mul_le_mul_right _ himage)
  have hN4 : 4 ≤ N * N := by nlinarith
  have hfac : Nat.factorial (N * N) =
      N * N * (N * N - 1) * Nat.factorial (N * N - 2) := by
    have h1 : Nat.factorial (N * N) = (N * N) * Nat.factorial (N * N - 1) := by
      conv_lhs => rw [show N * N = (N * N - 1) + 1 by omega]
      rw [Nat.factorial_succ, Nat.sub_add_cancel hNpos]
    have h2 : Nat.factorial (N * N - 1) =
        (N * N - 1) * Nat.factorial (N * N - 2) := by
      conv_lhs => rw [show N * N - 1 = (N * N - 2) + 1 by omega]
      rw [Nat.factorial_succ, show N * N - 2 + 1 = N * N - 1 by omega]
    rw [h1, h2]
    ring
  have hcardPerm : Fintype.card ((Block n × Block n) ≃ (Block n × Block n)) =
      Nat.factorial (N * N) := by
    rw [Fintype.card_perm, hcardX]
  calc N * (badPerms p q c).card
      = N * s.card := by rw [hs_eq]
    _ ≤ N * (N * N * N * Nat.factorial (N * N - 2)) := Nat.mul_le_mul_left _ hsbound
    _ = N * N * (N * N) * Nat.factorial (N * N - 2) := by ring
    _ ≤ 2 * (N * N * (N * N - 1) * Nat.factorial (N * N - 2)) := by
        have hN2le : N * N ≤ 2 * (N * N - 1) := by
          have h4 : 4 ≤ N * N := by nlinarith
          omega
        have h1 : N * N * (N * N) ≤ N * N * (2 * (N * N - 1)) :=
          Nat.mul_le_mul_left (N * N) hN2le
        have h2 : N * N * (N * N) * Nat.factorial (N * N - 2)
            ≤ (N * N * (2 * (N * N - 1))) * Nat.factorial (N * N - 2) :=
          Nat.mul_le_mul_right _ h1
        calc N * N * (N * N) * Nat.factorial (N * N - 2)
            ≤ (N * N * (2 * (N * N - 1))) * Nat.factorial (N * N - 2) := h2
          _ = 2 * (N * N * (N * N - 1) * Nat.factorial (N * N - 2)) := by ring
    _ = 2 * Fintype.card ((Block n × Block n) ≃ (Block n × Block n)) := by
        rw [hcardPerm, hfac]

/-- A Feistel-derived function with distinct selected prefixes has a nonzero period, and
permutations satisfy the stated fixed-pair first-half-difference counting bound. -/
theorem period_and_fixed_pair_count (hcard : 2 ≤ Fintype.card (Block n)) :
    (∀ (P1 P2 : Block n → Block n) (α β : Block n), α ≠ β →
        ∃ s : Bool × Block n, s ≠ (false, 0) ∧
          PassesPeriodTest (feistelSimonFun P1 P2 α β) s) ∧
      (∀ (p q : Block n × Block n), p ≠ q → ∀ c : Block n,
        Fintype.card (Block n) * (badPerms p q c).card
          ≤ 2 * Fintype.card ((Block n × Block n) ≃ (Block n × Block n))) := by
  refine ⟨?_, ?_⟩
  · intro P1 P2 α β _hαβ
    exact feistel3_passes_period_test P1 P2 α β
  · intro p q hpq c
    exact random_permutation_bad_count hcard p q hpq c

end Qatlib.Papers.SimonSymKey16.FeistelPeriod
