/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.ExactSimon97.MachineSuccess
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.BigOperators

@[expose] public section

/-!
# Simon's promised-oracle distribution and the transcript distribution law

Theorem 9 and Corollary 10 of [BrassardHoyer1997] (quant-ph/9704027v1). This module replaces the machine-success interface’s
uniform distribution over *all* Boolean oracles with Simon's promised-oracle
distribution and proves the first link of Theorem 9: the distribution law of
the adaptive query/answer transcript under the promised-oracle draw.

The promise structure is the `X ∪ Xs` identification of Theorem 9's setting:
a mask `s` translates the address space by pointwise XOR (`maskAdd`), and a
promised oracle `f` is constant on each two-point coset `{x, x ⊕ s}`
(`simonPromise`: `f (x ⊕ s) = f x` for every `x`) — the oracle hides the
subgroup `{0, s}`. The promise fiber `{f // simonPromise s f}` is nonempty
and finite; at a nonzero mask, a bit-flip transversal exhibits its exact
cardinality `2 ^ 2 ^ (a - 1)` (`promiseFiber_card`), halving the exponent of
the full Boolean oracle space.

`promiseOracleLaw` is the uniform finite distribution on the promise fiber
(zero mass off the fiber, equal masses on it). The execution-derived success-expectation
machinery is re-established on it: `promiseOracleExpect`, `promiseSuccess`
with its finite average form and the `[0, 1]` range.

Theorem 9's first link is the transcript distribution law `probEvent_promise_eq`:
for every decidable oracle property `Q`, the probability that one promised-oracle
draw satisfies `Q` is exactly the counting bound `|{promised oracles satisfying
Q}| / |promise fiber|`. Instantiating `Q` at the execution-derived
transcript map gives `transcriptProb_eq`: the mass of an adaptive transcript is
the number of promised oracles reproducing it, divided by the fiber size; the
mass is in `[0, 1]` (`transcriptProb_nonneg`, `transcriptProb_le_one`) and is
bounded by the answer-agreement counting bound (`transcriptProb_le_agree`,
via `oracleTranscript_agree`: every recorded answer bit is a genuine oracle
value). As the single-query seed of the conditioning argument,
`promiseBit_uniform` shows that each fixed address reads a fair coin under
the promised draw (at the zero mask the law degenerates to the uniform law
over all oracles, and the reading is still fair).

Honest non-coverage. The machine interface consults Boolean oracles, so the
promise here is the invariance half `f (x ⊕ s) = f x` only; the exactness half
of the paper's promise (only the coset pairs collide) is not expressible as a
condition on a single Boolean output bit and is not imposed. The conditional
form of Theorem 9 (transcript uniformity conditioned on a prefix of fresh
queries), the lower bound itself, oracle diagonalization with future-query
isolation, `QP^O` membership, and any Corollary 10 claim remain open (DESIGN
§12.8: nothing here is the original theorem).

## Main statements

* `simonPromise` / `promiseFiber_card`: the `X ∪ Xs` promise and the exact
  size `2 ^ 2 ^ (a - 1)` of its oracle fiber at a nonzero mask.
* `promiseOracleLaw`: the uniform finite distribution on the promise fiber.
* `promiseSuccess_eq_average` / `promiseSuccess_le_one`: the execution-derived
  success-expectation machinery on the promised draw.
* `probEvent_promise_eq`: promised-draw probability = counting bound over the
  promise fiber — the general distribution law.
* `transcriptProb_eq`: the adaptive transcript mass equals
  `|{promised oracles reproducing the transcript}| / |promise fiber|`.
* `transcriptProb_le_agree`: the transcript mass is bounded by the
  answer-agreement counting bound.
* `promiseBit_uniform`: under the promised draw, each fixed address bit is a
  fair coin.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

open scoped BigOperators Classical

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.CircuitLang.XorOracle
open Qatlib.Papers.ExactSimon97.OracleMachine
open Qatlib.Papers.ExactSimon97.MachineEnum
open Qatlib.Papers.ExactSimon97.MachineSuccess
open Qatlib.Papers.ExactSimon97.MainResults

namespace Qatlib.Papers.ExactSimon97.PromiseOracle

variable {a w : ℕ}

/-! ## The mask translate on the address space -/

/-- The zero mask of an address space: every coordinate false. -/
def zeroAddr (a : ℕ) : Addr a :=
  fun _ => false

/-- Translate an address by a mask: pointwise XOR with the mask bits, the same
Boolean XOR used by the standard `xorInto` oracle update. This is addition in
the `F₂`-vector-space structure of `Addr a` (the operation behind `x - y` on
`BoolVec n` in the Qatlib ExactSimon97 development). -/
def maskAdd (s x : Addr a) : Addr a :=
  fun i => x i ^^ s i

/-- Translating twice by the same mask returns the original address. -/
theorem maskAdd_self (s x : Addr a) : maskAdd s (maskAdd s x) = x := by
  funext i
  simp only [maskAdd, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

/-- Translation by a mask is injective. -/
theorem maskAdd_inj (s : Addr a) : Function.Injective (maskAdd s) := by
  intro x y h
  have h2 := congrArg (maskAdd s) h
  rwa [maskAdd_self, maskAdd_self] at h2

/-- A nonzero mask has at least one true bit. -/
theorem exists_bit_of_ne_zeroAddr {s : Addr a} (hs : s ≠ zeroAddr a) :
    ∃ k : Fin a, s k = true := by
  by_contra h
  have hall : ∀ i : Fin a, ¬ (s i = true) := fun i hi => h ⟨i, hi⟩
  refine hs (funext fun i => ?_)
  show s i = zeroAddr a i
  cases hsi : s i with
  | true => exact absurd hsi (hall i)
  | false => rfl

/-- Translation by a nonzero mask moves every address: no address is its own
coset partner. -/
theorem maskAdd_ne_self {s : Addr a} (hs : s ≠ zeroAddr a) (x : Addr a) :
    maskAdd s x ≠ x := by
  obtain ⟨k, hk⟩ := exists_bit_of_ne_zeroAddr hs
  intro heq
  have hbit : maskAdd s x k = x k := congrFun heq k
  simp only [maskAdd] at hbit
  rw [hk, Bool.xor_true] at hbit
  cases hxk : x k <;> rw [hxk] at hbit <;> simp at hbit

/-! ## The `X ∪ Xs` promise on Boolean oracles -/

/-- The Simon promise at mask `s`: the oracle is constant on each two-point
coset `{x, x ⊕ s}`, i.e. `f (x ⊕ s) = f x` for every address `x`. Reading the
domain as `X ∪ Xs` (each address together with its translate), a promised
oracle assigns one bit per coset; it hides the subgroup `{0, s}`. -/
def simonPromise (s : Addr a) (f : Addr a → Bool) : Prop :=
  ∀ x, f (maskAdd s x) = f x

/-- The Simon promise is decidable: a finite check over the address space. -/
instance simonPromiseDecidablePred (s : Addr a) : DecidablePred (simonPromise s) :=
  fun _ => Fintype.decidableForallFintype

/-- Constant oracles satisfy the promise at every mask: the fiber is nonempty. -/
theorem simonPromise_const (s : Addr a) (b : Bool) :
    simonPromise s (fun _ : Addr a => b) :=
  fun _ => rfl

/-- The promise fiber of mask `s`: the Boolean oracles satisfying the Simon
promise. -/
abbrev PromiseFiber (s : Addr a) : Type :=
  {f : Addr a → Bool // simonPromise s f}

/-- The promise fiber is nonempty: constant oracles are promised. -/
theorem promiseFiber_nonempty (s : Addr a) : Nonempty (PromiseFiber s) :=
  ⟨⟨fun _ => false, simonPromise_const s false⟩⟩

/-- The promise fiber, counted through its characteristic filter, is positive. -/
theorem promiseFiberCard_pos (s : Addr a) :
    0 < (Finset.univ.filter (simonPromise s)).card :=
  Finset.card_pos.2 ⟨fun _ => false,
    Finset.mem_filter.2 ⟨Finset.mem_univ _, simonPromise_const s false⟩⟩

/-! ## A bit-flip transversal and the fiber cardinality -/

/-- Flip exactly one address bit (not to be confused with the full mask
translate `maskAdd`). -/
def maskFlip (k : Fin a) (x : Addr a) : Addr a :=
  Function.update x k (!x k)

/-- The flipped address reads the negated bit at the flipped position. -/
theorem maskFlip_bit (k : Fin a) (x : Addr a) : maskFlip k x k = !x k := by
  simp [maskFlip]

/-- Flipping the same bit twice is the identity. -/
theorem maskFlip_self (k : Fin a) (x : Addr a) : maskFlip k (maskFlip k x) = x := by
  funext i
  by_cases h : i = k
  · subst h
    simp [maskFlip, Function.update_self]
  · simp [maskFlip, Function.update_self, Function.update_of_ne h]

/-- The transversal slice of a bit position: the addresses reading `false`
there. -/
abbrev maskSlice (k : Fin a) : Type :=
  {x : Addr a // x k = false}

/-- The full address space of the machine layer has `2 ^ a` addresses. -/
theorem card_addr (a : ℕ) : Fintype.card (Addr a) = 2 ^ a := by
  simp [Fintype.card_fin, Fintype.card_bool]

/-- Complementing one bit pairs the two slices of that position: equally many
addresses read `false` and `true` at `k`. -/
theorem card_bit_slices (k : Fin a) :
    (Finset.univ.filter (fun x : Addr a => x k = false)).card =
      (Finset.univ.filter (fun x : Addr a => x k = true)).card := by
  refine Finset.card_bij' (fun x _ => maskFlip k x) (fun x _ => maskFlip k x)
    (fun x hx => ?_) (fun x hx => ?_) (fun x _ => maskFlip_self k x)
    (fun x _ => maskFlip_self k x)
  · obtain hx' := (Finset.mem_filter.1 hx).2
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, by
      rw [maskFlip_bit, hx']; exact Bool.not_false⟩
  · obtain hx' := (Finset.mem_filter.1 hx).2
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, by
      rw [maskFlip_bit, hx']; exact Bool.not_true⟩

/-- The transversal slice carries half the address space: `2 ^ (a - 1)`
addresses. -/
theorem maskSlice_card (k : Fin a) : Fintype.card (maskSlice k) = 2 ^ (a - 1) := by
  have hunion : (Finset.univ.filter (fun x : Addr a => x k = false)) ∪
      (Finset.univ.filter (fun x : Addr a => x k = true)) = Finset.univ := by
    ext x
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    cases hx : x k with
    | false => simp
    | true => simp
  have hdisj : (Finset.univ.filter (fun x : Addr a => x k = false)) ∩
      (Finset.univ.filter (fun x : Addr a => x k = true)) = ∅ := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
    cases hx : x k with
    | false => simp
    | true => simp
  have haddr : (Finset.univ.filter (fun x : Addr a => x k = false)).card +
      (Finset.univ.filter (fun x : Addr a => x k = true)).card =
      (Finset.univ : Finset (Addr a)).card := by
    have hpart := Finset.card_union_of_disjoint (s := Finset.univ.filter
        (fun x : Addr a => x k = false)) (t := Finset.univ.filter
        (fun x : Addr a => x k = true)) (by
      rw [Finset.disjoint_iff_inter_eq_empty]
      exact hdisj)
    rw [hunion] at hpart
    exact hpart.symm
  rw [Finset.card_univ, card_addr] at haddr
  have hbij := card_bit_slices k
  have hsub : Fintype.card (maskSlice k) =
      (Finset.univ.filter (fun x : Addr a => x k = false)).card :=
    Fintype.card_subtype (fun x : Addr a => x k = false)
  have ha : 0 < a := lt_of_le_of_lt (Nat.zero_le _) k.isLt
  have hpow : 2 ^ (a - 1 + 1) = 2 ^ (a - 1) * 2 := Nat.pow_succ _ _
  have haa : a - 1 + 1 = a := by omega
  rw [haa] at hpow
  omega

/-- The coset retraction at a mask bit `k` with `s k = true`: of `x` and its
translate `x ⊕ s`, keep the one reading `false` at `k`. -/
def pairRep (s : Addr a) (k : Fin a) : Addr a → Addr a :=
  fun x => if x k = true then maskAdd s x else x

/-- The retraction always lands in the transversal slice of `k`. -/
theorem pairRep_bit {s : Addr a} {k : Fin a} (hk : s k = true) (x : Addr a) :
    pairRep s k x k = false := by
  simp only [pairRep]
  by_cases hx : x k = true
  · rw [ite_eq_left hx]
    have hmk : maskAdd s x k = (x k ^^ s k : Bool) := rfl
    rw [hmk, hx, hk, Bool.xor_self]
  · rw [ite_eq_right hx]
    cases hxb : x k with
    | false => rfl
    | true => exact absurd hxb hx

/-- The retraction is translation-invariant: both elements of a coset retract
to the same transversal representative. -/
theorem pairRep_pair {s : Addr a} {k : Fin a} (hk : s k = true) (x : Addr a) :
    pairRep s k (maskAdd s x) = pairRep s k x := by
  have hbit : maskAdd s x k = !x k := by
    have hmk : maskAdd s x k = (x k ^^ s k : Bool) := rfl
    rw [hmk, hk, Bool.xor_true]
  cases hxb : x k with
  | true =>
      have h1 : ¬ ((maskAdd s x) k = true) := by rw [hbit, hxb]; simp
      simp only [pairRep, ite_eq_right h1, ite_eq_left hxb]
  | false =>
      have h1 : ((maskAdd s x) k) = true := by rw [hbit, hxb]; rfl
      have h2 : ¬ (x k = true) := by rw [hxb]; simp
      simp only [pairRep, ite_eq_left h1, ite_eq_right h2, maskAdd_self]

/-- The retraction fixes slice elements. -/
theorem pairRep_eq_of_bit_false {s : Addr a} {k : Fin a} (x : Addr a) (hx : x k = false) :
    pairRep s k x = x := by
  have h2 : ¬ (x k = true) := by rw [hx]; simp
  simp only [pairRep, ite_eq_right h2]

/-- The retraction sends bit-true addresses to their translate. -/
theorem pairRep_eq_of_bit_true {s : Addr a} {k : Fin a} (x : Addr a) (hx : x k = true) :
    pairRep s k x = maskAdd s x := by
  simp only [pairRep, ite_eq_left hx]

/-- Restriction to the transversal identifies the promise fiber with the
Boolean functions on the slice: a promised oracle is exactly its values on the
chosen coset representatives. -/
def fiberEquivSlice (s : Addr a) (k : Fin a) (hk : s k = true) :
    PromiseFiber s ≃ (maskSlice k → Bool) where
  toFun f := fun x => f.1 x.1
  invFun g :=
    ⟨fun y => g ⟨pairRep s k y, pairRep_bit hk y⟩, by
      intro y
      exact congrArg g (Subtype.ext (pairRep_pair hk y))⟩
  left_inv f := by
    refine Subtype.ext (funext fun y => ?_)
    show f.1 (pairRep s k y) = f.1 y
    by_cases hy : y k = true
    · rw [pairRep_eq_of_bit_true y hy]
      exact f.2 y
    · rw [pairRep_eq_of_bit_false y (by
        cases hyb : y k with
        | false => rfl
        | true => exact absurd hyb hy)]
  right_inv g := by
    funext x
    show g ⟨pairRep s k x.1, pairRep_bit hk x.1⟩ = g x
    exact congrArg g (Subtype.ext (pairRep_eq_of_bit_false x.1 x.2))

/-- The promise fiber at a nonzero mask has exactly `2 ^ 2 ^ (a - 1)` oracles:
one independent fair bit per two-point coset. -/
theorem promiseFiber_card {s : Addr a} (hs : s ≠ zeroAddr a) :
    Fintype.card (PromiseFiber s) = 2 ^ 2 ^ (a - 1) := by
  obtain ⟨k, hk⟩ := exists_bit_of_ne_zeroAddr hs
  have h1 : Fintype.card (PromiseFiber s) =
      Fintype.card (maskSlice k → Bool) :=
    Fintype.card_congr (fiberEquivSlice s k hk)
  rw [h1, Fintype.card_fun, Fintype.card_bool, maskSlice_card]

/-! ## The promised-oracle distribution -/

/-- The total mass of a constant over a finite set: the normalized count. -/
theorem sum_const_inv_card {ι : Type} (S : Finset ι) (N : ℕ) :
    ∑ _f ∈ S, ((N : ℝ))⁻¹ = ((S.card : ℝ)) * ((N : ℝ))⁻¹ := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert t S hS ih =>
      rw [Finset.sum_insert hS, Finset.card_insert_of_notMem hS, ih]
      push_cast
      ring

/-- The promised-oracle distribution: the uniform finite law on the promise
fiber of mask `s`, with zero mass off the fiber. This replaces the machine-success interface’s
uniform law over *all* Boolean oracles for the Simon setting. -/
noncomputable def promiseOracleLaw (s : Addr a) : FinDist (Addr a → Bool) where
  prob f :=
    if simonPromise s f then
      ((Finset.univ.filter (simonPromise s)).card : ℝ)⁻¹ else 0
  nonneg f := by
    by_cases h : simonPromise s f
    · rw [ite_eq_left h]
      positivity
    · rw [ite_eq_right h]
  sum_one := by
    have hpos : (0 : ℝ) < ((Finset.univ.filter (simonPromise s)).card : ℝ) := by
      exact_mod_cast promiseFiberCard_pos s
    rw [← Finset.sum_filter, sum_const_inv_card, mul_inv_cancel₀ (ne_of_gt hpos)]

/-- The mass of a promised oracle under the promised-oracle distribution. -/
theorem promiseOracleLaw_prob_of_mem {s : Addr a} {f : Addr a → Bool}
    (h : simonPromise s f) :
    (promiseOracleLaw s).prob f =
      ((Finset.univ.filter (simonPromise s)).card : ℝ)⁻¹ := by
  show (if simonPromise s f then
      ((Finset.univ.filter (simonPromise s)).card : ℝ)⁻¹ else 0) = _
  rw [ite_eq_left h]

/-- The mass of an oracle off the promise fiber is zero. -/
theorem promiseOracleLaw_prob_of_not_mem {s : Addr a} {f : Addr a → Bool}
    (h : ¬ simonPromise s f) : (promiseOracleLaw s).prob f = 0 := by
  show (if simonPromise s f then
      ((Finset.univ.filter (simonPromise s)).card : ℝ)⁻¹ else 0) = _
  rw [ite_eq_right h]

/-- Expectation under the promised-oracle distribution. -/
noncomputable def promiseOracleExpect (s : Addr a) (F : (Addr a → Bool) → ℝ) : ℝ :=
  FinDist.expect (promiseOracleLaw s) F

/-- The promise fiber identifies with its characteristic filter. -/
def fiberFilterEquiv (s : Addr a) :
    PromiseFiber s ≃ {f : Addr a → Bool // f ∈ Finset.univ.filter (simonPromise s)} where
  toFun p := ⟨p.1, Finset.mem_filter.2 ⟨Finset.mem_univ _, p.2⟩⟩
  invFun q := ⟨q.1, (Finset.mem_filter.1 q.2).2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- Summing over the promise fiber is summing over its characteristic filter. -/
theorem sum_promiseFiber (s : Addr a) (F : (Addr a → Bool) → ℝ) :
    ∑ f : PromiseFiber s, F f.1 = ∑ f ∈ Finset.univ.filter (simonPromise s), F f := by
  rw [Fintype.sum_equiv (fiberFilterEquiv s)
    (fun p : PromiseFiber s => F p.1)
    (fun q : {f : Addr a → Bool // f ∈ Finset.univ.filter (simonPromise s)} => F q.1)
    (fun _ => rfl)]
  exact Finset.sum_coe_sort _ _

/-- Expectation under the promised-oracle distribution is the normalized sum
over the promise fiber. -/
theorem promiseOracleExpect_eq_average (s : Addr a) (F : (Addr a → Bool) → ℝ) :
    promiseOracleExpect s F =
      (∑ f : PromiseFiber s, F f.1) /
        ((Finset.univ.filter (simonPromise s)).card : ℝ) := by
  have hit : ∀ f ∈ (Finset.univ : Finset (Addr a → Bool)),
      (promiseOracleLaw s).prob f * F f =
        if simonPromise s f then
          ((Finset.univ.filter (simonPromise s)).card : ℝ)⁻¹ * F f else 0 := by
    intro f _
    by_cases h : simonPromise s f
    · rw [promiseOracleLaw_prob_of_mem h, ite_eq_left h]
    · rw [promiseOracleLaw_prob_of_not_mem h, ite_eq_right h, zero_mul]
  unfold promiseOracleExpect FinDist.expect
  rw [Finset.sum_congr rfl hit, ← Finset.sum_filter, ← Finset.mul_sum,
    div_eq_mul_inv, sum_promiseFiber, mul_comm]

/-- The execution-derived success expectation under the promised-oracle draw:
the execution-derived success value averaged over the promise fiber. -/
noncomputable def promiseSuccess (accept : Conf a w → Bool) (P : Prog a w) (k : ℕ)
    (c : Conf a w) (s : Addr a) : ℝ :=
  promiseOracleExpect s (fun f => successValue accept f P k c)

/-- Promised-oracle success is the average of the deterministic execution
outcomes over the promise fiber. -/
theorem promiseSuccess_eq_average (accept : Conf a w → Bool) (P : Prog a w) (k : ℕ)
    (c : Conf a w) (s : Addr a) :
    promiseSuccess accept P k c s =
      (∑ f : PromiseFiber s, successValue accept f.1 P k c) /
        ((Finset.univ.filter (simonPromise s)).card : ℝ) :=
  promiseOracleExpect_eq_average s (fun f => successValue accept f P k c)

/-- Promised-oracle execution success is nonnegative. -/
theorem promiseSuccess_nonneg (accept : Conf a w → Bool) (P : Prog a w) (k : ℕ)
    (c : Conf a w) (s : Addr a) : 0 ≤ promiseSuccess accept P k c s := by
  unfold promiseSuccess promiseOracleExpect FinDist.expect
  exact Finset.sum_nonneg fun f _ =>
    mul_nonneg ((promiseOracleLaw s).nonneg f) (successValue_nonneg accept f P k c)

/-- Promised-oracle execution success is at most one. -/
theorem promiseSuccess_le_one (accept : Conf a w → Bool) (P : Prog a w) (k : ℕ)
    (c : Conf a w) (s : Addr a) : promiseSuccess accept P k c s ≤ 1 := by
  have hterm : ∀ f : Addr a → Bool,
      (promiseOracleLaw s).prob f * successValue accept f P k c ≤
      (promiseOracleLaw s).prob f * 1 := by
    intro f
    have hv := successValue_le_one accept f P k c
    have hp := (promiseOracleLaw s).nonneg f
    nlinarith
  unfold promiseSuccess promiseOracleExpect FinDist.expect
  calc (∑ f : Addr a → Bool, (promiseOracleLaw s).prob f * successValue accept f P k c) ≤
      ∑ f : Addr a → Bool, (promiseOracleLaw s).prob f * 1 :=
    Finset.sum_le_sum (fun f _ => hterm f)
  _ = 1 := by simpa using (promiseOracleLaw s).sum_one

/-! ## The transcript distribution law: first link of Theorem 9 -/

/-- Reduction of a single-draw event to a plain sum of masses: the probability
that the drawn oracle satisfies `Q` is the total mass of the `Q`-oracles. -/
theorem probEvent_one_eq_sum (s : Addr a) (Q : (Addr a → Bool) → Prop) [DecidablePred Q] :
    FinDist.probEvent (L := 1) (promiseOracleLaw s) (fun ω => Q (ω 0)) =
      ∑ f ∈ Finset.univ.filter Q, (promiseOracleLaw s).prob f := by
  have hpr : ∀ ω ∈ Finset.univ.filter (fun ω : Fin 1 → Addr a → Bool => Q (ω 0)),
      (promiseOracleLaw s).probOf ω = (promiseOracleLaw s).prob (ω 0) := by
    intro ω _
    exact Fin.prod_univ_one _
  unfold FinDist.probEvent
  rw [Finset.sum_congr rfl hpr]
  refine Finset.sum_nbij' (fun ω : Fin 1 → Addr a → Bool => ω 0)
    (fun f : Addr a → Bool => fun _ => f) ?_ ?_ ?_ ?_ ?_
  · intro ω hω
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hω).2⟩
  · intro f hf
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hf).2⟩
  · intro ω _
    funext i
    fin_cases i
    rfl
  · intro f _
    rfl
  · intro ω _
    rfl

/-- The distribution law of the promised-oracle draw: the probability of any
decidable oracle property is exactly the counting bound over the promise
fiber — the number of promised oracles with the property, divided by the
fiber size. This is the general form of Theorem 9's first link. -/
theorem probEvent_promise_eq (s : Addr a) (Q : (Addr a → Bool) → Prop) [DecidablePred Q] :
    FinDist.probEvent (L := 1) (promiseOracleLaw s) (fun ω => Q (ω 0)) =
      ((Finset.univ.filter (fun f => simonPromise s f ∧ Q f)).card : ℝ) /
        ((Finset.univ.filter (simonPromise s)).card : ℝ) := by
  rw [probEvent_one_eq_sum]
  have hit : ∀ f ∈ Finset.univ.filter Q, (promiseOracleLaw s).prob f =
      if simonPromise s f then
        ((Finset.univ.filter (simonPromise s)).card : ℝ)⁻¹ else 0 := by
    intro f _
    by_cases h : simonPromise s f
    · rw [promiseOracleLaw_prob_of_mem h, ite_eq_left h]
    · rw [promiseOracleLaw_prob_of_not_mem h, ite_eq_right h]
  rw [Finset.sum_congr rfl hit, ← Finset.sum_filter, Finset.filter_filter,
    Finset.filter_congr (fun f _ => and_comm), sum_const_inv_card, div_eq_mul_inv]

/-- The mass of an adaptive transcript: the probability that the execution-derived
execution-derived query/answer transcript of the machine run equals `T`, when
the consulted oracle is drawn from the promise fiber of `s`. -/
noncomputable def transcriptProb (s : Addr a) (P : Prog a w) (k : ℕ) (c : Conf a w)
    (T : List (Addr a × Bool)) : ℝ :=
  FinDist.probEvent (L := 1) (promiseOracleLaw s)
    (fun ω => oracleTranscript (ω 0) P k c = T)

/-- The transcript distribution law: the mass of an adaptive transcript is the
number of promised oracles that reproduce it, divided by the promise fiber
size. The transcript is produced by the real machine execution (`oracleTranscript`
of the machine-success interface), so this is the counting form of the first link of Theorem 9. -/
theorem transcriptProb_eq (s : Addr a) (P : Prog a w) (k : ℕ) (c : Conf a w)
    (T : List (Addr a × Bool)) :
    transcriptProb s P k c T =
      ((Finset.univ.filter
        (fun f => simonPromise s f ∧ oracleTranscript f P k c = T)).card : ℝ) /
        ((Finset.univ.filter (simonPromise s)).card : ℝ) :=
  probEvent_promise_eq s (fun f => oracleTranscript f P k c = T)

/-- Transcript masses are nonnegative. -/
theorem transcriptProb_nonneg (s : Addr a) (P : Prog a w) (k : ℕ) (c : Conf a w)
    (T : List (Addr a × Bool)) : 0 ≤ transcriptProb s P k c T := by
  rw [transcriptProb_eq]
  exact div_nonneg (Nat.cast_nonneg _)
    (by exact_mod_cast (promiseFiberCard_pos s).le)

/-- Transcript masses are at most one. -/
theorem transcriptProb_le_one (s : Addr a) (P : Prog a w) (k : ℕ) (c : Conf a w)
    (T : List (Addr a × Bool)) : transcriptProb s P k c T ≤ 1 := by
  exact probEvent_le_one _ _

/-- Answer agreement as decidable data: the oracle returns precisely the
recorded answer bit at every transcript entry. -/
def agreeWith (T : List (Addr a × Bool)) (f : Addr a → Bool) : Bool :=
  T.all (fun e => f e.1 == e.2)

/-- Answer agreement of a cons entry: the head comparison and the tail. -/
theorem agreeWith_cons (e : Addr a × Bool) (T : List (Addr a × Bool)) (f : Addr a → Bool) :
    agreeWith (e :: T) f = (f e.1 == e.2 && agreeWith T f) :=
  rfl

/-- Boolean form of answer agreement. -/
theorem agreeWith_iff (T : List (Addr a × Bool)) (f : Addr a → Bool) :
    agreeWith T f = true ↔ ∀ e ∈ T, f e.1 = e.2 := by
  rw [agreeWith, List.all_eq_true]
  constructor
  · intro h e he
    exact beq_iff_eq.mp (h e he)
  · intro h e he
    exact beq_iff_eq.mpr (h e he)

/-- Every entry of the execution-derived transcript records a genuine oracle
value: the consulted oracle agrees with its own transcript. -/
theorem oracleTranscript_agree (f : Addr a → Bool) (P : Prog a w) (k : ℕ) :
    ∀ c : Conf a w, agreeWith (oracleTranscript f P k c) f = true := by
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
      intro c
      by_cases h : instrAt P c.pc = Instr.oracle
      · have hEq : oracleTranscript f P (k + 1) c =
            (c.reg.1, f c.reg.1) :: oracleTranscript f P k (step f P c) := by
          simp [oracleTranscript, h]
        rw [hEq, agreeWith_cons, beq_self_eq_true, Bool.true_and]
        exact ih (step f P c)
      · have hEq : oracleTranscript f P (k + 1) c =
            oracleTranscript f P k (step f P c) := by simp [oracleTranscript, h]
        rw [hEq]
        exact ih (step f P c)

/-- The counting bound on transcript masses: the mass of a transcript is at
most the number of promised oracles answering consistently with it, over the
promise fiber size. Weaker than `transcriptProb_eq` in the numerator, but the
form the conditioning argument of Theorem 9 consumes. -/
theorem transcriptProb_le_agree (s : Addr a) (P : Prog a w) (k : ℕ) (c : Conf a w)
    (T : List (Addr a × Bool)) :
    transcriptProb s P k c T ≤
      ((Finset.univ.filter (fun f => simonPromise s f ∧ agreeWith T f)).card : ℝ) /
        ((Finset.univ.filter (simonPromise s)).card : ℝ) := by
  rw [transcriptProb_eq]
  have hsub : (Finset.univ.filter
      (fun f => simonPromise s f ∧ oracleTranscript f P k c = T)) ⊆
      Finset.univ.filter (fun f => simonPromise s f ∧ agreeWith T f) := by
    intro f hf
    obtain ⟨_, _, hfx⟩ := Finset.mem_filter.1 hf
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hf).2.1, ?_⟩
    have hagree := oracleTranscript_agree f P k c
    rw [hfx] at hagree
    exact hagree
  have hcast : (((Finset.univ.filter
      (fun f => simonPromise s f ∧ oracleTranscript f P k c = T)).card : ℝ) ≤
      ((Finset.univ.filter (fun f => simonPromise s f ∧ agreeWith T f)).card : ℝ)) :=
    by exact_mod_cast Finset.card_le_card hsub
  have hN : (0 : ℝ) ≤ ((Finset.univ.filter (simonPromise s)).card : ℝ) := by
    exact_mod_cast (promiseFiberCard_pos s).le
  exact div_le_div_of_nonneg_right hcast hN

/-! ## A fair coin per coset: uniformity of single readings -/

/-- Membership in the two-point coset `{x, x ⊕ s}`, phrased on translates. -/
theorem mem_pair_iff (s x y : Addr a) :
    (maskAdd s y = x ∨ maskAdd s y = maskAdd s x) ↔ (y = x ∨ y = maskAdd s x) := by
  constructor
  · rintro (h | h)
    · refine Or.inr ?_
      have h2 := congrArg (maskAdd s) h
      rwa [maskAdd_self] at h2
    · exact Or.inl (maskAdd_inj s h)
  · rintro (rfl | h)
    · exact Or.inr rfl
    · rw [h, maskAdd_self]
      exact Or.inl rfl

/-- The coset-exchange map: flip the oracle's values on the two-point coset
`{x, x ⊕ s}`, leave everything else unchanged. -/
def flipPair (s x : Addr a) (f : Addr a → Bool) : Addr a → Bool :=
  fun y => if y = x ∨ y = maskAdd s x then !f y else f y

/-- The coset-exchange map preserves the Simon promise: it flips whole coset
values, so the flipped oracle is still constant on cosets. -/
theorem flipPair_mem_promise {s x : Addr a} {f : Addr a → Bool}
    (h : simonPromise s f) : simonPromise s (flipPair s x f) := by
  intro y
  have key := mem_pair_iff s x y
  simp only [flipPair]
  by_cases hy : y = x ∨ y = maskAdd s x
  · rw [ite_eq_left (key.mpr hy), ite_eq_left hy, h y]
  · rw [ite_eq_right (fun hc => hy (key.mp hc)), ite_eq_right hy, h y]

/-- The coset exchange flips the reading at the pivot address. -/
theorem flipPair_at (s x : Addr a) (f : Addr a → Bool) :
    flipPair s x f x = !f x := by
  simp [flipPair]

/-- The coset exchange is an involution. -/
theorem flipPair_invol (s x : Addr a) (f : Addr a → Bool) :
    flipPair s x (flipPair s x f) = f := by
  funext y
  by_cases hy : y = x ∨ y = maskAdd s x
  · simp [flipPair, hy]
  · simp [flipPair, hy]

/-- The promised oracles reading `true` at a fixed address are as many as
those reading `false`: the coset exchange pairs them. -/
theorem promiseBit_card_eq (s : Addr a) (x : Addr a) :
    (Finset.univ.filter (fun f => simonPromise s f ∧ f x = true)).card =
      (Finset.univ.filter (fun f => simonPromise s f ∧ f x = false)).card := by
  refine Finset.card_bij' (fun f _ => flipPair s x f) (fun f _ => flipPair s x f)
    (fun f hf => ?_) (fun f hf => ?_) (fun f _ => flipPair_invol s x f)
    (fun f _ => flipPair_invol s x f)
  · obtain ⟨_, hp, hx⟩ := Finset.mem_filter.1 hf
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, flipPair_mem_promise hp, ?_⟩
    rw [flipPair_at, hx]
    exact Bool.not_true
  · obtain ⟨_, hp, hx⟩ := Finset.mem_filter.1 hf
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, flipPair_mem_promise hp, ?_⟩
    rw [flipPair_at, hx]
    exact Bool.not_false

/-- The single-reading fair-coin law: under the promised-oracle draw, the
oracle's value at any fixed address is a fair coin. This is the unconditional
seed of Theorem 9's conditioning argument. -/
theorem promiseBit_uniform (s : Addr a) (x : Addr a) (b : Bool) :
    FinDist.probEvent (L := 1) (promiseOracleLaw s) (fun ω => ω 0 x = b) = 1 / 2 := by
  have hlaw := probEvent_promise_eq s (fun f : Addr a → Bool => f x = b)
  simp only [hlaw]
  have hbij := promiseBit_card_eq s x
  have hsplit : (Finset.univ.filter (simonPromise s)).card =
      (Finset.univ.filter (fun f => simonPromise s f ∧ f x = true)).card +
      (Finset.univ.filter (fun f => simonPromise s f ∧ f x = false)).card := by
    have h : ((Finset.univ.filter (simonPromise s)).filter
          (fun f : Addr a → Bool => f x = true)).card +
        ((Finset.univ.filter (simonPromise s)).filter
          (fun f : Addr a → Bool => ¬ (f x = true))).card =
        (Finset.univ.filter (simonPromise s)).card :=
      Finset.card_filter_add_card_filter_not _
    have hfalse : Finset.univ.filter (fun f => simonPromise s f ∧ ¬ (f x = true)) =
        Finset.univ.filter (fun f => simonPromise s f ∧ f x = false) :=
      Finset.filter_congr fun f _ => by simp [Bool.not_eq_true]
    rw [Finset.filter_filter, Finset.filter_filter, hfalse] at h
    exact h.symm
  have hcount : (0 : ℝ) <
      ((Finset.univ.filter (fun f => simonPromise s f ∧ f x = b)).card : ℝ) := by
    have hmem : (fun _ : Addr a => b) ∈
        Finset.univ.filter (fun f => simonPromise s f ∧ f x = b) :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, simonPromise_const s b, rfl⟩
    exact_mod_cast Finset.card_pos.2 ⟨fun _ => b, hmem⟩
  have hY : ((Finset.univ.filter (simonPromise s)).card : ℝ) =
      2 * ((Finset.univ.filter (fun f => simonPromise s f ∧ f x = b)).card : ℝ) := by
    cases b
    · have h2 : 2 * (Finset.univ.filter (fun f => simonPromise s f ∧ f x = false)).card =
          (Finset.univ.filter (simonPromise s)).card := by omega
      exact_mod_cast h2.symm
    · have h2 : 2 * (Finset.univ.filter (fun f => simonPromise s f ∧ f x = true)).card =
          (Finset.univ.filter (simonPromise s)).card := by omega
      exact_mod_cast h2.symm
  rw [hY, div_eq_mul_inv, mul_inv, mul_left_comm,
    mul_inv_cancel₀ (ne_of_gt hcount)]
  norm_num

end Qatlib.Papers.ExactSimon97.PromiseOracle
