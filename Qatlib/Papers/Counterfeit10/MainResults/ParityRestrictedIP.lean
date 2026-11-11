/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

/-!
# Parity-restricted inner-product oracle (Counterfeit10, Lemma 1)

Formal companion to Iwama–Nishimura–Raymond–Teruyama, *Quantum Counterfeit Coin Problems*,
arXiv:1009.0416v1, Section 2 (`Lemma 1`) and Appendix A.

An `N`-coin oracle is a string `x : Fin N → Bool`, with `true` marking a counterfeit coin.
The inner-product (IP) oracle applies the phase `(-1)^{q·x} = ∏ i, (-1)^{x i && q i}` to a
query `q`.  The paper restricts to *parity-restricted* queries, i.e. query strings `q` of
even Hamming weight, and shows that one such query still identifies every oracle of weight
below `N/2`.

The proof has three steps, each formalised below.

* The character sum `Σ_{q even} (-1)^{q·z}` equals `2^{N-1}` when `z` is the all-fair or the
  all-counterfeit string and vanishes otherwise (`sum_even_ipPhase`).
* Consequently the amplitude of `|w⟩` in `H |ψ_x⟩`, where `|ψ_x⟩` is the uniform even-weight
  phase state, is `1/2` at `w = x` and at `w = x̄` and `0` elsewhere (`amp_eq_pair`).
* Distinct `x, y` of weight below `N/2` yield orthogonal amplitudes, because `x̄` has weight
  above `N/2` and so cannot coincide with either (`parityRestricted_orthonormal`).
-/

namespace Qatlib.Papers.Counterfeit10.MainResults

/-- An `N`-coin oracle string; `true` marks a counterfeit (false) coin. -/
abbrev CoinString (N : ℕ) := Fin N → Bool

/-- The number of counterfeit coins, i.e. the Hamming weight of the oracle string. -/
def coinWeight {N : ℕ} (x : CoinString N) : ℕ := (Finset.univ.filter fun i => x i).card

/-- The complementary oracle string `x̄`, obtained by swapping fair and counterfeit coins. -/
def compl {N : ℕ} (x : CoinString N) : CoinString N := fun i => !x i

/-- `z` is the all-fair string (no counterfeit coin). -/
abbrev IsZero {N : ℕ} (z : CoinString N) : Prop := ∀ i, z i = false

/-- `z` is the all-counterfeit string. -/
abbrev IsOne {N : ℕ} (z : CoinString N) : Prop := ∀ i, z i = true

/-- `x` and `w` agree on every coin. -/
abbrev SameEverywhere {N : ℕ} (x w : CoinString N) : Prop := ∀ i, x i = w i

/-- `x` and `w` disagree on every coin, i.e. `w` is the pointwise complement of `x`. -/
abbrev OppositeEverywhere {N : ℕ} (x w : CoinString N) : Prop := ∀ i, x i = !w i

/-- The Hamming weight is the sum of the per-coin indicators. -/
lemma coinWeight_eq_sum {N : ℕ} (x : CoinString N) :
    coinWeight x = ∑ i, (if x i then 1 else 0) := by
  rw [coinWeight, Finset.card_eq_sum_ones, Finset.sum_filter]

/-- `(-1)` raised to the Hamming weight factors as a product over the individual coins. -/
lemma pow_coinWeight {N : ℕ} (x : CoinString N) {R : Type*} [CommRing R] :
    (-1 : R) ^ coinWeight x = ∏ i, (if x i then (-1 : R) else 1) := by
  have key : ∀ s : Finset (Fin N),
      (-1 : R) ^ (∑ i ∈ s, (if x i then 1 else 0)) = ∏ i ∈ s, (if x i then -1 else 1) := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.prod_insert ha, pow_add, ih]
        by_cases h : x a <;> simp [h]
  simpa [coinWeight_eq_sum] using key Finset.univ

/-- A sum over the whole Boolean cube of a one-coordinate product factors into a product of one-coordinate sums. -/
lemma sum_prod_factor {N : ℕ} {R : Type*} [CommRing R] (g : Fin N → Bool → R) :
    (∑ q : CoinString N, ∏ i, g i (q i)) = ∏ i, (g i true + g i false) := by
  have h := Finset.sum_prod_piFinset (s := (Finset.univ : Finset Bool)) (g := g)
  rw [Fintype.piFinset_univ] at h
  simpa using h

/-- A product whose factors are each `2` or `0` equals `2^N` exactly when every factor is `2`, and `0` otherwise. -/
lemma prod_ite_two {N : ℕ} (p : Fin N → Prop) [DecidablePred p] :
    (∏ i : Fin N, (if p i then (2 : ℚ) else 0)) = if (∀ i, p i) then (2 : ℚ) ^ N else 0 := by
  by_cases h : ∀ i, p i
  · rw [if_pos h]
    have hstep : ∀ i : Fin N, (if p i then (2 : ℚ) else 0) = 2 := fun i => if_pos (h i)
    rw [Finset.prod_congr rfl (fun i _ => hstep i), Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, ¬ p i := by
      by_contra h'
      exact h fun i => by by_contra hi; exact h' ⟨i, hi⟩
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- Halving an indicator-weighted power of two subtracts one from the exponent. -/
lemma half_ite_pow {N : ℕ} (hN : 0 < N) (P : Prop) [Decidable P] :
    (if P then (2 : ℚ) ^ N else 0) / 2 = if P then (2 : ℚ) ^ (N - 1) else 0 := by
  by_cases h : P
  · rw [if_pos h, if_pos h]
    have hpow : (2 : ℚ) ^ (N - 1) = 2 ^ N / 2 := by
      cases N with
      | zero => exact absurd hN (Nat.lt_irrefl 0)
      | succ n => rw [Nat.add_sub_cancel]; ring
    rw [hpow]
  · rw [if_neg h, if_neg h]; ring

/-- The phase `(-1)^{q·x}` that the inner-product (IP) oracle applies to the query `q`. -/
noncomputable def ipPhase {N : ℕ} (x q : CoinString N) : ℚ :=
  ∏ i, if x i && q i then (-1 : ℚ) else 1

/-- The parity-restricted query set: all query strings of even Hamming weight (paper: `Q_even`). -/
noncomputable def evenQueries (N : ℕ) : Finset (CoinString N) :=
  Finset.univ.filter fun q => Even (coinWeight q)

/-- Summation of the IP phase over the entire cube: it is `2^N` for the all-fair string and `0` otherwise. -/
theorem sum_ipPhase_eq_indicator {N : ℕ} (z : CoinString N) :
    (∑ q : CoinString N, ipPhase z q) = if IsZero z then (2 : ℚ) ^ N else 0 := by
  have hfac : ∀ i : Fin N,
      ((if z i && true then (-1 : ℚ) else 1) + (if z i && false then (-1 : ℚ) else 1))
        = (if z i = false then 2 else 0) := by
    intro i; cases h : z i <;> norm_num [h]
  have hmain : (∑ q : CoinString N, ipPhase z q)
      = ∏ i, ((if z i && true then (-1 : ℚ) else 1) + (if z i && false then (-1 : ℚ) else 1)) := by
    unfold ipPhase
    exact sum_prod_factor (fun i b => if z i && b then (-1 : ℚ) else 1)
  rw [hmain, Finset.prod_congr rfl (fun i _ => hfac i)]
  exact prod_ite_two (fun i : Fin N => z i = false)

/-- The same cube sum with each query `q` additionally weighted by `(-1)^{wt(q)}`; it is `2^N` exactly for the all-counterfeit string. -/
theorem sum_twisted_ipPhase_eq_indicator {N : ℕ} (z : CoinString N) :
    (∑ q : CoinString N, (-1 : ℚ) ^ coinWeight q * ipPhase z q)
      = if IsOne z then (2 : ℚ) ^ N else 0 := by
  have hterm : ∀ q : CoinString N, (-1 : ℚ) ^ coinWeight q * ipPhase z q
      = ∏ i, (if q i then (-1 : ℚ) else 1) * (if z i && q i then (-1 : ℚ) else 1) := by
    intro q
    rw [pow_coinWeight (R := ℚ), ipPhase, Finset.prod_mul_distrib]
  rw [Finset.sum_congr rfl (fun q _ => hterm q)]
  have hmain : (∑ q : CoinString N,
        ∏ i, (if q i then (-1 : ℚ) else 1) * (if z i && q i then (-1 : ℚ) else 1))
      = ∏ i, (((if true then (-1 : ℚ) else 1) * (if z i && true then (-1 : ℚ) else 1))
          + ((if false then (-1 : ℚ) else 1) * (if z i && false then (-1 : ℚ) else 1))) :=
    sum_prod_factor (fun i b => (if b then (-1 : ℚ) else 1) * (if z i && b then (-1 : ℚ) else 1))
  rw [hmain]
  have hfac : ∀ i : Fin N,
      (((if true then (-1 : ℚ) else 1) * (if z i && true then (-1 : ℚ) else 1))
          + ((if false then (-1 : ℚ) else 1) * (if z i && false then (-1 : ℚ) else 1)))
        = (if z i = true then 2 else 0) := by
    intro i; cases h : z i <;> norm_num [h]
  rw [Finset.prod_congr rfl (fun i _ => hfac i)]
  exact prod_ite_two (fun i : Fin N => z i = true)

/-- The two-point cube sum of IP phases vanishes unless the two oracles coincide, where it is `2^N`. -/
theorem sum_prod_ipPhase_eq_indicator {N : ℕ} (x w : CoinString N) :
    (∑ q : CoinString N, ipPhase x q * ipPhase w q)
      = if SameEverywhere x w then (2 : ℚ) ^ N else 0 := by
  have hterm : ∀ q : CoinString N, ipPhase x q * ipPhase w q
      = ∏ i, (if x i && q i then (-1 : ℚ) else 1) * (if w i && q i then (-1 : ℚ) else 1) := by
    intro q; rw [ipPhase, ipPhase, Finset.prod_mul_distrib]
  rw [Finset.sum_congr rfl (fun q _ => hterm q)]
  rw [sum_prod_factor (fun i b =>
    (if x i && b then (-1 : ℚ) else 1) * (if w i && b then (-1 : ℚ) else 1))]
  have hfac : ∀ i : Fin N,
      ((if x i && true then (-1 : ℚ) else 1) * (if w i && true then (-1 : ℚ) else 1))
        + ((if x i && false then (-1 : ℚ) else 1) * (if w i && false then (-1 : ℚ) else 1))
      = (if x i = w i then (2 : ℚ) else 0) := by
    intro i; cases hx : x i <;> cases hw : w i <;> norm_num [hx, hw]
  rw [Finset.prod_congr rfl (fun i _ => hfac i)]
  exact prod_ite_two (fun i : Fin N => x i = w i)

/-- The twisted two-point cube sum of IP phases vanishes unless the two oracles are pointwise complementary. -/
theorem sum_twisted_prod_ipPhase_eq_indicator {N : ℕ} (x w : CoinString N) :
    (∑ q : CoinString N, (-1 : ℚ) ^ coinWeight q * (ipPhase x q * ipPhase w q))
      = if OppositeEverywhere x w then (2 : ℚ) ^ N else 0 := by
  have hterm : ∀ q : CoinString N, (-1 : ℚ) ^ coinWeight q * (ipPhase x q * ipPhase w q)
      = ∏ i, (if q i then (-1 : ℚ) else 1)
          * ((if x i && q i then (-1 : ℚ) else 1) * (if w i && q i then (-1 : ℚ) else 1)) := by
    intro q
    rw [pow_coinWeight (R := ℚ), ipPhase, ipPhase, Finset.prod_mul_distrib,
      Finset.prod_mul_distrib]
  rw [Finset.sum_congr rfl (fun q _ => hterm q)]
  rw [sum_prod_factor (fun i b => (if b then (-1 : ℚ) else 1)
    * ((if x i && b then (-1 : ℚ) else 1) * (if w i && b then (-1 : ℚ) else 1)))]
  have hfac : ∀ i : Fin N,
      ((if true then (-1 : ℚ) else 1)
          * ((if x i && true then (-1 : ℚ) else 1) * (if w i && true then (-1 : ℚ) else 1)))
        + ((if false then (-1 : ℚ) else 1)
          * ((if x i && false then (-1 : ℚ) else 1) * (if w i && false then (-1 : ℚ) else 1)))
      = (if x i = !w i then (2 : ℚ) else 0) := by
    intro i; cases hx : x i <;> cases hw : w i <;> norm_num [hx, hw]
  rw [Finset.prod_congr rfl (fun i _ => hfac i)]
  exact prod_ite_two (fun i : Fin N => x i = !w i)

/-- The indicator of even Hamming weight equals `(1 + (-1)^{wt(q)})/2`. -/
lemma even_indicator {N : ℕ} (q : CoinString N) :
    (if Even (coinWeight q) then (1 : ℚ) else 0) = (1 + (-1 : ℚ) ^ coinWeight q) / 2 := by
  rcases Nat.even_or_odd (coinWeight q) with h | h
  · rw [if_pos h, h.neg_one_pow]; ring
  · rw [if_neg (Nat.not_even_iff_odd.mpr h), h.neg_one_pow]; ring

/-- A sum over `Q_even` is the corresponding even-weight-indicator weighted sum over the whole cube. -/
lemma sum_evenQueries_eq {N : ℕ} (f : CoinString N → ℚ) :
    (∑ q ∈ evenQueries N, f q)
      = ∑ q : CoinString N, (if Even (coinWeight q) then (1 : ℚ) else 0) * f q := by
  rw [evenQueries, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  by_cases h : Even (coinWeight q) <;> simp [h]

/-- Even/odd decomposition of a cube sum: twice the even-weight part is the plain sum plus the `(-1)^{wt}`-twisted sum. -/
theorem even_odd_split {N : ℕ} (f : CoinString N → ℚ) :
    2 * (∑ q ∈ evenQueries N, f q)
      = (∑ q : CoinString N, f q) + (∑ q : CoinString N, (-1 : ℚ) ^ coinWeight q * f q) := by
  have hstep : ∀ q : CoinString N,
      2 * ((if Even (coinWeight q) then (1 : ℚ) else 0) * f q)
        = f q + (-1 : ℚ) ^ coinWeight q * f q := by
    intro q
    rw [even_indicator q]
    field_simp
  rw [sum_evenQueries_eq, Finset.mul_sum,
    Finset.sum_congr rfl (fun q _ => hstep q), Finset.sum_add_distrib]

/-- The character sum over parity-restricted queries: it is `2^{N-1}` for the all-fair and the all-counterfeit string and vanishes otherwise. -/
theorem sum_even_ipPhase {N : ℕ} (hN : 0 < N) (z : CoinString N) :
    (∑ q ∈ evenQueries N, ipPhase z q)
      = (if IsZero z then (2 : ℚ) ^ (N - 1) else 0)
        + (if IsOne z then (2 : ℚ) ^ (N - 1) else 0) := by
  have hsplit := even_odd_split (N := N) (fun q => ipPhase z q)
  rw [sum_ipPhase_eq_indicator, sum_twisted_ipPhase_eq_indicator] at hsplit
  have hS : (∑ q ∈ evenQueries N, ipPhase z q)
      = (if IsZero z then (2 : ℚ) ^ N else 0) / 2
        + (if IsOne z then (2 : ℚ) ^ N else 0) / 2 := by linarith
  rw [hS, half_ite_pow hN (IsZero z), half_ite_pow hN (IsOne z)]

/-- The two-point character sum over parity-restricted queries; it is `2^{N-1}` exactly when the two oracles agree or are pointwise complementary. -/
theorem sum_even_prod_ipPhase {N : ℕ} (hN : 0 < N) (x w : CoinString N) :
    (∑ q ∈ evenQueries N, ipPhase x q * ipPhase w q)
      = (if SameEverywhere x w then (2 : ℚ) ^ (N - 1) else 0)
        + (if OppositeEverywhere x w then (2 : ℚ) ^ (N - 1) else 0) := by
  have hsplit := even_odd_split (N := N) (fun q => ipPhase x q * ipPhase w q)
  rw [sum_prod_ipPhase_eq_indicator, sum_twisted_prod_ipPhase_eq_indicator] at hsplit
  have hS : (∑ q ∈ evenQueries N, ipPhase x q * ipPhase w q)
      = (if SameEverywhere x w then (2 : ℚ) ^ N else 0) / 2
        + (if OppositeEverywhere x w then (2 : ℚ) ^ N else 0) / 2 := by linarith
  rw [hS, half_ite_pow hN (SameEverywhere x w), half_ite_pow hN (OppositeEverywhere x w)]


/-- The amplitude of `|w⟩` in `H|ψ_x⟩`, where `|ψ_x⟩` is the uniform even-weight phase state of Lemma 1. -/
noncomputable def amp {N : ℕ} (x w : CoinString N) : ℚ :=
  ((2 : ℚ) ^ N)⁻¹ * ∑ q ∈ evenQueries N, ipPhase x q * ipPhase w q

/-- The unnormalised indicator of `z = x` or `z = x̄`, as a sum of the agreement and disagreement indicators. -/
noncomputable def pairInd {N : ℕ} (x z : CoinString N) : ℚ :=
  (if SameEverywhere x z then (1 : ℚ) else 0) + (if OppositeEverywhere x z then (1 : ℚ) else 0)

/-- The computational-basis delta `z ↦ [z = a]`. -/
noncomputable def basis {N : ℕ} (a z : CoinString N) : ℚ := if z = a then 1 else 0

/-- An indicator-weighted power of two factors as the power times the indicator of the condition. -/
lemma ite_pow_mul_ite (k : ℕ) (P : Prop) [Decidable P] :
    (if P then (2 : ℚ) ^ k else 0) = (2 : ℚ) ^ k * (if P then 1 else 0) := by
  by_cases h : P <;> simp [h]

/-- Complementing an oracle string replaces its weight by `N - wt(x)`. -/
lemma coinWeight_compl {N : ℕ} (x : CoinString N) : coinWeight (compl x) = N - coinWeight x := by
  have hstep : ∀ i : Fin N, ((if compl x i then 1 else 0) + (if x i then 1 else 0) : ℕ) = 1 := by
    intro i; cases h : x i <;> simp [compl, h]
  have hsum : coinWeight (compl x) + coinWeight x = N := by
    calc coinWeight (compl x) + coinWeight x
        = ∑ i : Fin N, ((if compl x i then 1 else 0) + (if x i then 1 else 0)) := by
          rw [coinWeight_eq_sum, coinWeight_eq_sum, ← Finset.sum_add_distrib]
      _ = ∑ _i : Fin N, 1 := Finset.sum_congr rfl (fun i _ => hstep i)
      _ = N := by simp
  omega

/-- Pointwise agreement with `x` characterises the single string `x`. -/
lemma same_iff_eq {N : ℕ} (x z : CoinString N) : SameEverywhere x z ↔ z = x := by
  constructor
  · intro h; exact funext fun i => (h i).symm
  · intro h i; rw [h]

/-- Pointwise disagreement with `x` characterises the single string `x̄`. -/
lemma opp_iff_eq_compl {N : ℕ} (x z : CoinString N) : OppositeEverywhere x z ↔ z = compl x := by
  unfold OppositeEverywhere compl
  constructor
  · intro h
    funext i
    simp [h i]
  · intro h i
    rw [h]
    simp

/-- The amplitude of `|w⟩` in `H|ψ_x⟩` is `1/2` at `w = x` and at `w = x̄`, and `0` elsewhere. -/
theorem amp_eq_pair {N : ℕ} (hN : 0 < N) (x w : CoinString N) :
    amp x w = pairInd x w / 2 := by
  rw [amp, sum_even_prod_ipPhase hN, pairInd]
  have hpow : (2 : ℚ) ^ (N - 1) = 2 ^ N / 2 := by
    cases N with
    | zero => exact absurd hN (Nat.lt_irrefl 0)
    | succ n => rw [Nat.add_sub_cancel]; ring
  rw [ite_pow_mul_ite (N - 1) (SameEverywhere x w),
    ite_pow_mul_ite (N - 1) (OppositeEverywhere x w), hpow]
  have hne : (2 : ℚ) ^ N ≠ 0 := by positivity
  field_simp

/-- The amplitude of `|w⟩` is the sum of two computational-basis deltas, at `x` and at `x̄`. -/
theorem amp_eq_basis {N : ℕ} (hN : 0 < N) (x z : CoinString N) :
    amp x z = (basis x z + basis (compl x) z) / 2 := by
  rw [amp_eq_pair hN]
  simp only [pairInd, same_iff_eq x z, opp_iff_eq_compl x z, basis]

/-- Two basis deltas are orthogonal unless they are the same delta. -/
lemma sum_basis_mul {N : ℕ} (a b : CoinString N) :
    (∑ z : CoinString N, basis a z * basis b z) = if a = b then 1 else 0 := by
  rw [Finset.sum_eq_single a]
  · unfold basis
    by_cases h : a = b <;> simp [h]
  · intro z _ hz
    unfold basis
    simp [hz]
  · intro h; exact absurd (Finset.mem_univ a) h

/-- Complementing twice returns the original oracle string. -/
lemma compl_compl {N : ℕ} (x : CoinString N) : compl (compl x) = x := by
  funext i; simp [compl]

/-- An oracle string of weight below `N/2` is not its own complement. -/
lemma ne_compl_self {N : ℕ} {x : CoinString N} (hx : coinWeight x < N / 2) : x ≠ compl x := by
  intro h
  have hw : coinWeight x = coinWeight (compl x) := congrArg coinWeight h
  rw [coinWeight_compl] at hw
  omega

/-- Two oracle strings of weight below `N/2` cannot be pointwise complementary. -/
lemma ne_compl_of_weight {N : ℕ} {x y : CoinString N}
    (hx : coinWeight x < N / 2) (hy : coinWeight y < N / 2) : x ≠ compl y := by
  intro h
  have hw : coinWeight x = N - coinWeight y := by rw [h, coinWeight_compl]
  omega

/-- Lemma 1 (arXiv:1009.0416v1, Section 2): a single parity-restricted IP query distinguishes every oracle of weight below `N/2`.  The amplitudes of the transformed states are orthonormal up to the common factor `1/2`. -/
theorem parityRestricted_orthonormal {N : ℕ} (hN : 0 < N) {x y : CoinString N}
    (hx : coinWeight x < N / 2) (hy : coinWeight y < N / 2) :
    (∑ z : CoinString N, amp x z * amp y z) = if x = y then (1 : ℚ) / 2 else 0 := by
  have hstep : ∀ z : CoinString N, amp x z * amp y z
      = (basis x z * basis y z + basis x z * basis (compl y) z
          + basis (compl x) z * basis y z + basis (compl x) z * basis (compl y) z) / 4 := by
    intro z
    rw [amp_eq_basis hN, amp_eq_basis hN]
    ring
  rw [Finset.sum_congr rfl (fun z _ => hstep z), ← Finset.sum_div]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [sum_basis_mul, sum_basis_mul, sum_basis_mul, sum_basis_mul]
  rcases eq_or_ne x y with hxy | hxy
  · subst hxy
    have hne : x ≠ compl x := ne_compl_self hx
    have hne' : compl x ≠ x := fun hc => hne hc.symm
    simp only [if_true, if_neg hne, if_neg hne']
    norm_num
  · have h1 : ¬ (x = compl y) := ne_compl_of_weight hx hy
    have h2 : ¬ (compl x = y) := fun hc => ne_compl_of_weight hy hx hc.symm
    have h3 : ¬ (compl x = compl y) := fun hc =>
      hxy (by rw [← compl_compl x, hc, compl_compl y])
    simp only [if_neg hxy, if_neg h1, if_neg h2, if_neg h3]
    norm_num

/-- Corollary of Lemma 1: the parity-restricted readout is injective on the set `S_{<N/2}`. -/
theorem parityRestricted_injective {N : ℕ} (hN : 0 < N) {x y : CoinString N}
    (hx : coinWeight x < N / 2) (hy : coinWeight y < N / 2)
    (hamp : (∑ z : CoinString N, amp x z * amp y z) ≠ 0) : x = y := by
  by_contra hxy
  exact hamp (by rw [parityRestricted_orthonormal hN hx hy, if_neg hxy])

/-- The all-fair oracle string. -/
def zeroString {N : ℕ} : CoinString N := fun _ => false

/-- The IP phase of the all-fair oracle is trivial. -/
lemma ipPhase_zero_left {N : ℕ} (q : CoinString N) : ipPhase (zeroString (N := N)) q = 1 := by
  unfold ipPhase zeroString
  simp

/-- There are exactly `2^{N-1}` parity-restricted queries, matching the paper's
`|Q_even| = 2^{N-1}`. -/
lemma evenQueries_card {N : ℕ} (hN : 0 < N) : (evenQueries N).card = 2 ^ (N - 1) := by
  have hsum : (∑ q ∈ evenQueries N, ipPhase (zeroString (N := N)) q)
      = ((evenQueries N).card : ℚ) := by
    rw [Finset.sum_congr rfl (fun q _ => ipPhase_zero_left q)]
    simp
  have h := sum_even_ipPhase hN (zeroString (N := N))
  rw [hsum] at h
  have hz : IsZero (zeroString (N := N)) := fun i => rfl
  have ho : ¬ IsOne (zeroString (N := N)) := by
    intro h1
    have := h1 ⟨0, hN⟩
    exact Bool.false_ne_true this
  rw [if_pos hz, if_neg ho, add_zero] at h
  have hcast : ((evenQueries N).card : ℚ) = ((2 ^ (N - 1) : ℕ) : ℚ) := by
    rw [h]; push_cast; ring
  exact_mod_cast hcast

end Qatlib.Papers.Counterfeit10.MainResults
