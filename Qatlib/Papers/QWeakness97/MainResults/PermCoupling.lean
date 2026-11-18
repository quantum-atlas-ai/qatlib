/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QWeakness97.MainResults.Theorem31Distance
public import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge

/-!
# Transposition coupling for random permutation oracles (Theorem 3.6 core)

Finite core of Theorem 3.6 of Bennett--Bernstein--Brassard--Vazirani
(quant-ph/9701001v1): a `T`-query machine interacting with permutation oracles
motivates the finite transposition-coupling estimates below. These estimates
use a finite basis space `I` and its in-place permutation action `permAct`;
this is a restricted model, without a source QTM address/answer/workspace bridge:

* two permutation oracles perturb any state by squared Euclidean distance at
  most four times the query mass on their disagreement set (`permDiff_le`);
* the transposition chain `pi_{k+1} = pi_k . (x_k x_{k+1})` of the source is
  `chainPerm`; its disagreement set against any later stage stays inside the
  fresh-string scope `{x_j : k <= j <= T'}` (`differScope`), and the preimage
  of the distinguished output tracks the fresh strings (`chainPreim`);
* a uniformly fresh string only ever carries its fair share of query mass
  (`sumFresh`), so the expected hybrid charge of the fresh scope is at most
  the number of scope pairs divided by `|I|`;
* the hybrid telescope against the mixed-schedule trajectory, combined with a
  Cauchy--Schwarz schedule as in the source, bounds the expected distance
  between the mixed-schedule run and the final fixed-oracle run by the explicit
  finite square-root sum (`avgDistPinned`);
* at least a quarter of all transposition schedules simultaneously keep the
  mixed-schedule and final fixed-oracle runs within `2/25` of each other and flip the
  first-bit-of-preimage language value (`thm36Core`).

The countable-QTM layer, all-lengths uniformity, the probability-one
statement, the source comparison of two adjacent fixed-oracle runs, and
the source's exact constants are not claimed. In particular this module does
not establish either Theorem 3.6 or Corollary 3.7.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace Qatlib.Papers.QWeakness97.MainResults.PermCoupling

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Papers.QWeakness97.MainResults
open scoped Classical BigOperators

variable {I : Type} [Fintype I] [DecidableEq I]

/-! ## Permutation oracles on amplitude vectors -/

/-- The action of a finite permutation oracle on amplitude vectors: the basis
state `y` is sent to the basis state `sigma y`. -/
def permAct (σ : I ≃ I) (ψ : QState I) : QState I := fun x => ψ (σ.symm x)

omit [DecidableEq I] in
/-- Applying a permutation oracle permutes the total squared mass. -/
theorem mass_permAct (σ : I ≃ I) (ψ : QState I) :
    ∑ x, ‖permAct σ ψ x‖ ^ 2 = ∑ x, ‖ψ x‖ ^ 2 :=
  Equiv.sum_comp σ.symm (fun x => ‖ψ x‖ ^ 2)

/-- Bound the squared distance of two complex amplitudes by their masses. -/
private theorem cmod_sub_sq_le (a b : ℂ) : ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have htri : ‖a - b‖ ≤ ‖a‖ + ‖b‖ := by
    calc ‖a - b‖ = ‖a + -b‖ := by rw [sub_eq_add_neg]
      _ ≤ ‖a‖ + ‖-b‖ := norm_add_le a (-b)
      _ = ‖a‖ + ‖b‖ := by rw [norm_neg]
  have h1 : ‖a - b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg (a - b)) htri 2
  have h2 : (‖a‖ + ‖b‖) ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
    nlinarith [sq_nonneg (‖a‖ - ‖b‖), norm_nonneg a, norm_nonneg b]
  linarith

/-- The set of addresses on which two permutation oracles answer differently. -/
def differSet (p q : I ≃ I) : Finset I := Finset.univ.filter (fun y => p y ≠ q y)

/-- Two permutation oracles perturb any state by squared Euclidean distance at
most four times the query mass on their disagreement set. -/
theorem permDiff_le (p q : I ≃ I) (ψ : QState I) :
    ∑ x, ‖permAct p ψ x - permAct q ψ x‖ ^ 2 ≤
      4 * ∑ y ∈ differSet p q, ‖ψ y‖ ^ 2 := by
  classical
  have hreindex : ∑ x, ‖permAct p ψ x - permAct q ψ x‖ ^ 2 =
      ∑ y, ‖permAct p ψ (p y) - permAct q ψ (p y)‖ ^ 2 :=
    (Fintype.sum_bijective p p.bijective
      (fun y => ‖permAct p ψ (p y) - permAct q ψ (p y)‖ ^ 2)
      (fun x => ‖permAct p ψ x - permAct q ψ x‖ ^ 2)
      (fun _ => rfl)).symm
  have hval : ∀ y, permAct p ψ (p y) = ψ y := by
    intro y
    unfold permAct
    rw [p.symm_apply_apply]
  have hterm : ∀ y, ‖permAct p ψ (p y) - permAct q ψ (p y)‖ ^ 2 ≤
      if p y ≠ q y then 2 * ‖ψ y‖ ^ 2 + 2 * ‖ψ (q.symm (p y))‖ ^ 2 else 0 := by
    intro y
    by_cases hne : p y ≠ q y
    · rw [hval]
      split
      · exact cmod_sub_sq_le (ψ y) (ψ (q.symm (p y)))
      · exact absurd hne (by assumption)
    · have hq : q.symm (p y) = y := by
        rw [not_not.1 hne, q.symm_apply_apply]
      have hq2 : permAct q ψ (p y) = ψ y := by
        unfold permAct
        rw [hq]
      rw [hval, hq2]
      split
      · exact absurd (by assumption) hne
      · rw [sub_self, norm_zero]
        norm_num
  have hfilter : ∑ y, (if p y ≠ q y then 2 * ‖ψ y‖ ^ 2 + 2 * ‖ψ (q.symm (p y))‖ ^ 2 else 0) =
      ∑ y ∈ differSet p q, (2 * ‖ψ y‖ ^ 2 + 2 * ‖ψ (q.symm (p y))‖ ^ 2) := by
    unfold differSet
    rw [← Finset.sum_filter]
  set σm : I ≃ I := p.trans q.symm with hσm
  have hσapp : ∀ y, σm y = q.symm (p y) := fun _ => rfl
  have hmem : ∀ y, y ∈ differSet p q ↔ σm y ∈ differSet p q := by
    intro y
    constructor
    · intro hy
      have hyne : p y ≠ q y := (Finset.mem_filter.mp hy).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      intro hcon
      refine hyne ?_
      have hqz : q (σm y) = p y := by rw [hσapp]; exact q.apply_symm_apply (p y)
      have hzy : σm y = y := p.injective (hcon.trans hqz)
      calc p y = q (σm y) := hqz.symm
        _ = q y := by rw [hzy]
    · intro hy
      have hyne : p (σm y) ≠ q (σm y) := (Finset.mem_filter.mp hy).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      by_contra hpy
      apply hyne
      have hzy : σm y = y := by
        refine q.injective ?_
        calc q (σm y) = p y := by rw [hσapp]; exact q.apply_symm_apply (p y)
          _ = q y := hpy
      rw [hzy]
      exact hpy
  have hσsum : ∑ y ∈ differSet p q, ‖ψ (σm y)‖ ^ 2 =
      ∑ z ∈ differSet p q, ‖ψ z‖ ^ 2 := by
    exact Finset.sum_bijective (fun y => σm y) σm.bijective hmem (fun y _ => rfl)
  calc ∑ x, ‖permAct p ψ x - permAct q ψ x‖ ^ 2
      = ∑ y, ‖permAct p ψ (p y) - permAct q ψ (p y)‖ ^ 2 := hreindex
    _ ≤ ∑ y, (if p y ≠ q y then 2 * ‖ψ y‖ ^ 2 + 2 * ‖ψ (q.symm (p y))‖ ^ 2 else 0) :=
        Finset.sum_le_sum (fun y _ => hterm y)
    _ = ∑ y ∈ differSet p q, (2 * ‖ψ y‖ ^ 2 + 2 * ‖ψ (q.symm (p y))‖ ^ 2) := hfilter
    _ = 2 * ∑ y ∈ differSet p q, ‖ψ y‖ ^ 2
          + 2 * ∑ y ∈ differSet p q, ‖ψ (q.symm (p y))‖ ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = 2 * ∑ y ∈ differSet p q, ‖ψ y‖ ^ 2 + 2 * ∑ z ∈ differSet p q, ‖ψ z‖ ^ 2 := by
        exact congrArg (fun t => 2 * ∑ y ∈ differSet p q, ‖ψ y‖ ^ 2 + 2 * t) hσsum
    _ = 4 * ∑ y ∈ differSet p q, ‖ψ y‖ ^ 2 := by ring

/-! ## The transposition chain of the source proof -/

/-- The transposition chain of Theorem 3.6: fresh strings `x_0, x_1, ...` are
drawn and the oracle is updated by `pi_{k+1} = pi_k . (x_k x_{k+1})`. -/
def chainPerm (π0 : I ≃ I) (xs : ℕ → I) : ℕ → I ≃ I
  | 0 => π0
  | k + 1 => (Equiv.swap (xs k) (xs (k + 1))).trans (chainPerm π0 xs k)

omit [Fintype I] in
/-- The chain starts at its supplied seed permutation. -/
@[simp]
theorem chainPerm_zero (π0 : I ≃ I) (xs : ℕ → I) : chainPerm π0 xs 0 = π0 := rfl

omit [Fintype I] in
/-- Each chain step precomposes its predecessor with the next transposition. -/
@[simp]
theorem chainPerm_succ (π0 : I ≃ I) (xs : ℕ → I) (k : ℕ) :
    chainPerm π0 xs (k + 1) =
      (Equiv.swap (xs k) (xs (k + 1))).trans (chainPerm π0 xs k) := rfl

omit [Fintype I] in
/-- The chain depends on the drawn strings only through coordinates at most
`k`. -/
theorem chainPerm_congr (π0 : I ≃ I) {xs xs' : ℕ → I} : ∀ (k : ℕ),
    (∀ t, t ≤ k → xs t = xs' t) → chainPerm π0 xs k = chainPerm π0 xs' k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
      intro h
      rw [chainPerm_succ, chainPerm_succ]
      rw [h k (by omega), h (k + 1) (le_refl _), ih (fun t ht => h t (by omega))]

omit [Fintype I] in
/-- The disagreement set of the chain's final stage against its `k`-th stage
stays inside the fresh strings `x_j` with `k <= j <= m`; this is the scope
`S` of the source proof. -/
theorem differScope (π0 : I ≃ I) (xs : ℕ → I) : ∀ (m k : ℕ), k ≤ m → ∀ y,
    chainPerm π0 xs m y ≠ chainPerm π0 xs k y → ∃ j, k ≤ j ∧ j ≤ m ∧ y = xs j := by
  intro m
  induction m with
  | zero =>
      intro k hk y hne
      have hk0 : k = 0 := Nat.le_zero.1 hk
      subst hk0
      exact absurd rfl hne
  | succ m ih =>
      intro k hk y hne
      by_cases hkm : k ≤ m
      · by_cases hy : y = xs m ∨ y = xs (m + 1)
        · rcases hy with h | h
          · exact ⟨m, by omega, by omega, h⟩
          · exact ⟨m + 1, by omega, by omega, h⟩
        · have h1 : y ≠ xs m := fun h => hy (Or.inl h)
          have h2 : y ≠ xs (m + 1) := fun h => hy (Or.inr h)
          have hyval : Equiv.swap (xs m) (xs (m + 1)) y = y :=
            Equiv.swap_apply_of_ne_of_ne h1 h2
          rw [chainPerm_succ, Equiv.trans_apply, hyval] at hne
          obtain ⟨j, hj1, hj2, hj3⟩ := ih k hkm y hne
          exact ⟨j, hj1, by omega, hj3⟩
      · have hke : k = m + 1 := by omega
        subst hke
        exact absurd rfl hne

omit [Fintype I] in
/-- If the seed permutation sends the drawn `x_0` to the distinguished output
`y₀`, the image of each drawn string `x_k` under the `k`-th chain permutation
is exactly `y₀`; the language bit at `y₀` therefore tracks the fresh strings,
and it is the preimage because permutations are injective. -/
theorem chainPreim (π0 : I ≃ I) (xs : ℕ → I) (y₀ : I) (h0 : π0 (xs 0) = y₀) :
    ∀ k, chainPerm π0 xs k (xs k) = y₀ := by
  intro k
  induction k with
  | zero => exact h0
  | succ k ih =>
      rw [chainPerm_succ, Equiv.trans_apply]
      by_cases hk : xs (k + 1) = xs k
      · have hsw : Equiv.swap (xs k) (xs (k + 1)) = Equiv.refl I := by
          rw [hk]
          exact Equiv.swap_self (xs k)
        rw [hsw, Equiv.refl_apply, hk]
        exact ih
      · rw [Equiv.swap_apply_right (xs k) (xs (k + 1))]
        exact ih

/-! ## Query runs with a schedule of permutation oracles -/

/-- A `T`-step run whose step `k` consults the permutation oracle `o k` and
then applies the interleaving matrix `U k`. -/
noncomputable def oracleRun (o : ℕ → I ≃ I) (U : ℕ → Matrix I I ℂ)
    (init : QState I) : ℕ → QState I
  | 0 => init
  | k + 1 => ApplyGate (U k) (permAct (o k) (oracleRun o U init k))

omit [DecidableEq I] in
/-- The run state at step `i` depends only on the first `i` oracles. -/
theorem oracleRun_congr {o o' : ℕ → I ≃ I} {U : ℕ → Matrix I I ℂ} {init : QState I}
    {i : ℕ} (h : ∀ k, k < i → o k = o' k) :
    oracleRun o U init i = oracleRun o' U init i := by
  induction i with
  | zero => rfl
  | succ i ih =>
      have hstep : o i = o' i := h i (by omega)
      rw [oracleRun, oracleRun, hstep, ih (fun k hk => h k (by omega))]

/-- Unitary interleavings and permutation oracles preserve the total squared
mass of the run state. -/
theorem mass_oracleRun (o : ℕ → I ≃ I) (U : ℕ → Matrix I I ℂ)
    (hU : ∀ k, U k ∈ Matrix.unitaryGroup I ℂ) (init : QState I) : ∀ k,
    ∑ x, ‖oracleRun o U init k x‖ ^ 2 = ∑ x, ‖init x‖ ^ 2 := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      have h1 : ∑ x, ‖oracleRun o U init (k + 1) x‖ ^ 2
          = ∑ x, ‖((U k) *ᵥ (permAct (o k) (oracleRun o U init k))) x‖ ^ 2 := rfl
      rw [h1]
      simp_rw [← Complex.normSq_eq_norm_sq]
      rw [sum_normSq_mulVec_of_mem_unitaryGroup (hU k)]
      simp_rw [Complex.normSq_eq_norm_sq, mass_permAct, ih]

omit [DecidableEq I] in
/-- In-place permutation action preserves Euclidean norm. -/
private theorem permPres (σ : I ≃ I) (v : QState I) :
    ‖toEuclidean_fromVec (permAct σ v)‖ = ‖toEuclidean_fromVec v‖ := by
  have h : ‖toEuclidean_fromVec (permAct σ v)‖ ^ 2 = ‖toEuclidean_fromVec v‖ ^ 2 := by
    rw [norm_toEuclidean_fromVec_sq, norm_toEuclidean_fromVec_sq, mass_permAct]
  have h2 := congrArg Real.sqrt h
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h2

/-- A unitary interleaving preserves Euclidean norm. -/
private theorem gatePres {U : Matrix I I ℂ} (hU : U ∈ Matrix.unitaryGroup I ℂ)
    (v : QState I) :
    ‖toEuclidean_fromVec (ApplyGate U v)‖ = ‖toEuclidean_fromVec v‖ := by
  have h : ‖toEuclidean_fromVec (ApplyGate U v)‖ ^ 2 = ‖toEuclidean_fromVec v‖ ^ 2 := by
    rw [norm_toEuclidean_fromVec_sq, norm_toEuclidean_fromVec_sq]
    simp only [ApplyGate]
    simp_rw [← Complex.normSq_eq_norm_sq]
    exact sum_normSq_mulVec_of_mem_unitaryGroup hU v
  have h2 := congrArg Real.sqrt h
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h2

omit [DecidableEq I] in
/-- Matrix application distributes over subtraction. -/
private theorem gate_sub (U : Matrix I I ℂ) (a b : QState I) :
    ApplyGate U (a - b) = ApplyGate U a - ApplyGate U b := Matrix.mulVec_sub U a b

omit [DecidableEq I] in
/-- Matrix application distributes over addition. -/
private theorem gate_add (U : Matrix I I ℂ) (a b : QState I) :
    ApplyGate U (a + b) = ApplyGate U a + ApplyGate U b := Matrix.mulVec_add U a b

omit [Fintype I] [DecidableEq I] in
/-- The Euclidean representation respects vector addition. -/
private theorem toLp_add (a b : QState I) :
    toEuclidean_fromVec (a + b) = toEuclidean_fromVec a + toEuclidean_fromVec b := by
  simp only [toEuclidean_fromVec, WithLp.toLp_add]

/-- The hybrid telescope: the mixed-schedule run stays within the sum over the
steps of the oracle deviation of the mixed trajectory, `permAct (o k) - permAct`
applied to the mixed state before the step. -/
theorem hybDist (o : ℕ → I ≃ I) (σ : I ≃ I) (U : ℕ → Matrix I I ℂ)
    (hU : ∀ k, U k ∈ Matrix.unitaryGroup I ℂ) (init : QState I) : ∀ T,
    ‖toEuclidean_fromVec (oracleRun o U init T - oracleRun (fun _ => σ) U init T)‖ ≤
      ∑ k ∈ Finset.range T, ‖toEuclidean_fromVec (permAct (o k) (oracleRun o U init k)
        - permAct σ (oracleRun o U init k))‖ := by
  intro T
  induction T with
  | zero =>
      show ‖toEuclidean_fromVec (init - init)‖ ≤ ∑ _k ∈ Finset.range 0, _
      rw [sub_self]
      have hz : (toEuclidean_fromVec (I := I) 0) = 0 := rfl
      rw [hz, norm_zero]
      norm_num
  | succ T ih =>
      set ψ := oracleRun o U init T with hψ
      set φ := oracleRun (fun _ => σ) U init T with hφ
      have hrun : oracleRun o U init (T + 1) - oracleRun (fun _ => σ) U init (T + 1)
          = ApplyGate (U T) (permAct (o T) ψ) - ApplyGate (U T) (permAct σ φ) := rfl
      have hsplit : ApplyGate (U T) (permAct (o T) ψ) - ApplyGate (U T) (permAct σ φ)
          = ApplyGate (U T) (permAct σ (ψ - φ)
            + (permAct (o T) ψ - permAct σ ψ)) := by
        rw [← gate_sub]
        congr 1
        funext x
        simp only [permAct, Pi.add_apply, Pi.sub_apply]
        ring
      have htoLp : toEuclidean_fromVec (ApplyGate (U T) (permAct σ (ψ - φ)
            + (permAct (o T) ψ - permAct σ ψ)))
          = toEuclidean_fromVec (ApplyGate (U T) (permAct σ (ψ - φ)))
            + toEuclidean_fromVec (ApplyGate (U T) (permAct (o T) ψ - permAct σ ψ)) := by
        rw [gate_add]
        exact toLp_add _ _
      rw [hrun, hsplit, htoLp]
      calc ‖toEuclidean_fromVec (ApplyGate (U T) (permAct σ (ψ - φ)))
            + toEuclidean_fromVec (ApplyGate (U T) (permAct (o T) ψ - permAct σ ψ))‖
            ≤ ‖toEuclidean_fromVec (ApplyGate (U T) (permAct σ (ψ - φ)))‖
              + ‖toEuclidean_fromVec (ApplyGate (U T) (permAct (o T) ψ - permAct σ ψ))‖ :=
                norm_add_le _ _
          _ = ‖toEuclidean_fromVec (permAct σ (ψ - φ))‖
              + ‖toEuclidean_fromVec (permAct (o T) ψ - permAct σ ψ)‖ := by
                rw [gatePres (hU T), gatePres (hU T)]
          _ = ‖toEuclidean_fromVec (ψ - φ)‖
              + ‖toEuclidean_fromVec (permAct (o T) ψ - permAct σ ψ)‖ := by
                rw [permPres]
          _ ≤ (∑ k ∈ Finset.range T, ‖toEuclidean_fromVec (permAct (o k)
                (oracleRun o U init k) - permAct σ (oracleRun o U init k))‖)
              + ‖toEuclidean_fromVec (permAct (o T) ψ - permAct σ ψ)‖ :=
                add_le_add ih (le_refl _)
          _ = ∑ k ∈ Finset.range (T + 1), ‖toEuclidean_fromVec (permAct (o k)
                (oracleRun o U init k) - permAct σ (oracleRun o U init k))‖ := by
                rw [Finset.range_add_one,
                  Finset.sum_insert (by simp [Finset.mem_range])]
                exact (add_comm _ _).symm

/-! ## Fresh-coordinate averaging -/

/-- Append a value at the last coordinate. -/
def snocf {n : ℕ} (u : Fin n → I) (a : I) : Fin (n + 1) → I :=
  fun i => if h : (i : ℕ) < n then u ⟨i, h⟩ else a

omit [Fintype I] [DecidableEq I] in
/-- Appending a coordinate leaves every earlier coordinate unchanged. -/
theorem snocf_lt {n : ℕ} (u : Fin n → I) (a : I) (i : Fin n) :
    snocf u a i.castSucc = u i := by
  have hlt : ((i.castSucc : Fin (n + 1)) : ℕ) < n := i.isLt
  show (if h' : ((i.castSucc : Fin (n + 1)) : ℕ) < n then u ⟨_, h'⟩ else a) = u i
  rw [dite_eq_left hlt]
  exact congrArg u (Fin.ext rfl)

omit [Fintype I] [DecidableEq I] in
/-- The appended coordinate is the last coordinate. -/
theorem snocf_last {n : ℕ} (u : Fin n → I) (a : I) : snocf u a (Fin.last n) = a := by
  have h : ¬ ((Fin.last n : Fin (n + 1)) : ℕ) < n := by simp
  show (if h' : ((Fin.last n : Fin (n + 1)) : ℕ) < n then u ⟨_, h'⟩ else a) = a
  exact dite_eq_right h

/-- Split a function on `Fin (n+1)` into its restriction and its last value. -/
def splitLast {n : ℕ} : (Fin (n + 1) → I) ≃ (Fin n → I) × I where
  toFun r := (fun i => r i.castSucc, r (Fin.last n))
  invFun p := snocf p.1 p.2
  left_inv r := by
    funext i
    show snocf (fun i => r i.castSucc) (r (Fin.last n)) i = r i
    by_cases h : (i : ℕ) < n
    · have hi : i = (⟨i, h⟩ : Fin n).castSucc := Fin.ext rfl
      rw [hi, snocf_lt]
    · have hi : i = Fin.last n :=
        Fin.ext (by have h1 := i.isLt; have h2 : (Fin.last n).val = n := rfl; omega)
      subst hi
      rw [snocf_last]
  right_inv p := by
    obtain ⟨u, a⟩ := p
    show (fun i => snocf u a i.castSucc, snocf u a (Fin.last n)) = (u, a)
    have h1 : (fun i => snocf u a i.castSucc) = u := by
      funext i
      rw [snocf_lt]
    have h2 : snocf u a (Fin.last n) = a := snocf_last u a
    rw [h1, h2]

omit [DecidableEq I] in
/-- If `f r` does not depend on the last coordinate of `r`, a uniformly drawn
last coordinate only carries its fair share of the mass of `f r`. -/
theorem sumFreshLast {n : ℕ} [Nonempty I] (f : (Fin (n + 1) → I) → I → ℂ)
    (hind : ∀ u : Fin n → I, ∀ c c', f (snocf u c) = f (snocf u c'))
    (B : ℝ) (hB : ∀ r, ∑ c, ‖f r c‖ ^ 2 ≤ B) :
    ∑ r : Fin (n + 1) → I, ‖f r (r (Fin.last n))‖ ^ 2 ≤
      B * (Fintype.card I) ^ n := by
  classical
  have hstep : ∑ r : Fin (n + 1) → I, ‖f r (r (Fin.last n))‖ ^ 2
      ≤ ∑ u : Fin n → I, B := by
    have hconv : ∑ r : Fin (n + 1) → I, ‖f r (r (Fin.last n))‖ ^ 2
        = ∑ p : (Fin n → I) × I, ‖f (snocf p.1 p.2) p.2‖ ^ 2 :=
      Fintype.sum_equiv splitLast _ _ (fun r => by
        show ‖f r (r (Fin.last n))‖ ^ 2
          = ‖f (snocf (fun i => r i.castSucc) (r (Fin.last n))) (r (Fin.last n))‖ ^ 2
        exact congrArg (fun v => ‖f v (r (Fin.last n))‖ ^ 2)
          (splitLast.left_inv r).symm)
    refine le_trans (le_of_eq hconv) ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_le_sum fun u _ => ?_
    obtain ⟨c₀⟩ := ‹Nonempty I›
    calc ∑ c, ‖f (snocf u c) c‖ ^ 2
          = ∑ c, ‖f (snocf u c₀) c‖ ^ 2 :=
            Finset.sum_congr rfl (fun c _ => by rw [hind u c c₀])
        _ ≤ B := hB (snocf u c₀)
  calc ∑ r : Fin (n + 1) → I, ‖f r (r (Fin.last n))‖ ^ 2
      ≤ ∑ _u : Fin n → I, B := hstep
    _ = B * Fintype.card (Fin n → I) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
    _ = B * (Fintype.card I) ^ n := by
        rw [Fintype.card_pi]
        simp

/-- Move coordinate `j` to the last position by conjugating with the
transposition of `j` and the last index. -/
def toLast {n : ℕ} (j : Fin (n + 1)) : (Fin (n + 1) → I) ≃ (Fin (n + 1) → I) where
  toFun r k := r (Equiv.swap j (Fin.last n) k)
  invFun s k := s (Equiv.swap j (Fin.last n) k)
  left_inv r := by
    funext k
    simp only [Equiv.swap_apply_self]
  right_inv s := by
    funext k
    simp only [Equiv.swap_apply_self]

omit [Fintype I] [DecidableEq I] in
/-- Moving a coordinate to the last position returns that coordinate there. -/
theorem toLast_last {n : ℕ} (j : Fin (n + 1)) (r : Fin (n + 1) → I) :
    toLast j r (Fin.last n) = r j := by
  show r (Equiv.swap j (Fin.last n) (Fin.last n)) = r j
  rw [Equiv.swap_apply_right j (Fin.last n)]

omit [Fintype I] [DecidableEq I] in
/-- The coordinate transposition is its own inverse. -/
theorem toLast_symm {n : ℕ} (j : Fin (n + 1)) (s : Fin (n + 1) → I) (k : Fin (n + 1)) :
    (toLast j).symm s k = s (Equiv.swap j (Fin.last n) k) := rfl

omit [DecidableEq I] in
/-- If `f r` does not depend on the `j`-th coordinate of `r`, a uniformly drawn
`j`-th coordinate only carries its fair share of the mass of `f r`. -/
theorem sumFresh {n : ℕ} [Nonempty I] (j : Fin (n + 1)) (f : (Fin (n + 1) → I) → I → ℂ)
    (hind : ∀ r c, f (Function.update r j c) = f r)
    (B : ℝ) (hB : ∀ r, ∑ c, ‖f r c‖ ^ 2 ≤ B) :
    ∑ r : Fin (n + 1) → I, ‖f r (r j)‖ ^ 2 ≤ B * (Fintype.card I) ^ n := by
  classical
  set F : (Fin (n + 1) → I) → I → ℂ := fun s => f ((toLast j).symm s) with hF
  have hmain : ∑ r : Fin (n + 1) → I, ‖f r (r j)‖ ^ 2
      = ∑ s : Fin (n + 1) → I, ‖F s (s (Fin.last n))‖ ^ 2 := by
    refine Fintype.sum_equiv (toLast j) _ _ ?_
    intro r
    have hli : (toLast j).symm ((toLast j) r) = r := (toLast j).left_inv r
    have hlast : (toLast j) r (Fin.last n) = r j := toLast_last j r
    show ‖f r (r j)‖ ^ 2 = ‖F ((toLast j) r) ((toLast j) r (Fin.last n))‖ ^ 2
    rw [hlast]
    exact congrArg (fun v => ‖f v (r j)‖ ^ 2) hli.symm
  have he : ∀ p : Fin (n + 1), Equiv.swap j (Fin.last n) p = Fin.last n ↔ p = j := by
    intro p
    constructor
    · intro h
      have h2 := Equiv.swap_apply_eq_iff.mp h
      simpa using h2
    · intro h
      rw [h]
      exact Equiv.swap_apply_left j (Fin.last n)
  have hdiffer : ∀ u : Fin n → I, ∀ c c',
      (toLast j).symm (snocf u c)
        = Function.update ((toLast j).symm (snocf u c')) j c := by
    intro u c c'
    funext p
    rw [Function.update_apply, toLast_symm, toLast_symm]
    by_cases hp : p = j
    · have hs : Equiv.swap j (Fin.last n) p = Fin.last n := by
        rw [hp]
        exact Equiv.swap_apply_left j (Fin.last n)
      rw [hs, hp, ite_eq_left rfl, snocf_last]
    · have hs : ¬ (Equiv.swap j (Fin.last n) p = Fin.last n) := fun h => hp ((he p).1 h)
      rw [ite_eq_right hp]
      have hlt : ((Equiv.swap j (Fin.last n) p : Fin (n + 1)) : ℕ) < n := by
        rcases Nat.lt_or_ge ((Equiv.swap j (Fin.last n) p : Fin (n + 1)) : ℕ) n with h | h
        · exact h
        · have hge := (Equiv.swap j (Fin.last n) p).isLt.le
          have hlastval : ((Fin.last n : Fin (n + 1)) : ℕ) = n := rfl
          exact absurd (Fin.ext (by omega)) hs
      rw [snocf, snocf, dite_eq_left hlt, dite_eq_left hlt]
  have hindLast : ∀ u : Fin n → I, ∀ c c', F (snocf u c) = F (snocf u c') := by
    intro u c c'
    show f ((toLast j).symm (snocf u c)) = f ((toLast j).symm (snocf u c'))
    rw [hdiffer u c c', hind]
  have hBF : ∀ r, ∑ c, ‖F r c‖ ^ 2 ≤ B := fun r => hB ((toLast j).symm r)
  rw [hmain]
  exact sumFreshLast F hindLast B hBF

/-! ## Expected hybrid charge and expected distance -/

/-- Bound a finite sum of square roots by its total mass and cardinality. -/
private theorem sumSqrtCard {α : Type} [Fintype α] (m : α → ℝ) (hm : ∀ r, 0 ≤ m r) :
    (∑ r, Real.sqrt (m r)) ^ 2 ≤ (Fintype.card α) * ∑ r, m r := by
  classical
  have hpair : ∀ r r', Real.sqrt (m r) * Real.sqrt (m r') ≤ (m r + m r') / 2 := by
    intro r r'
    have h3 : Real.sqrt (m r) * Real.sqrt (m r') = Real.sqrt (m r * m r') :=
      (Real.sqrt_mul (hm r) (m r')).symm
    rw [h3]
    have h4 : m r * m r' ≤ (m r + m r') ^ 2 / 4 := by
      nlinarith [sq_nonneg (m r - m r'), hm r, hm r']
    have h5 : Real.sqrt (m r * m r') ≤ Real.sqrt ((m r + m r') ^ 2 / 4) :=
      Real.sqrt_le_sqrt h4
    have h6 : Real.sqrt ((m r + m r') ^ 2 / 4) = (m r + m r') / 2 := by
      have hnn : 0 ≤ m r + m r' := add_nonneg (hm r) (hm r')
      rw [Real.sqrt_div (sq_nonneg (m r + m r')), Real.sqrt_sq hnn,
        show ((4 : ℝ)) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [h6] at h5
    exact h5
  have hswap : ∑ r : α, ∑ r' : α, (m r + m r') / 2 = (Fintype.card α : ℝ) * ∑ r : α, m r := by
    have e1 : ∀ r : α, ∑ r' : α, (m r + m r') / 2
        = ((Fintype.card α : ℝ) * m r + ∑ r' : α, m r') / 2 := by
      intro r
      rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
        Finset.card_univ]
    have hsplit : ∑ r : α, ((Fintype.card α : ℝ) * m r + ∑ r' : α, m r') / 2
        = ((Fintype.card α : ℝ) * ∑ r : α, m r + ∑ r : α, ∑ r' : α, m r') / 2 := by
      rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.mul_sum]
    have e2 : ∑ r : α, ∑ r' : α, m r' = (Fintype.card α : ℝ) * ∑ r : α, m r := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.mul_sum, Finset.card_univ]
    calc ∑ r : α, ∑ r' : α, (m r + m r') / 2
        = ∑ r : α, ((Fintype.card α : ℝ) * m r + ∑ r' : α, m r') / 2 :=
          Finset.sum_congr rfl (fun r _ => e1 r)
      _ = ((Fintype.card α : ℝ) * ∑ r : α, m r + ∑ r : α, ∑ r' : α, m r') / 2 := hsplit
      _ = (Fintype.card α : ℝ) * ∑ r : α, m r := by rw [e2]; ring
  calc (∑ r : α, Real.sqrt (m r)) ^ 2
      = ∑ r : α, ∑ r' : α, Real.sqrt (m r) * Real.sqrt (m r') := by
        rw [pow_two, Finset.sum_mul_sum]
    _ ≤ ∑ r : α, ∑ r' : α, (m r + m r') / 2 := Finset.sum_le_sum (fun r _ =>
        Finset.sum_le_sum (fun r' _ => hpair r r'))
    _ = (Fintype.card α : ℝ) * ∑ r : α, m r := hswap
omit [Fintype I] in
/-- Summing a nonnegative function over an image cannot exceed the indexed sum. -/
private theorem sumDomLe {s : Finset ℕ} {h : ℕ → I} {g : I → ℝ} (hg : ∀ y, 0 ≤ g y) :
    ∑ y ∈ Finset.image h s, g y ≤ ∑ j ∈ s, g (h j) := by
  classical
  have hfib : ∑ j ∈ s, g (h j)
      = ∑ y ∈ Finset.image h s, ∑ j ∈ s.filter (fun j => h j = y), g (h j) :=
    (Finset.sum_fiberwise_of_maps_to (fun j hj =>
      Finset.mem_image.mpr ⟨j, hj, rfl⟩) (fun i => g (h i))).symm
  rw [hfib]
  refine Finset.sum_le_sum fun y hy => ?_
  obtain ⟨j, hj, hjy⟩ := Finset.mem_image.mp hy
  have hjmem : j ∈ s.filter (fun j => h j = y) := Finset.mem_filter.mpr ⟨hj, hjy⟩
  have hc : (1 : ℝ) ≤ (s.filter (fun j => h j = y)).card := by
    exact_mod_cast Finset.one_le_card.mpr ⟨j, hjmem⟩
  calc g y = g y * 1 := by ring
    _ ≤ g y * (s.filter (fun j => h j = y)).card := mul_le_mul_of_nonneg_left hc (hg y)
    _ = ∑ j' ∈ s.filter (fun j => h j = y), g y := by
        simp [Finset.sum_const, mul_comm]
    _ = ∑ j' ∈ s.filter (fun j => h j = y), g (h j') :=
        Finset.sum_congr rfl (fun j' hj' => by rw [(Finset.mem_filter.mp hj').2])

/-- Extend a fresh-string draw to an `ℕ`-indexed sequence. -/
def extSeq (T : ℕ) (r : Fin (T + 1) → I) : ℕ → I :=
  fun k => if h : (k : ℕ) < T + 1 then r ⟨k, h⟩ else r ⟨0, by omega⟩

omit [Fintype I] [DecidableEq I] in
/-- Updating one draw leaves each different in-range sequence coordinate unchanged. -/
theorem extSeq_update (T : ℕ) (r : Fin (T + 1) → I) (j : Fin (T + 1)) (c : I)
    (m : ℕ) (hm : (m : ℕ) ≠ (j : ℕ)) (hmT : (m : ℕ) ≤ T) :
    extSeq T (Function.update r j c) m = extSeq T r m := by
  classical
  have h : (m : ℕ) < T + 1 := by omega
  unfold extSeq
  rw [dite_eq_left h, dite_eq_left h]
  have hjm : ¬ (⟨m, h⟩ : Fin (T + 1)) = j := fun hc => hm (Fin.ext_iff.mp hc)
  exact Function.update_of_ne hjm c r

/-- The mixed-schedule run of the transposition chain. -/
def mixRun (T : ℕ) (π0 : I ≃ I) (r : Fin (T + 1) → I) (U : ℕ → Matrix I I ℂ)
    (init : QState I) : ℕ → QState I :=
  oracleRun (fun t => chainPerm π0 (extSeq T r) t) U init

/-- A mixed run depends only on draw coordinates already reached by its chain. -/
theorem mixRun_indep (T : ℕ) (π0 : I ≃ I) (r : Fin (T + 1) → I) (U : ℕ → Matrix I I ℂ)
    (init : QState I) (j : Fin (T + 1)) (c : I) (k : ℕ) (hk : (k : ℕ) ≤ (j : ℕ)) :
    mixRun T π0 (Function.update r j c) U init k = mixRun T π0 r U init k := by
  unfold mixRun
  refine oracleRun_congr (i := k) fun t ht => ?_
  refine chainPerm_congr π0 t fun t' ht' => ?_
  rw [extSeq_update T r j c t' (by omega) (by omega)]

/-- The expected total hybrid charge of the fresh scope at step `k` is at most
the number of scope pairs divided by `|I|`; each uniformly fresh string only
carries its fair share of the query mass. -/
theorem avgCharge [Nonempty I] (T T' k : ℕ) (_hkT : k < T) (hkT' : k ≤ T')
    (hT' : T' ≤ T)
    (π0 : I ≃ I) (U : ℕ → Matrix I I ℂ) (hU : ∀ k, U k ∈ Matrix.unitaryGroup I ℂ)
    (init : QState I) (hinit : ∑ x, ‖init x‖ ^ 2 ≤ 1) :
    ∑ r : Fin (T + 1) → I, ∑ y ∈ differSet
        (chainPerm π0 (extSeq T r) k) (chainPerm π0 (extSeq T r) T'),
      ‖mixRun T π0 r U init k y‖ ^ 2 ≤
      ((T' + 1 - k : ℕ) : ℝ) * ((Fintype.card I : ℝ) ^ T) := by
  classical
  have hscope : ∀ r : Fin (T + 1) → I, ∀ y ∈ differSet
      (chainPerm π0 (extSeq T r) k) (chainPerm π0 (extSeq T r) T'),
      y ∈ Finset.image (extSeq T r) (Finset.Icc k T') := by
    intro r y hy
    obtain ⟨j, hj1, hj2, hj3⟩ := differScope π0 (extSeq T r) T' k hkT' y
      ((Finset.mem_filter.mp hy).2).symm
    exact Finset.mem_image.mpr ⟨j, Finset.mem_Icc.mpr ⟨hj1, hj2⟩, hj3.symm⟩
  have hstep1 : ∀ r : Fin (T + 1) → I, ∑ y ∈ differSet
      (chainPerm π0 (extSeq T r) k) (chainPerm π0 (extSeq T r) T'),
      ‖mixRun T π0 r U init k y‖ ^ 2 ≤
      ∑ j ∈ Finset.Icc k T', ‖mixRun T π0 r U init k (extSeq T r j)‖ ^ 2 := by
    intro r
    calc ∑ y ∈ differSet (chainPerm π0 (extSeq T r) k) (chainPerm π0 (extSeq T r) T'),
          ‖mixRun T π0 r U init k y‖ ^ 2
        ≤ ∑ y ∈ Finset.image (extSeq T r) (Finset.Icc k T'),
          ‖mixRun T π0 r U init k y‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (f := fun y => ‖mixRun T π0 r U init k y‖ ^ 2)
            (fun y hy => hscope r y hy) (fun y _ _ => sq_nonneg _)
      _ ≤ ∑ j ∈ Finset.Icc k T', ‖mixRun T π0 r U init k (extSeq T r j)‖ ^ 2 :=
          sumDomLe (h := extSeq T r) (g := fun y => ‖mixRun T π0 r U init k y‖ ^ 2)
            (fun y => sq_nonneg _)
  refine le_trans (Finset.sum_le_sum
    (f := fun r => ∑ y ∈ differSet (chainPerm π0 (extSeq T r) k)
      (chainPerm π0 (extSeq T r) T'), ‖mixRun T π0 r U init k y‖ ^ 2)
    (g := fun r => ∑ j ∈ Finset.Icc k T',
      ‖mixRun T π0 r U init k (extSeq T r j)‖ ^ 2)
    (fun r _ => hstep1 r)) ?_
  rw [Finset.sum_comm]
  have hmain : ∀ j ∈ Finset.Icc k T',
      (∑ r : Fin (T + 1) → I,
        ‖mixRun T π0 r U init k (extSeq T r j)‖ ^ 2) ≤ (1 : ℝ) * (Fintype.card I) ^ T := by
    intro j hj
    obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hj
    have hjlt : (j : ℕ) < T + 1 := by omega
    have hinner : ∑ r : Fin (T + 1) → I,
        ‖mixRun T π0 r U init k (extSeq T r j)‖ ^ 2
        ≤ (1 : ℝ) * (Fintype.card I) ^ T := by
      have hext : ∀ r : Fin (T + 1) → I, extSeq T r j = r ⟨j, hjlt⟩ := fun r => dite_eq_left hjlt
      have hrew : ∑ r : Fin (T + 1) → I, ‖mixRun T π0 r U init k (extSeq T r j)‖ ^ 2
          = ∑ r : Fin (T + 1) → I, ‖mixRun T π0 r U init k (r ⟨j, hjlt⟩)‖ ^ 2 :=
        Finset.sum_congr rfl fun r _ => by rw [hext r]
      rw [hrew]
      refine sumFresh (⟨j, hjlt⟩ : Fin (T + 1))
        (fun r => mixRun T π0 r U init k) ?_ 1 ?_
      · intro r c
        exact mixRun_indep T π0 r U init ⟨j, hjlt⟩ c k (by simp; omega)
      · intro r
        calc ∑ c, ‖mixRun T π0 r U init k c‖ ^ 2
            = ∑ x, ‖init x‖ ^ 2 := mass_oracleRun _ _ hU init k
          _ ≤ 1 := hinit
    exact hinner
  have hcard : (Finset.Icc k T').card = T' + 1 - k := Nat.card_Icc k T'
  calc ∑ j ∈ Finset.Icc k T', ∑ r : Fin (T + 1) → I,
      ‖mixRun T π0 r U init k (extSeq T r j)‖ ^ 2
      ≤ ∑ j ∈ Finset.Icc k T', (1 : ℝ) * (Fintype.card I) ^ T :=
        Finset.sum_le_sum fun j hj => hmain j hj
    _ = ((T' + 1 - k : ℕ) : ℝ) * ((Fintype.card I : ℝ) ^ T) := by
        rw [Finset.sum_const, nsmul_eq_mul, hcard]
        ring


/-! ## Pinned transposition schedules -/

omit [DecidableEq I] in
/-- The number of draw tuples on `Fin m` equals `|I| ^ m`. -/
private theorem cardFinPow (m : ℕ) : Fintype.card (Fin m → I) = (Fintype.card I) ^ m := by
  rw [Fintype.card_pi]
  simp

omit [DecidableEq I] in
/-- A uniformly drawn coordinate of a uniform tuple on `Fin m` with `m ≥ 1`
only carries its fair share of the mass of `f` when `f` ignores that
coordinate. -/
theorem sumFreshFin {m : ℕ} (hm : 1 ≤ m) [Nonempty I] (j : Fin m)
    (f : (Fin m → I) → I → ℂ)
    (hind : ∀ r c, f (Function.update r j c) = f r)
    (B : ℝ) (hB : ∀ r, ∑ c, ‖f r c‖ ^ 2 ≤ B) :
    ∑ r : Fin m → I, ‖f r (r j)‖ ^ 2 ≤ B * ((Fintype.card I : ℝ) ^ (m - 1)) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  refine le_trans (sumFresh j f hind B hB) ?_
  exact le_refl _

/-- The draw sequence of the pinned transposition chain: coordinate `0` is the
seed preimage `x₀` and coordinate `k` with `1 ≤ k ≤ T` is the `(k-1)`-th drawn
string. -/
def pinnedSeq (x₀ : I) (T : ℕ) (s : Fin T → I) : ℕ → I :=
  fun k => if h : 0 < k ∧ k ≤ T then s ⟨k - 1, by omega⟩ else x₀

omit [Fintype I] [DecidableEq I] in
/-- A pinned sequence begins at the seed preimage. -/
theorem pinnedSeq_zero (x₀ : I) (T : ℕ) (s : Fin T → I) :
    pinnedSeq x₀ T s 0 = x₀ := by
  simp [pinnedSeq]

omit [Fintype I] [DecidableEq I] in
/-- Positive in-range indices select their corresponding fresh draw. -/
theorem pinnedSeq_pos (x₀ : I) (T : ℕ) (s : Fin T → I) {k : ℕ} (h1 : 0 < k)
    (h2 : k ≤ T) : pinnedSeq x₀ T s k = s ⟨k - 1, by omega⟩ := by
  have h : 0 < k ∧ k ≤ T := ⟨h1, h2⟩
  simp [pinnedSeq, h]

omit [Fintype I] [DecidableEq I] in
/-- Indices outside the draw range return the seed preimage. -/
theorem pinnedSeq_neg (x₀ : I) (T : ℕ) (s : Fin T → I) {k : ℕ}
    (h : ¬ (0 < k ∧ k ≤ T)) : pinnedSeq x₀ T s k = x₀ := by
  simp [pinnedSeq, h]

/-- The mixed-schedule run of the pinned transposition chain, whose step `t`
consults the oracle `chainPerm π0 (pinnedSeq x₀ T s) t`. -/
def pinRun (T : ℕ) (π0 : I ≃ I) (x₀ : I) (s : Fin T → I)
    (U : ℕ → Matrix I I ℂ) (init : QState I) : ℕ → QState I :=
  oracleRun (fun t => chainPerm π0 (pinnedSeq x₀ T s) t) U init

/-- The pinned mixed run starts from the supplied state. -/
theorem pinRun_zero (T : ℕ) (π0 : I ≃ I) (x₀ : I) (s : Fin T → I)
    (U : ℕ → Matrix I I ℂ) (init : QState I) : pinRun T π0 x₀ s U init 0 = init := rfl

/-- The pinned run state at step `k` does not depend on the drawn coordinate
`j+1` whenever `k ≤ j+1`: a fresh string the chain has not yet reached cannot
influence the run. -/
theorem pinRun_update (T : ℕ) (π0 : I ≃ I) (x₀ : I) (s : Fin T → I)
    (U : ℕ → Matrix I I ℂ) (init : QState I) (j : Fin T) (c : I)
    {k : ℕ} (hk : k ≤ (j : ℕ) + 1) :
    pinRun T π0 x₀ (Function.update s j c) U init k = pinRun T π0 x₀ s U init k := by
  unfold pinRun
  refine oracleRun_congr (i := k) fun t ht => ?_
  refine chainPerm_congr π0 t fun t' ht' => ?_
  by_cases h1 : 0 < t' ∧ t' ≤ T
  · rw [pinnedSeq_pos x₀ T _ h1.1 h1.2, pinnedSeq_pos x₀ T _ h1.1 h1.2]
    have hne : (t' - 1 : ℕ) ≠ (j : ℕ) := by omega
    have hne' : (⟨t' - 1, by omega⟩ : Fin T) ≠ j := by
      intro hc
      apply hne
      exact congrArg Fin.val hc
    exact Function.update_of_ne hne' c s
  · rw [pinnedSeq_neg x₀ T _ h1, pinnedSeq_neg x₀ T _ h1]

/-- Expected hybrid charge of the pinned chain at step `k`: summed over all
draw tuples, the query mass that the pinned run puts on the disagreement scope
between the `k`-th and the final chain stage is at most the number of scope
positions times the fair share `|I| ^ (T-1)`. -/
theorem chargePinned [Nonempty I] {T : ℕ} (hT1 : 1 ≤ T) (π0 : I ≃ I) (x₀ : I)
    (U : ℕ → Matrix I I ℂ) (hU : ∀ k, U k ∈ Matrix.unitaryGroup I ℂ)
    (init : QState I) (hinit : ∑ x, ‖init x‖ ^ 2 ≤ 1)
    (hx₀m : ‖init x₀‖ ^ 2 ≤ (Fintype.card I : ℝ)⁻¹) (k : ℕ) (hk : k ≤ T) :
    ∑ s : Fin T → I, ∑ y ∈ differSet (chainPerm π0 (pinnedSeq x₀ T s) k)
        (chainPerm π0 (pinnedSeq x₀ T s) T),
      ‖pinRun T π0 x₀ s U init k y‖ ^ 2 ≤
    (((T + 1 - k : ℕ) : ℝ) * ((Fintype.card I : ℝ) ^ (T - 1))) := by
  classical
  obtain ⟨n, rfl⟩ : ∃ n, T = n + 1 := ⟨T - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hscope : ∀ s : Fin (n + 1) → I, ∀ y ∈ differSet
      (chainPerm π0 (pinnedSeq x₀ (n + 1) s) k) (chainPerm π0 (pinnedSeq x₀ (n + 1) s) (n + 1)),
      y ∈ Finset.image (pinnedSeq x₀ (n + 1) s) (Finset.Icc k (n + 1)) := by
    intro s y hy
    obtain ⟨j, hj1, hj2, hj3⟩ := differScope π0 (pinnedSeq x₀ (n + 1) s) (n + 1) k hk y
      ((Finset.mem_filter.mp hy).2).symm
    exact Finset.mem_image.mpr ⟨j, Finset.mem_Icc.mpr ⟨hj1, hj2⟩, hj3.symm⟩
  have hstep1 : ∀ s : Fin (n + 1) → I, ∑ y ∈ differSet
      (chainPerm π0 (pinnedSeq x₀ (n + 1) s) k) (chainPerm π0 (pinnedSeq x₀ (n + 1) s) (n + 1)),
      ‖pinRun (n + 1) π0 x₀ s U init k y‖ ^ 2 ≤
      ∑ j ∈ Finset.Icc k (n + 1),
        ‖pinRun (n + 1) π0 x₀ s U init k (pinnedSeq x₀ (n + 1) s j)‖ ^ 2 := by
    intro s
    calc ∑ y ∈ differSet (chainPerm π0 (pinnedSeq x₀ (n + 1) s) k)
          (chainPerm π0 (pinnedSeq x₀ (n + 1) s) (n + 1)),
          ‖pinRun (n + 1) π0 x₀ s U init k y‖ ^ 2
        ≤ ∑ y ∈ Finset.image (pinnedSeq x₀ (n + 1) s) (Finset.Icc k (n + 1)),
          ‖pinRun (n + 1) π0 x₀ s U init k y‖ ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg
              (f := fun y => ‖pinRun (n + 1) π0 x₀ s U init k y‖ ^ 2)
              (fun y hy => hscope s y hy) (fun y _ _ => sq_nonneg _)
      _ ≤ ∑ j ∈ Finset.Icc k (n + 1),
          ‖pinRun (n + 1) π0 x₀ s U init k (pinnedSeq x₀ (n + 1) s j)‖ ^ 2 :=
            sumDomLe (h := pinnedSeq x₀ (n + 1) s)
              (g := fun y => ‖pinRun (n + 1) π0 x₀ s U init k y‖ ^ 2)
              (fun y => sq_nonneg _)
  have hterm : ∀ j ∈ Finset.Icc k (n + 1), ∑ s : Fin (n + 1) → I,
      ‖pinRun (n + 1) π0 x₀ s U init k (pinnedSeq x₀ (n + 1) s j)‖ ^ 2 ≤
      (1 : ℝ) * ((Fintype.card I : ℝ) ^ n) := by
    intro j hj
    obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · have hpin : ∀ s : Fin (n + 1) → I, pinnedSeq x₀ (n + 1) s 0 = x₀ :=
        fun s => pinnedSeq_zero x₀ (n + 1) s
      have hk0 : k = 0 := by omega
      subst hk0
      have hcpos : (0 : ℝ) < (Fintype.card I : ℝ) := by
        exact_mod_cast Fintype.card_pos
      have hrew : ∑ s : Fin (n + 1) → I,
          ‖pinRun (n + 1) π0 x₀ s U init 0 (pinnedSeq x₀ (n + 1) s 0)‖ ^ 2
          = ∑ s : Fin (n + 1) → I, ‖init x₀‖ ^ 2 :=
        Finset.sum_congr rfl fun s _ => by simp only [hpin s, pinRun_zero]
      rw [hrew]
      calc ∑ s : Fin (n + 1) → I, ‖init x₀‖ ^ 2
          = (Fintype.card (Fin (n + 1) → I) : ℝ) * ‖init x₀‖ ^ 2 := by
            rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
          _ = ((Fintype.card I : ℝ) ^ (n + 1)) * ‖init x₀‖ ^ 2 := by
            rw [cardFinPow]
            simp
          _ ≤ ((Fintype.card I : ℝ) ^ (n + 1)) * ((Fintype.card I : ℝ)⁻¹) :=
            mul_le_mul_of_nonneg_left hx₀m (by positivity)
          _ = (Fintype.card I : ℝ) ^ n := by
            rw [pow_succ]
            field_simp
          _ = (1 : ℝ) * ((Fintype.card I : ℝ) ^ n) := by ring
    · have hkk : k ≤ (j - 1) + 1 := by omega
      have hrew2 : ∑ s : Fin (n + 1) → I,
          ‖pinRun (n + 1) π0 x₀ s U init k (pinnedSeq x₀ (n + 1) s j)‖ ^ 2
          = ∑ s : Fin (n + 1) → I,
          ‖pinRun (n + 1) π0 x₀ s U init k (s ⟨j - 1, by omega⟩)‖ ^ 2 :=
        Finset.sum_congr rfl fun s _ => by rw [pinnedSeq_pos x₀ (n + 1) s hjpos hj2]
      rw [hrew2]
      refine sumFreshFin (by omega : 1 ≤ n + 1) (⟨j - 1, by omega⟩ : Fin (n + 1))
        (fun s => pinRun (n + 1) π0 x₀ s U init k) ?_ 1 ?_
      · exact fun s c => pinRun_update (n + 1) π0 x₀ s U init _ c hkk
      · intro s
        calc ∑ c, ‖pinRun (n + 1) π0 x₀ s U init k c‖ ^ 2
            = ∑ x, ‖init x‖ ^ 2 := mass_oracleRun _ _ hU init k
          _ ≤ 1 := hinit
  calc ∑ s : Fin (n + 1) → I, ∑ y ∈ differSet
        (chainPerm π0 (pinnedSeq x₀ (n + 1) s) k) (chainPerm π0 (pinnedSeq x₀ (n + 1) s) (n + 1)),
        ‖pinRun (n + 1) π0 x₀ s U init k y‖ ^ 2
    ≤ ∑ s : Fin (n + 1) → I, ∑ j ∈ Finset.Icc k (n + 1),
        ‖pinRun (n + 1) π0 x₀ s U init k (pinnedSeq x₀ (n + 1) s j)‖ ^ 2 :=
        Finset.sum_le_sum fun s _ => hstep1 s
  _ = ∑ j ∈ Finset.Icc k (n + 1), ∑ s : Fin (n + 1) → I,
      ‖pinRun (n + 1) π0 x₀ s U init k (pinnedSeq x₀ (n + 1) s j)‖ ^ 2 :=
        Finset.sum_comm
  _ ≤ ∑ j ∈ Finset.Icc k (n + 1), (1 : ℝ) * ((Fintype.card I : ℝ) ^ n) :=
        Finset.sum_le_sum fun j hj => hterm j hj
  _ = (((n + 1 + 1 - k : ℕ) : ℝ) * ((Fintype.card I : ℝ) ^ n)) := by
        rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc k (n + 1)]
        ring

/-- Cauchy--Schwarz over the draw tuples bounds the total distance between the
pinned mixed-schedule run and the run under the final fixed oracle by
`2 |I|^(T-1) Σ_k √((T+1-k) |I|)`; after dividing by `|I|^T` draws this is the
finite square-root-sum schedule bound. The state uses an in-place
permutation action, and the seed-preimage fair-share hypothesis is explicit;
no standard reversible bit-query port bridge is asserted. -/
theorem avgDistPinned [Nonempty I] {T : ℕ} (hT1 : 1 ≤ T) (π0 : I ≃ I) (x₀ : I)
    (U : ℕ → Matrix I I ℂ) (hU : ∀ k, U k ∈ Matrix.unitaryGroup I ℂ)
    (init : QState I) (hinit : ∑ x, ‖init x‖ ^ 2 ≤ 1)
    (hx₀m : ‖init x₀‖ ^ 2 ≤ (Fintype.card I : ℝ)⁻¹) :
    ∑ s : Fin T → I, ‖toEuclidean_fromVec (pinRun T π0 x₀ s U init T
        - oracleRun (fun _ => chainPerm π0 (pinnedSeq x₀ T s) T) U init T)‖ ≤
      ∑ k ∈ Finset.range T, 2 * ((Fintype.card I : ℝ) ^ (T - 1))
        * Real.sqrt (((T + 1 - k : ℕ) : ℝ) * (Fintype.card I : ℝ)) := by
  classical
  obtain ⟨n, rfl⟩ : ∃ n, T = n + 1 := ⟨T - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hcardpos : (0 : ℝ) < (Fintype.card I : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hdist : ∀ s : Fin (n + 1) → I,
      ‖toEuclidean_fromVec (pinRun (n + 1) π0 x₀ s U init (n + 1)
        - oracleRun (fun _ => chainPerm π0 (pinnedSeq x₀ (n + 1) s) (n + 1)) U init (n + 1))‖ ≤
      ∑ k ∈ Finset.range (n + 1), ‖toEuclidean_fromVec (permAct
        (chainPerm π0 (pinnedSeq x₀ (n + 1) s) k) (pinRun (n + 1) π0 x₀ s U init k)
        - permAct (chainPerm π0 (pinnedSeq x₀ (n + 1) s) (n + 1))
            (pinRun (n + 1) π0 x₀ s U init k))‖ :=
    fun s => hybDist _ _ _ hU _ (n + 1)
  have hmass : ∀ k : ℕ, ∀ s : Fin (n + 1) → I, (‖toEuclidean_fromVec (permAct
        (chainPerm π0 (pinnedSeq x₀ (n + 1) s) k) (pinRun (n + 1) π0 x₀ s U init k)
        - permAct (chainPerm π0 (pinnedSeq x₀ (n + 1) s) (n + 1))
            (pinRun (n + 1) π0 x₀ s U init k))‖) ^ 2 ≤
      4 * ∑ y ∈ differSet (chainPerm π0 (pinnedSeq x₀ (n + 1) s) k)
        (chainPerm π0 (pinnedSeq x₀ (n + 1) s) (n + 1)),
        ‖pinRun (n + 1) π0 x₀ s U init k y‖ ^ 2 := by
    intro k s
    rw [norm_toEuclidean_fromVec_sq]
    exact permDiff_le _ _ _
  have hstep : ∀ k ∈ Finset.range (n + 1),
      (∑ s : Fin (n + 1) → I, ‖toEuclidean_fromVec (permAct
        (chainPerm π0 (pinnedSeq x₀ (n + 1) s) k) (pinRun (n + 1) π0 x₀ s U init k)
        - permAct (chainPerm π0 (pinnedSeq x₀ (n + 1) s) (n + 1))
            (pinRun (n + 1) π0 x₀ s U init k))‖) ^ 2 ≤
      (2 * ((Fintype.card I : ℝ) ^ n)
        * Real.sqrt (((n + 1 + 1 - k : ℕ) : ℝ) * (Fintype.card I : ℝ))) ^ 2 := by
    intro k hk
    have hk1 : k < n + 1 := Finset.mem_range.mp hk
    have hchg := chargePinned hT1 π0 x₀ U hU init hinit hx₀m k (by omega)
    have hsq : (∑ s : Fin (n + 1) → I, Real.sqrt ((‖toEuclidean_fromVec (permAct
        (chainPerm π0 (pinnedSeq x₀ (n + 1) s) k) (pinRun (n + 1) π0 x₀ s U init k)
        - permAct (chainPerm π0 (pinnedSeq x₀ (n + 1) s) (n + 1))
            (pinRun (n + 1) π0 x₀ s U init k))‖) ^ 2)) ^ 2 ≤
        (Fintype.card (Fin (n + 1) → I)) * ∑ s : Fin (n + 1) → I, (‖toEuclidean_fromVec
          (permAct (chainPerm π0 (pinnedSeq x₀ (n + 1) s) k) (pinRun (n + 1) π0 x₀ s U init k)
          - permAct (chainPerm π0 (pinnedSeq x₀ (n + 1) s) (n + 1))
            (pinRun (n + 1) π0 x₀ s U init k))‖) ^ 2 :=
      sumSqrtCard _ (fun s => sq_nonneg _)
    have hsqrt : ∑ s : Fin (n + 1) → I, Real.sqrt ((‖toEuclidean_fromVec (permAct
        (chainPerm π0 (pinnedSeq x₀ (n + 1) s) k) (pinRun (n + 1) π0 x₀ s U init k)
        - permAct (chainPerm π0 (pinnedSeq x₀ (n + 1) s) (n + 1))
            (pinRun (n + 1) π0 x₀ s U init k))‖) ^ 2)
        = ∑ s : Fin (n + 1) → I, ‖toEuclidean_fromVec (permAct
        (chainPerm π0 (pinnedSeq x₀ (n + 1) s) k) (pinRun (n + 1) π0 x₀ s U init k)
        - permAct (chainPerm π0 (pinnedSeq x₀ (n + 1) s) (n + 1))
            (pinRun (n + 1) π0 x₀ s U init k))‖ :=
      Finset.sum_congr rfl fun s _ => Real.sqrt_sq (norm_nonneg _)
    rw [hsqrt, cardFinPow] at hsq
    have hpow : (2 * ((Fintype.card I : ℝ) ^ n)
          * Real.sqrt (((n + 1 + 1 - k : ℕ) : ℝ) * (Fintype.card I : ℝ))) ^ 2
        = ((Fintype.card I : ℝ) ^ (n + 1)) * (4 * (((n + 1 + 1 - k : ℕ) : ℝ)
          * ((Fintype.card I : ℝ) ^ n))) := by
      have hK : (0 : ℝ) ≤ (((n + 1 + 1 - k : ℕ) : ℝ) * (Fintype.card I : ℝ)) := by
        have hc : (0 : ℝ) ≤ (Fintype.card I : ℝ) := le_of_lt hcardpos
        positivity
      have e1 : (2 * ((Fintype.card I : ℝ) ^ n)
          * Real.sqrt (((n + 1 + 1 - k : ℕ) : ℝ) * (Fintype.card I : ℝ))) ^ 2
          = (2 : ℝ) ^ 2 * (((Fintype.card I : ℝ) ^ n) ^ 2)
            * (((n + 1 + 1 - k : ℕ) : ℝ) * (Fintype.card I : ℝ)) := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hK]
      have e1' : (2 : ℝ) ^ 2 * (((Fintype.card I : ℝ) ^ n) ^ 2)
          * (((n + 1 + 1 - k : ℕ) : ℝ) * (Fintype.card I : ℝ))
          = 4 * ((Fintype.card I : ℝ) ^ (n + n)) * (((n + 1 + 1 - k : ℕ) : ℝ)
            * (Fintype.card I : ℝ)) := by
        rw [show (2 : ℝ) ^ 2 = 4 by norm_num, sq, ← pow_add]
      have e2 : 4 * ((Fintype.card I : ℝ) ^ (n + n)) * (((n + 1 + 1 - k : ℕ) : ℝ)
            * (Fintype.card I : ℝ))
          = ((Fintype.card I : ℝ) ^ (n + 1)) * (4 * (((n + 1 + 1 - k : ℕ) : ℝ)
            * ((Fintype.card I : ℝ) ^ n))) := by
        rw [pow_succ, pow_add]
        ring
      rw [e1, e1', e2]
    calc (∑ s : Fin (n + 1) → I, ‖toEuclidean_fromVec (permAct
          (chainPerm π0 (pinnedSeq x₀ (n + 1) s) k) (pinRun (n + 1) π0 x₀ s U init k)
          - permAct (chainPerm π0 (pinnedSeq x₀ (n + 1) s) (n + 1))
            (pinRun (n + 1) π0 x₀ s U init k))‖) ^ 2
        ≤ ((Fintype.card I : ℝ) ^ (n + 1)) * ∑ s : Fin (n + 1) → I, (‖toEuclidean_fromVec
            (permAct (chainPerm π0 (pinnedSeq x₀ (n + 1) s) k) (pinRun (n + 1) π0 x₀ s U init k)
            - permAct (chainPerm π0 (pinnedSeq x₀ (n + 1) s) (n + 1))
              (pinRun (n + 1) π0 x₀ s U init k))‖) ^ 2 := by
            exact_mod_cast hsq
      _ ≤ ((Fintype.card I : ℝ) ^ (n + 1))
            * (4 * (((n + 1 + 1 - k : ℕ) : ℝ) * ((Fintype.card I : ℝ) ^ n))) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            calc ∑ s : Fin (n + 1) → I, (‖toEuclidean_fromVec
                  (permAct (chainPerm π0 (pinnedSeq x₀ (n + 1) s) k)
                    (pinRun (n + 1) π0 x₀ s U init k)
                  - permAct (chainPerm π0 (pinnedSeq x₀ (n + 1) s) (n + 1))
                    (pinRun (n + 1) π0 x₀ s U init k))‖) ^ 2
                ≤ ∑ s : Fin (n + 1) → I, 4 * ∑ y ∈ differSet
                    (chainPerm π0 (pinnedSeq x₀ (n + 1) s) k)
                    (chainPerm π0 (pinnedSeq x₀ (n + 1) s) (n + 1)),
                    ‖pinRun (n + 1) π0 x₀ s U init k y‖ ^ 2 :=
                  Finset.sum_le_sum fun s _ => hmass k s
              _ = 4 * ∑ s : Fin (n + 1) → I, ∑ y ∈ differSet
                    (chainPerm π0 (pinnedSeq x₀ (n + 1) s) k)
                    (chainPerm π0 (pinnedSeq x₀ (n + 1) s) (n + 1)),
                    ‖pinRun (n + 1) π0 x₀ s U init k y‖ ^ 2 :=
                  (Finset.mul_sum _ _ _).symm
              _ ≤ 4 * (((n + 1 + 1 - k : ℕ) : ℝ) * ((Fintype.card I : ℝ) ^ n)) :=
                  mul_le_mul_of_nonneg_left hchg (by norm_num)
      _ = (2 * ((Fintype.card I : ℝ) ^ n)
          * Real.sqrt (((n + 1 + 1 - k : ℕ) : ℝ) * (Fintype.card I : ℝ))) ^ 2 := hpow.symm
  have hstep' : ∀ k ∈ Finset.range (n + 1),
      (∑ s : Fin (n + 1) → I, ‖toEuclidean_fromVec (permAct
        (chainPerm π0 (pinnedSeq x₀ (n + 1) s) k) (pinRun (n + 1) π0 x₀ s U init k)
        - permAct (chainPerm π0 (pinnedSeq x₀ (n + 1) s) (n + 1))
            (pinRun (n + 1) π0 x₀ s U init k))‖) ≤
      2 * ((Fintype.card I : ℝ) ^ n)
        * Real.sqrt (((n + 1 + 1 - k : ℕ) : ℝ) * (Fintype.card I : ℝ)) :=
    fun k hk => by
      have e1 : (∑ s : Fin (n + 1) → I, ‖toEuclidean_fromVec (permAct
        (chainPerm π0 (pinnedSeq x₀ (n + 1) s) k) (pinRun (n + 1) π0 x₀ s U init k)
        - permAct (chainPerm π0 (pinnedSeq x₀ (n + 1) s) (n + 1))
            (pinRun (n + 1) π0 x₀ s U init k))‖)
          = Real.sqrt ((∑ s : Fin (n + 1) → I, ‖toEuclidean_fromVec (permAct
        (chainPerm π0 (pinnedSeq x₀ (n + 1) s) k) (pinRun (n + 1) π0 x₀ s U init k)
        - permAct (chainPerm π0 (pinnedSeq x₀ (n + 1) s) (n + 1))
            (pinRun (n + 1) π0 x₀ s U init k))‖) ^ 2) :=
        (Real.sqrt_sq (Finset.sum_nonneg fun s _ => norm_nonneg _)).symm
      have e2 : (2 * ((Fintype.card I : ℝ) ^ n)
          * Real.sqrt (((n + 1 + 1 - k : ℕ) : ℝ) * (Fintype.card I : ℝ)))
          = Real.sqrt ((2 * ((Fintype.card I : ℝ) ^ n)
          * Real.sqrt (((n + 1 + 1 - k : ℕ) : ℝ) * (Fintype.card I : ℝ))) ^ 2) :=
        (Real.sqrt_sq (by positivity)).symm
      rw [e1, e2]
      exact Real.sqrt_le_sqrt (hstep k hk)
  calc ∑ s : Fin (n + 1) → I, ‖toEuclidean_fromVec (pinRun (n + 1) π0 x₀ s U init (n + 1)
        - oracleRun (fun _ => chainPerm π0 (pinnedSeq x₀ (n + 1) s) (n + 1)) U init (n + 1))‖
    ≤ ∑ s : Fin (n + 1) → I, ∑ k ∈ Finset.range (n + 1), ‖toEuclidean_fromVec (permAct
        (chainPerm π0 (pinnedSeq x₀ (n + 1) s) k) (pinRun (n + 1) π0 x₀ s U init k)
        - permAct (chainPerm π0 (pinnedSeq x₀ (n + 1) s) (n + 1))
            (pinRun (n + 1) π0 x₀ s U init k))‖ :=
        Finset.sum_le_sum fun s _ => hdist s
  _ = ∑ k ∈ Finset.range (n + 1), ∑ s : Fin (n + 1) → I, ‖toEuclidean_fromVec (permAct
        (chainPerm π0 (pinnedSeq x₀ (n + 1) s) k) (pinRun (n + 1) π0 x₀ s U init k)
        - permAct (chainPerm π0 (pinnedSeq x₀ (n + 1) s) (n + 1))
            (pinRun (n + 1) π0 x₀ s U init k))‖ :=
        Finset.sum_comm
  _ ≤ ∑ k ∈ Finset.range (n + 1), 2 * ((Fintype.card I : ℝ) ^ n)
        * Real.sqrt (((n + 1 + 1 - k : ℕ) : ℝ) * (Fintype.card I : ℝ)) :=
        Finset.sum_le_sum fun k hk => hstep' k hk

/-- The Euclidean distance between the pinned mixed-schedule run and the run
under the final fixed permutation oracle. -/
def runDist (T : ℕ) (π0 : I ≃ I) (x₀ : I) (U : ℕ → Matrix I I ℂ)
    (init : QState I) (s : Fin T → I) : ℝ :=
  ‖toEuclidean_fromVec (pinRun T π0 x₀ s U init T
    - oracleRun (fun _ => chainPerm π0 (pinnedSeq x₀ T s) T) U init T)‖

/-- A finite mixed-schedule estimate supporting Theorem 3.6: under the pinned transposition coupling
with seed preimage `x₀ = π0⁻¹ y₀`, at least a quarter of all draw tuples
simultaneously keep the mixed-schedule run within `2/25` of the run under the
final fixed oracle and flip the value of the first-bit-of-preimage language at
the distinguished output `y₀` between the seed oracle `π0` and the final
oracle, provided `T` is in the small-query regime `100 T √((T+1)|I|) ≤ |I|`,
the two label classes are balanced, and the initial state keeps fair-share
mass on `x₀`. -/
theorem thm36Core [Nonempty I] {T : ℕ} (hT1 : 1 ≤ T) (lab : I → Bool)
    (π0 : I ≃ I) (y₀ x₀ : I) (hx₀ : π0 x₀ = y₀)
    (hbal : 2 * (Finset.univ.filter (fun x => lab x ≠ lab x₀)).card ≥ Fintype.card I)
    (U : ℕ → Matrix I I ℂ) (hU : ∀ k, U k ∈ Matrix.unitaryGroup I ℂ)
    (init : QState I) (hinit : ∑ x, ‖init x‖ ^ 2 ≤ 1)
    (hx₀m : ‖init x₀‖ ^ 2 ≤ (Fintype.card I : ℝ)⁻¹)
    (hregime : 100 * (T : ℝ) * Real.sqrt (((T + 1 : ℕ) : ℝ) * (Fintype.card I : ℝ))
      ≤ (Fintype.card I : ℝ)) :
    4 * (Finset.univ.filter (fun s : Fin T → I =>
        runDist T π0 x₀ U init s ≤ 2 / 25
        ∧ lab ((chainPerm π0 (pinnedSeq x₀ T s) T).symm y₀) ≠ lab x₀)).card
      ≥ (Fintype.card I) ^ T := by
  classical
  obtain ⟨n, rfl⟩ : ∃ n, T = n + 1 := ⟨T - 1, by omega⟩
  set N := (Fintype.card I) ^ (n + 1) with hNdef
  have hcardT : Fintype.card (Fin (n + 1) → I) = N := by rw [cardFinPow, hNdef]
  have hcardpos : (0 : ℝ) < (Fintype.card I : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hpre : ∀ s : Fin (n + 1) → I,
      (chainPerm π0 (pinnedSeq x₀ (n + 1) s) (n + 1)).symm y₀ = s ⟨n, Nat.lt_succ_self n⟩ := by
    intro s
    have h0 : π0 (pinnedSeq x₀ (n + 1) s 0) = y₀ := by
      rw [pinnedSeq_zero]; exact hx₀
    have hT : chainPerm π0 (pinnedSeq x₀ (n + 1) s) (n + 1)
        (pinnedSeq x₀ (n + 1) s (n + 1)) = y₀ :=
      chainPreim π0 (pinnedSeq x₀ (n + 1) s) y₀ h0 (n + 1)
    rw [pinnedSeq_pos x₀ (n + 1) s (by omega) (le_refl _)] at hT
    rw [← hT]
    exact Equiv.symm_apply_apply _ _
  have htotal : ∑ s : Fin (n + 1) → I, runDist (n + 1) π0 x₀ U init s
      ≤ ((N : ℝ)) / 50 := by
    have hrun : ∑ s : Fin (n + 1) → I, runDist (n + 1) π0 x₀ U init s
        = ∑ s : Fin (n + 1) → I, ‖toEuclidean_fromVec (pinRun (n + 1) π0 x₀ s U init (n + 1)
            - oracleRun (fun _ => chainPerm π0 (pinnedSeq x₀ (n + 1) s) (n + 1)) U init (n + 1))‖ :=
      rfl
    rw [hrun]
    have havg := avgDistPinned hT1 π0 x₀ U hU init hinit hx₀m
    have hsum : ∑ k ∈ Finset.range (n + 1),
        Real.sqrt (((n + 1 + 1 - k : ℕ) : ℝ) * (Fintype.card I : ℝ)) ≤
        ((n + 1 : ℕ) : ℝ) * Real.sqrt (((n + 1 + 1 : ℕ) : ℝ) * (Fintype.card I : ℝ)) := by
      calc ∑ k ∈ Finset.range (n + 1),
            Real.sqrt (((n + 1 + 1 - k : ℕ) : ℝ) * (Fintype.card I : ℝ))
          ≤ ∑ k ∈ Finset.range (n + 1),
              Real.sqrt (((n + 1 + 1 : ℕ) : ℝ) * (Fintype.card I : ℝ)) :=
            Finset.sum_le_sum fun k hk => Real.sqrt_le_sqrt
              (mul_le_mul_of_nonneg_right
                ((Nat.cast_le (m := (n + 1 + 1 - k : ℕ)) (n := (n + 1 + 1 : ℕ))).2 (by omega))
                (le_of_lt hcardpos))
        _ = ((n + 1 : ℕ) : ℝ) * Real.sqrt (((n + 1 + 1 : ℕ) : ℝ) * (Fintype.card I : ℝ)) := by
            rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
    calc ∑ s : Fin (n + 1) → I, ‖toEuclidean_fromVec (pinRun (n + 1) π0 x₀ s U init (n + 1)
          - oracleRun (fun _ => chainPerm π0 (pinnedSeq x₀ (n + 1) s) (n + 1)) U init (n + 1))‖
        ≤ ∑ k ∈ Finset.range (n + 1), 2 * ((Fintype.card I : ℝ) ^ n)
            * Real.sqrt (((n + 1 + 1 - k : ℕ) : ℝ) * (Fintype.card I : ℝ)) := havg
      _ = 2 * ((Fintype.card I : ℝ) ^ n) * ∑ k ∈ Finset.range (n + 1),
            Real.sqrt (((n + 1 + 1 - k : ℕ) : ℝ) * (Fintype.card I : ℝ)) :=
            (Finset.mul_sum _ _ _).symm
      _ ≤ 2 * ((Fintype.card I : ℝ) ^ n) * (((n + 1 : ℕ) : ℝ)
            * Real.sqrt (((n + 1 + 1 : ℕ) : ℝ) * (Fintype.card I : ℝ))) :=
            mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = (2 / 100) * (((Fintype.card I : ℝ) ^ n) * (100 * (((n + 1 : ℕ) : ℝ)
            * Real.sqrt (((n + 1 + 1 : ℕ) : ℝ) * (Fintype.card I : ℝ))))) := by
            ring
      _ ≤ (2 / 100) * (((Fintype.card I : ℝ) ^ n) * (Fintype.card I : ℝ)) := by
            have hx0 : (0 : ℝ) ≤ ((Fintype.card I : ℝ) ^ n) := by positivity
            have hreg2 : (((Fintype.card I : ℝ) ^ n) * (100 * (((n + 1 : ℕ) : ℝ)
                * Real.sqrt (((n + 1 + 1 : ℕ) : ℝ) * (Fintype.card I : ℝ)))))
                ≤ (((Fintype.card I : ℝ) ^ n) * (Fintype.card I : ℝ)) := by
              nlinarith [hregime, hx0]
            exact mul_le_mul_of_nonneg_left hreg2 (by positivity)
      _ = ((N : ℝ)) / 50 := by
            rw [hNdef]
            push_cast
            rw [pow_succ]
            field_simp
            ring
  have hbad : (4 : ℝ) * ((Finset.univ.filter
      (fun s : Fin (n + 1) → I => 2 / 25 < runDist (n + 1) π0 x₀ U init s)).card : ℝ)
      ≤ ((N : ℝ)) := by
    have hlb : (2 / 25) * ((Finset.univ.filter
        (fun s : Fin (n + 1) → I => 2 / 25 < runDist (n + 1) π0 x₀ U init s)).card : ℝ)
        ≤ ∑ s ∈ Finset.univ.filter
            (fun s : Fin (n + 1) → I => 2 / 25 < runDist (n + 1) π0 x₀ U init s),
          runDist (n + 1) π0 x₀ U init s := by
      calc (2 / 25) * ((Finset.univ.filter
            (fun s : Fin (n + 1) → I => 2 / 25 < runDist (n + 1) π0 x₀ U init s)).card : ℝ)
          = ∑ s ∈ Finset.univ.filter
              (fun s : Fin (n + 1) → I => 2 / 25 < runDist (n + 1) π0 x₀ U init s),
              (2 / 25 : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
            ring
        _ ≤ ∑ s ∈ Finset.univ.filter
              (fun s : Fin (n + 1) → I => 2 / 25 < runDist (n + 1) π0 x₀ U init s),
              runDist (n + 1) π0 x₀ U init s := by
            refine Finset.sum_le_sum fun s hs => ?_
            exact le_of_lt (Finset.mem_filter.mp hs).2
    have hrd : ∀ s : Fin (n + 1) → I, (0 : ℝ) ≤ runDist (n + 1) π0 x₀ U init s :=
      fun s => norm_nonneg _
    have hub : ∑ s ∈ Finset.univ.filter
          (fun s : Fin (n + 1) → I => 2 / 25 < runDist (n + 1) π0 x₀ U init s),
          runDist (n + 1) π0 x₀ U init s
        ≤ ∑ s : Fin (n + 1) → I, runDist (n + 1) π0 x₀ U init s :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (f := fun s => runDist (n + 1) π0 x₀ U init s)
        (fun s _ => Finset.mem_univ s) (fun s _ _ => hrd s)
    have hfin := le_trans hub htotal
    nlinarith [hlb, hfin]
  have hflipcard : 2 * (Finset.univ.filter
      (fun s : Fin (n + 1) → I => lab (s ⟨n, Nat.lt_succ_self n⟩) ≠ lab x₀)).card ≥ N := by
    have hcf : ∀ {J : Type} [Fintype J] (P : J → Prop) [DecidablePred P],
        (Finset.univ.filter P).card = Fintype.card {s : J // P s} := by
      intro J _ P _
      exact (Fintype.card_subtype P).symm
    have hE : {s : Fin (n + 1) → I // lab (s ⟨n, Nat.lt_succ_self n⟩) ≠ lab x₀}
        ≃ (Fin n → I) × {a : I // lab a ≠ lab x₀} :=
      { toFun := fun s => (Fin.init s.1, ⟨s.1 ⟨n, Nat.lt_succ_self n⟩, s.2⟩)
        invFun := fun p => ⟨Fin.snoc (α := fun _ => I) p.1 p.2.1, by
          have h1 : Fin.snoc (α := fun _ => I) p.1 p.2.1 ⟨n, Nat.lt_succ_self n⟩ = p.2.1 :=
            Fin.snoc_last (α := fun _ => I) p.2.1 p.1
          rw [h1]
          exact p.2.2⟩
        left_inv := by
          intro s
          apply Subtype.ext
          show Fin.snoc (Fin.init s.1) (s.1 ⟨n, Nat.lt_succ_self n⟩) = s.1
          funext i
          have hil := i.isLt
          by_cases hi : (i : ℕ) = n
          · have h1 : i = Fin.last n := Fin.ext hi
            subst h1
            exact Fin.snoc_last (α := fun _ => I)
              (s.1 ⟨n, Nat.lt_succ_self n⟩) (Fin.init s.1)
          · have hij : (i : ℕ) < n := by omega
            have hj : i = (⟨(i : ℕ), hij⟩ : Fin n).castSucc := Fin.ext rfl
            rw [hj, Fin.snoc_castSucc (α := fun _ => I)]
            rfl
        right_inv := by
          intro p
          obtain ⟨u, a, ha⟩ := p
          have h1 : Fin.init (Fin.snoc (α := fun _ => I) u a) = u :=
            Fin.init_snoc (α := fun _ => I) a u
          have h2 : Fin.snoc (α := fun _ => I) u a ⟨n, Nat.lt_succ_self n⟩ = a :=
            Fin.snoc_last (α := fun _ => I) a u
          dsimp only
          rw [Prod.mk.injEq]
          exact ⟨h1, Subtype.ext h2⟩ }
    have hcard : (Finset.univ.filter
        (fun s : Fin (n + 1) → I => lab (s ⟨n, Nat.lt_succ_self n⟩) ≠ lab x₀)).card
        = (Fintype.card (Fin n → I)) * (Finset.univ.filter
            (fun a : I => lab a ≠ lab x₀)).card := by
      calc (Finset.univ.filter (fun s : Fin (n + 1) → I =>
              lab (s ⟨n, Nat.lt_succ_self n⟩) ≠ lab x₀)).card
          = Fintype.card {s : Fin (n + 1) → I //
              lab (s ⟨n, Nat.lt_succ_self n⟩) ≠ lab x₀} :=
            hcf _
        _ = Fintype.card ((Fin n → I) × {a : I // lab a ≠ lab x₀}) :=
            Fintype.card_congr hE
        _ = (Fintype.card (Fin n → I)) * Fintype.card {a : I // lab a ≠ lab x₀} :=
            Fintype.card_prod _ _
        _ = (Fintype.card (Fin n → I)) * (Finset.univ.filter
              (fun a : I => lab a ≠ lab x₀)).card :=
            congrArg (fun t => (Fintype.card (Fin n → I)) * t)
              ((hcf (fun a : I => lab a ≠ lab x₀)).symm)
    have h3 : (Fintype.card I) ^ n * (2 * (Finset.univ.filter
        (fun a : I => lab a ≠ lab x₀)).card) ≥ (Fintype.card I) ^ n * (Fintype.card I) :=
      Nat.mul_le_mul_left _ hbal
    rw [hcard, cardFinPow, hNdef, pow_succ]
    calc 2 * ((Fintype.card I) ^ n * (Finset.univ.filter
          (fun a : I => lab a ≠ lab x₀)).card)
        = (Fintype.card I) ^ n * (2 * (Finset.univ.filter
            (fun a : I => lab a ≠ lab x₀)).card) := by ring
      _ ≥ (Fintype.card I) ^ n * (Fintype.card I) := h3
  have hclosecard : (Finset.univ.filter
        (fun s : Fin (n + 1) → I => runDist (n + 1) π0 x₀ U init s ≤ 2 / 25)).card
      + (Finset.univ.filter
        (fun s : Fin (n + 1) → I => 2 / 25 < runDist (n + 1) π0 x₀ U init s)).card = N := by
    have hbadNot : (Finset.univ.filter
        (fun s : Fin (n + 1) → I => 2 / 25 < runDist (n + 1) π0 x₀ U init s))
        = Finset.univ.filter
            (fun s : Fin (n + 1) → I => ¬ (runDist (n + 1) π0 x₀ U init s ≤ 2 / 25)) := by
      exact Finset.filter_congr fun s _ => lt_iff_not_ge
    rw [hbadNot]
    simpa only [Finset.card_univ, hcardT] using
      (Finset.card_filter_add_card_filter_not (s := Finset.univ)
        (fun s : Fin (n + 1) → I => runDist (n + 1) π0 x₀ U init s ≤ 2 / 25))
  have hkey : (4 : ℤ) * ((Finset.univ.filter
        (fun s : Fin (n + 1) → I => runDist (n + 1) π0 x₀ U init s ≤ 2 / 25)
        ∩ Finset.univ.filter
          (fun s : Fin (n + 1) → I => lab (s ⟨n, Nat.lt_succ_self n⟩) ≠ lab x₀)).card) ≥ N := by
    have hIA := Finset.card_inter_add_card_union
      (Finset.univ.filter (fun s : Fin (n + 1) → I => runDist (n + 1) π0 x₀ U init s ≤ 2 / 25))
      (Finset.univ.filter
        (fun s : Fin (n + 1) → I => lab (s ⟨n, Nat.lt_succ_self n⟩) ≠ lab x₀))
    have hU : ((Finset.univ.filter
          (fun s : Fin (n + 1) → I => runDist (n + 1) π0 x₀ U init s ≤ 2 / 25)
          ∪ Finset.univ.filter
            (fun s : Fin (n + 1) → I => lab (s ⟨n, Nat.lt_succ_self n⟩) ≠ lab x₀)).card : ℤ)
        ≤ ((N : ℤ)) := by
      refine le_trans (Nat.cast_le.mpr (Finset.card_le_card
        (Finset.subset_univ _))) ?_
      rw [Finset.card_univ, hcardT]
    have hb : (4 : ℤ) * (Finset.univ.filter
        (fun s : Fin (n + 1) → I => 2 / 25 < runDist (n + 1) π0 x₀ U init s)).card
        ≤ ((N : ℤ)) := by exact_mod_cast hbad
    have hf : (2 : ℤ) * (Finset.univ.filter
        (fun s : Fin (n + 1) → I => lab (s ⟨n, Nat.lt_succ_self n⟩) ≠ lab x₀)).card
        ≥ ((N : ℤ)) := by exact_mod_cast hflipcard
    have hc : ((Finset.univ.filter
        (fun s : Fin (n + 1) → I => runDist (n + 1) π0 x₀ U init s ≤ 2 / 25)).card : ℤ)
        + (Finset.univ.filter
        (fun s : Fin (n + 1) → I => 2 / 25 < runDist (n + 1) π0 x₀ U init s)).card
        = ((N : ℤ)) := by exact_mod_cast hclosecard
    omega
  have hset : (Finset.univ.filter (fun s : Fin (n + 1) → I =>
        (runDist (n + 1) π0 x₀ U init s ≤ 2 / 25)
        ∧ lab ((chainPerm π0 (pinnedSeq x₀ (n + 1) s) (n + 1)).symm y₀) ≠ lab x₀))
      = (Finset.univ.filter
          (fun s : Fin (n + 1) → I => runDist (n + 1) π0 x₀ U init s ≤ 2 / 25))
        ∩ Finset.univ.filter
          (fun s : Fin (n + 1) → I => lab (s ⟨n, Nat.lt_succ_self n⟩) ≠ lab x₀) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter, hpre s]
  rw [hset]
  exact_mod_cast hkey

end Qatlib.Papers.QWeakness97.MainResults.PermCoupling
