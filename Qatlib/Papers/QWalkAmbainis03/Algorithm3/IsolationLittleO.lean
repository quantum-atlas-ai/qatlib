/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.WalkFind.SearchAlgorithm.Algorithm3IsolationQuan
public import Qatlib.Concepts.WalkFind.SearchAlgorithm.Algorithm3IsolationAsymptotics
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

/-!
# The little-o form of the collision-isolation error

Fixed source: [Ambainis2007ElementDistinctness], Lemma 4 (quant-ph/0311001v9, p. 20).
For a set `T` containing a
`k`-collision, with `None` the event that the retained set contains no
`k`-collision and `Unique` the event that it contains a unique `k`-collision,
the source asserts

`Pr[Unique] > Pr[None] - o(N^(-1/4))`.

The public library already proves the quantitative comparison
`algorithm3Isolation_quantitative`, whose explicit error is
`(1/2)^floor(log N) + 4/N + 16k^2(log N + 1)^2/sqrt N`, under the same
retained-prefix, size and approximate-independence hypotheses. What was
missing is the consumer bridge turning that explicit error into the source's
little-o statement. This module supplies that bridge, and nothing more: it
does not construct the approximately independent family, and it keeps every
hypothesis of the quantitative theorem.

The probabilities are uniform counts over a nonempty finite seed space.
The decay statements use the real power `N^(1/4)`.

## Main statements

* `isolationError`: the explicit error of the quantitative isolation bound.
* `isolationError_scaled_tendsto_zero`: `N^(1/4) * isolationError k N` tends
  to zero, i.e. the error is `o(N^(-1/4))`.
* `lemma4_quantitative_littleO`: the quantitative comparison restated with
  `isolationError`.
* `lemma4_strict_eventually`: for every `δ > 0`, eventually
  `Pr[None] - δ * N^(-1/4) < Pr[Unique]`, the strict little-o form.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Qatlib.Papers.QWalkAmbainis03.Algorithm3.IsolationLittleO

open Filter
open scoped Topology
open Qatlib.Concepts.WalkFind.SearchAlgorithm

noncomputable section

/-- The explicit isolation error
`(1/2)^floor(log N) + 4/N + 16k^2(log N + 1)^2/sqrt N` appearing in the
quantitative retained-prefix comparison. -/
def isolationError (k N : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ (Nat.floor (Real.log (N : ℝ))) + 4 / (N : ℝ) +
    16 * (k : ℝ) ^ 2 * (Real.log (N : ℝ) + 1) ^ 2 / Real.sqrt (N : ℝ)

/-- A constant divided by a positive real power of the natural argument tends
to zero. This is the `p = 0` case of the library's logarithmic-power decay,
transported from `ℝ` to `ℕ`. -/
theorem tendsto_const_div_rpow_nat (s : ℝ) (hs : 0 < s) (c : ℝ) :
    Tendsto (fun N : ℕ => c / (N : ℝ) ^ s) atTop (nhds 0) := by
  have h := (logPower_div_rpow_tendsto 0 s hs).comp tendsto_natCast_atTop_atTop
  have hmul := h.const_mul c
  rw [mul_zero] at hmul
  refine hmul.congr (fun N => ?_)
  simp only [Function.comp_apply, pow_zero, div_eq_mul_inv, one_mul]

/-- Logarithmic powers divided by a positive real power of the natural
argument tend to zero, transported from `ℝ` to `ℕ`. -/
theorem tendsto_logPow_div_rpow_nat (p : ℕ) (s : ℝ) (hs : 0 < s) :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ)) ^ p / (N : ℝ) ^ s) atTop (nhds 0) :=
  (logPower_div_rpow_tendsto p s hs).comp tendsto_natCast_atTop_atTop

/-- The scaled geometric tail `N^(1/4) * (1/2)^floor(log N)` tends to zero:
the library's tail bound `2 / N^(log 2)` leaves the negative exponent
`1/4 - log 2`. -/
theorem scaled_geometric_tendsto_zero :
    Tendsto (fun N : ℕ => (N : ℝ) ^ ((1 : ℝ) / 4) *
      (1 / 2 : ℝ) ^ (Nat.floor (Real.log (N : ℝ)))) atTop (nhds 0) := by
  have hs : (0 : ℝ) < Real.log 2 - 1 / 4 := by
    have h := Real.log_two_gt_d9
    linarith
  have hg : Tendsto (fun N : ℕ => (2 : ℝ) / (N : ℝ) ^ (Real.log 2 - 1 / 4))
      atTop (nhds 0) :=
    tendsto_const_div_rpow_nat _ hs 2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    exact mul_nonneg (Real.rpow_nonneg hNpos.le _) (pow_nonneg (by norm_num) _)
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    have htail := binaryFloorLog_tail_bound (N : ℝ) hNpos
    have hstep : (N : ℝ) ^ ((1 : ℝ) / 4) *
        (1 / 2 : ℝ) ^ (Nat.floor (Real.log (N : ℝ))) ≤
        (N : ℝ) ^ ((1 : ℝ) / 4) * (2 / (N : ℝ) ^ (Real.log 2)) :=
      mul_le_mul_of_nonneg_left htail (Real.rpow_nonneg hNpos.le _)
    refine hstep.trans_eq ?_
    have hrw : (N : ℝ) ^ (Real.log 2) =
        (N : ℝ) ^ (Real.log 2 - 1 / 4) * (N : ℝ) ^ ((1 : ℝ) / 4) := by
      rw [← Real.rpow_add hNpos]
      congr 1
      ring
    have hp1 : (0 : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hNpos _
    have hp2 : (0 : ℝ) < (N : ℝ) ^ (Real.log 2 - 1 / 4) := Real.rpow_pos_of_pos hNpos _
    rw [hrw]
    field_simp [hp1.ne', hp2.ne']

/-- The scaled inverse term `N^(1/4) * (4/N) = 4 / N^(3/4)` tends to zero. -/
theorem scaled_inverse_tendsto_zero :
    Tendsto (fun N : ℕ => (N : ℝ) ^ ((1 : ℝ) / 4) * (4 / (N : ℝ))) atTop (nhds 0) := by
  have hg : Tendsto (fun N : ℕ => (4 : ℝ) / (N : ℝ) ^ ((3 : ℝ) / 4)) atTop (nhds 0) :=
    tendsto_const_div_rpow_nat _ (by norm_num) 4
  refine hg.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hprod : (N : ℝ) ^ ((3 : ℝ) / 4) * (N : ℝ) ^ ((1 : ℝ) / 4) = (N : ℝ) := by
    rw [← Real.rpow_add hNpos]
    norm_num
  have hp1 : (0 : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hNpos _
  have hp2 : (0 : ℝ) < (N : ℝ) ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hNpos _
  field_simp [hp1.ne', hp2.ne', hNpos.ne']
  nlinarith only [hprod]

/-- The scaled logarithmic term
`N^(1/4) * (16k^2(log N + 1)^2/sqrt N) = 16k^2(log N + 1)^2/N^(1/4)` tends to
zero for every fixed `k`, by expanding the square and applying logarithmic
decay at powers `2, 1, 0`. -/
theorem scaled_logarithmic_tendsto_zero (k : ℕ) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ ((1 : ℝ) / 4) *
      (16 * (k : ℝ) ^ 2 * (Real.log (N : ℝ) + 1) ^ 2 / Real.sqrt (N : ℝ)))
      atTop (nhds 0) := by
  have hs : (0 : ℝ) < (1 : ℝ) / 4 := by norm_num
  have h2 := tendsto_logPow_div_rpow_nat 2 _ hs
  have h1 := tendsto_logPow_div_rpow_nat 1 _ hs
  have h0 := tendsto_const_div_rpow_nat _ hs 1
  have hsum := (h2.add (h1.const_mul 2)).add h0
  have hmul := hsum.const_mul (16 * (k : ℝ) ^ 2)
  simp only [mul_zero, add_zero] at hmul
  refine hmul.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hsqrt : Real.sqrt (N : ℝ) = (N : ℝ) ^ ((1 : ℝ) / 2) :=
    Real.sqrt_eq_rpow _
  have hrw : (N : ℝ) ^ ((1 : ℝ) / 2) =
      (N : ℝ) ^ ((1 : ℝ) / 4) * (N : ℝ) ^ ((1 : ℝ) / 4) := by
    rw [← Real.rpow_add hNpos]
    norm_num
  have hp1 : (0 : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hNpos _
  rw [hsqrt, hrw]
  field_simp [hp1.ne']
  ring

/-- The isolation error is `o(N^(-1/4))`: scaling it by the true power
`N^(1/4)` gives a sequence tending to zero, for every fixed collision size
`k`. This is the analytic content of the `o(1/N^(1/4))` term in Lemma 4 of
[Ambainis2007ElementDistinctness]. -/
theorem isolationError_scaled_tendsto_zero (k : ℕ) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ ((1 : ℝ) / 4) * isolationError k N)
      atTop (nhds 0) := by
  have hsum := (scaled_geometric_tendsto_zero.add scaled_inverse_tendsto_zero).add
    (scaled_logarithmic_tendsto_zero k)
  rw [add_zero, add_zero] at hsum
  refine hsum.congr (fun N => ?_)
  unfold isolationError
  ring

/-- The isolation error is nonnegative at every positive scale. -/
theorem isolationError_nonneg (k : ℕ) {N : ℕ} (_hN : 1 ≤ N) :
    0 ≤ isolationError k N := by
  unfold isolationError
  positivity

/-- Threshold form of the little-o statement: for every `δ > 0` there is a
scale beyond which `isolationError k N ≤ δ * N^(-1/4)`, with the genuine real
power on the right. -/
theorem isolationError_eventually_le (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      isolationError k N ≤ δ * (N : ℝ) ^ (-(1 / 4 : ℝ)) := by
  have htend := isolationError_scaled_tendsto_zero k
  have hev : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ ((1 : ℝ) / 4) * isolationError k N < δ ∧ 1 ≤ N :=
    (htend.eventually (eventually_lt_nhds hδ)).and (eventually_ge_atTop 1)
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp hev
  refine ⟨N0, fun N hN => ?_⟩
  obtain ⟨hsmall, hN1⟩ := hN0 N hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hp : (0 : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hNpos _
  have hE : isolationError k N =
      ((N : ℝ) ^ ((1 : ℝ) / 4) * isolationError k N) / (N : ℝ) ^ ((1 : ℝ) / 4) := by
    field_simp [hp.ne']
  have hRHS : δ * (N : ℝ) ^ (-(1 / 4 : ℝ)) =
      δ / (N : ℝ) ^ ((1 : ℝ) / 4) := by
    simp only [Real.rpow_neg hNpos.le, div_eq_mul_inv]
  rw [hE, hRHS]
  exact (div_le_div_iff_of_pos_right hp).mpr (le_of_lt hsmall)

/-- The quantitative isolation comparison, restated with the named error
`isolationError`. Under the retained-prefix size guard `sqrt N ≤ |T|`, the
`d = ceil(2k log N)`-order approximate independence with parameter `1/N`, and
the presence of a `k`-collision in `T`, the no-collision retained probability
is at most the unique-collision retained probability plus
`isolationError k N`. This is exactly
`algorithm3Isolation_quantitative`; the naming is what the little-o bridge
consumes. -/
theorem lemma4_quantitative_littleO {q R M N : ℕ} (k : ℕ) (hk : 2 ≤ k)
    (hN : 0 < N) (hlog : 2 ≤ Real.log (N : ℝ)) (_hR : 0 < R) (_hM : 0 < M)
    (x : Fin q → ZMod M) (T : Finset (Fin q)) (π : Fin R → Equiv.Perm (Fin q))
    (hsqrt : Real.sqrt (N : ℝ) ≤ (T.card : ℝ))
    (hπ : ApproxIndependent (Nat.ceil (2 * (k : ℝ) * Real.log (N : ℝ))) (1 / (N : ℝ)) π)
    (hcollision : ∃ S, CollisionIn k x T S) :
    eventProbability (fun s => ¬ ∃ S, CollisionIn k x (retained k T π s) S) ≤
      eventProbability (fun s => ∃! S, CollisionIn k x (retained k T π s) S) +
        isolationError k N :=
  algorithm3Isolation_quantitative k hk hN hlog x T π hsqrt hπ hcollision

/-- The strict little-o form of Lemma 4 of [Ambainis2007ElementDistinctness]: for every
`δ > 0` there is a threshold beyond which, under the same size, approximate
independence and collision hypotheses as the quantitative comparison,

`Pr[None] - δ * N^(-1/4) < Pr[Unique]`.

Equivalently `Pr[Unique] > Pr[None] - o(N^(-1/4))` with the explicit error
`isolationError`. The approximately independent family itself is still
hypothesised, exactly as in the quantitative theorem; this bridge only
converts its finite error into the source's asymptotic strict inequality. -/
theorem lemma4_strict_eventually (k : ℕ) (hk : 2 ≤ k) :
    ∀ δ : ℝ, 0 < δ → ∃ N0 : ℕ, ∀ (N q R M : ℕ), N0 ≤ N → 0 < R → 0 < M →
      ∀ (x : Fin q → ZMod M) (T : Finset (Fin q)) (π : Fin R → Equiv.Perm (Fin q)),
        Real.sqrt (N : ℝ) ≤ (T.card : ℝ) →
        ApproxIndependent (Nat.ceil (2 * (k : ℝ) * Real.log (N : ℝ))) (1 / (N : ℝ)) π →
        (∃ S, CollisionIn k x T S) →
        eventProbability (fun s => ¬ ∃ S, CollisionIn k x (retained k T π s) S) -
            δ * (N : ℝ) ^ (-(1 / 4 : ℝ)) <
          eventProbability (fun s => ∃! S, CollisionIn k x (retained k T π s) S) := by
  intro δ hδ
  obtain ⟨N0, hN0⟩ := isolationError_eventually_le k (show (0 : ℝ) < δ / 2 by linarith)
  have hlogEventually : ∀ᶠ N : ℕ in atTop, 2 ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 2)
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp (hlogEventually.and (eventually_ge_atTop 1))
  refine ⟨max N0 N1, fun N q R M hNge hR hM x T π hsqrt hπ hcollision => ?_⟩
  have ⟨hlog, hNposNat⟩ := hN1 N ((le_max_right N0 N1).trans hNge)
  have hN : 0 < N := by omega
  have hquant := lemma4_quantitative_littleO k hk hN hlog hR hM x T π hsqrt hπ hcollision
  have hE := hN0 N ((le_max_left N0 N1).trans hNge)
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hpow : (0 : ℝ) < (N : ℝ) ^ (-(1 / 4 : ℝ)) := Real.rpow_pos_of_pos hNpos _
  have hpos : (0 : ℝ) < (δ / 2) * (N : ℝ) ^ (-(1 / 4 : ℝ)) :=
    mul_pos (by linarith) hpow
  linarith

end

end Qatlib.Papers.QWalkAmbainis03.Algorithm3.IsolationLittleO
