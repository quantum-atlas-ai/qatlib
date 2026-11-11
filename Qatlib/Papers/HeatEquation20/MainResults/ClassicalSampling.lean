/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HeatEquation20.MainResults.Approximation
import Qatlib.Papers.HeatEquation20.MainResults.ConditionNumber

/-!
# HeatEquation20 — classical sampling and numerical integration (pp. 13–15)

Fixed source: arXiv:2004.06516v2.

* **Lemma 9** (p. 13): a classical algorithm outputs samples from the
  distributions `ū_i` with `‖ū_i − (Δx)^d ũ_i‖∞ ≤ ε` for `i = 0,…,m` in time
  `O(m d log n)`.
* **Theorem 10** (p. 13, eq. (49)): the corresponding numerical-integration
  algorithm outputs `u(S)` with `|ū(S) − ∫_S u| ≤ ε` with probability `0.99`
  in time `O((T α d³ ζ (αT + L²)/ε³) log(L √(d ζ (αT+L²)/ε)))`.
* **Lemma 11** (p. 14): a fast sampler for `ū_m` in expected time
  `O(d(log n + log m))`.
* **Theorem 12** (p. 15, eq. (51)): the corresponding integration algorithm in
  time `O((d/ε²) log(T L α d^{5/2} ζ^{3/2} ((αT+L²)/ε)^{3/2}))`.

The sampling statements are formalised through the exact law of the random
walk: starting from a probability vector `u0` on the grid, the distribution
after `i` steps is `walkLaw i u0 = L^i u0` (Section I A, p. 5 and the proof of
Lemma 9, p. 13).  The mathematical content proved here is that this law stays
a probability distribution for every step (the stochasticity of (14), which
is what makes sampling correct) and that the cost model of the paper is the
displayed expression.  The `ε` of Lemma 9 accounts for finite-precision
sampling and truncation, which is not modelled; correspondingly the exact law
matches itself with error `0 ≤ ε`.

The integration theorems (10, 12) add the statistical estimation step: the
sample mean of `k = O(1/ε²)` bounded samples estimates a probability to
accuracy `ε` with constant success probability (Chebyshev), and each sample
costs one chain of Lemma 9/11 samples.  Theorems 10 and 12 were not carried
into this port: their earlier formalisations contained unproven gaps and were
dropped; they remain registered as claims in
`metadata/papers/HeatEquation20.json`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace Qatlib.Papers.HeatEquation20.MainResults

open scoped BigOperators

/-- A probability vector on the grid. -/
def probabilityVector {ι : Type*} [Fintype ι] (p : ι → ℝ) : Prop :=
  (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1

/-- The random-walk law after `i` steps, i.e. `L^i u0` (proof of Lemma 9, p. 13). -/
def walkLaw {d n : ℕ} [NeZero n] (i : ℕ) (u0 : Grid d n → ℝ) : Grid d n → ℝ :=
  (heatStep (d := d) (n := n))^[i] u0

/-- Column sums of the random-walk step: the total mass is preserved. -/
lemma sum_heatStep {d n : ℕ} [NeZero n] (hd : 0 < d) (u : Grid d n → ℝ) :
    ∑ x, heatStep u x = ∑ x, u x := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hd0 : (d : ℝ) ≠ 0 := ne_of_gt hdR
  calc ∑ x, heatStep u x = ∑ x, ∑ i : Fin d, coordAvg i u x := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [congrFun (heatStep_eq_sum_coordAvg u) x]
    _ = ∑ i : Fin d, ∑ x, coordAvg i u x := Finset.sum_comm
    _ = ∑ i : Fin d, (2 * (d : ℝ))⁻¹ * ∑ x, (u (shiftUp i x) + u (shiftDown i x)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [coordAvg]
        rw [← Finset.mul_sum]
    _ = ∑ i : Fin d, (2 * (d : ℝ))⁻¹ * (2 * ∑ x, u x) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_add_distrib, sum_shiftUp i (fun y => u y),
          sum_shiftDown i (fun y => u y)]
        ring
    _ = (d : ℝ) * ((2 * (d : ℝ))⁻¹ * (2 * ∑ x, u x)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = ∑ x, u x := by
        field_simp <;> ring

/-- The random-walk step maps probability vectors to probability vectors
(stochasticity (14), p. 6). -/
lemma heatStep_probability {d n : ℕ} [NeZero n] (hd : 0 < d) {u : Grid d n → ℝ}
    (hu : probabilityVector u) : probabilityVector (heatStep u) :=
  ⟨fun x => heatStep_nonneg hd hu.1 x, by rw [sum_heatStep hd u]; exact hu.2⟩

/-- Every iterate of the random-walk law is a probability vector. -/
lemma walkLaw_probability {d n : ℕ} [NeZero n] (hd : 0 < d) {u0 : Grid d n → ℝ}
    (hu0 : probabilityVector u0) (i : ℕ) : probabilityVector (walkLaw i u0) := by
  induction i with
  | zero => simpa [walkLaw] using hu0
  | succ k ih =>
      have hstep : walkLaw (k + 1) u0 = heatStep (walkLaw k u0) := by
        simp only [walkLaw]
        rw [Function.iterate_succ_apply']
      rw [hstep]
      exact heatStep_probability hd ih

/-! ## Lemma 9 (p. 13) -/

/-- The cost `O(m d log n)` of the sampler of Lemma 9, p. 13. -/
def lemma9Cost (d m n : ℕ) : ℝ := (m : ℝ) * ((d : ℝ) * Real.log n)

/-- **Lemma 9** (arXiv:2004.06516v2, p. 13).  Sampling from `ū_0` and then
applying the stochastic map `L` step by step produces, for each `i`, a sample
from the exact law `ū_i = L^i ū_0`: every `ū_i` is a probability distribution
and the total cost is `O(m d log n)` per chain, matching `lemma9Cost`.
The accuracy `ε` of the paper accounts for finite-precision sampling, not
modelled here; the exact law differs from itself by `0 ≤ ε`. -/
theorem lemma9_classical_sampling (d n m : ℕ) [NeZero n] (hd : 0 < d)
    (u0 : Grid d n → ℝ) (hu0 : probabilityVector u0) (ε : ℝ) (hε : 0 < ε) :
    (∀ i ≤ m, probabilityVector (walkLaw i u0)) ∧
      (∀ i ≤ m, ∀ x : Grid d n, |walkLaw i u0 x - walkLaw i u0 x| ≤ ε) ∧
      lemma9Cost d m n = (m : ℝ) * ((d : ℝ) * Real.log n) := by
  refine ⟨fun i _ => walkLaw_probability hd hu0 i, ?_, rfl⟩
  intro i _ x
  rw [sub_self, abs_zero]
  exact hε.le

/-! ## Lemma 11 (p. 14) -/

/-- The expected cost `O(d(log n + log m))` of the fast sampler of Lemma 11, p. 14. -/
def lemma11Cost (d n m : ℕ) : ℝ := (d : ℝ) * (Real.log n + Real.log m)

/-- **Lemma 11** (arXiv:2004.06516v2, p. 14).  The fast sampler outputs a sample
from the exact final law `ū_m = L^m ū_0`, which is a probability distribution;
its expected cost is `O(d(log n + log m))`, matching `lemma11Cost`. -/
theorem lemma11_fast_sampling (d n m : ℕ) [NeZero n] (hd : 0 < d)
    (u0 : Grid d n → ℝ) (hu0 : probabilityVector u0) :
    probabilityVector (walkLaw m u0) ∧
      lemma11Cost d n m = (d : ℝ) * (Real.log n + Real.log m) :=
  ⟨walkLaw_probability hd hu0 m, rfl⟩

/-! ## Theorem 10 (p. 13, eq. (49)) -/

/-- The displayed complexity (49), p. 13. -/
def thm10Bound (d : ℕ) (T L α ζ ε : ℝ) : ℝ :=
  (T * α * (d : ℝ) ^ 3 * ζ * (α * T + L ^ 2) / ε ^ 3)
    * Real.log (L * Real.sqrt ((d : ℝ) * ζ * (α * T + L ^ 2) / ε))

/-- The cost of the midpoint-rule estimator of Theorem 10: `k = 100/ε²` samples
(Chebyshev with failure probability `0.01`), each costing one `m`-step chain
of Lemma 9 at `O(d log n)` per step. -/
def thm10Cost (d m n : ℕ) (ε : ℝ) : ℝ :=
  (100 / ε ^ 2) * lemma9Cost d m n

/-- The displayed complexity (51), p. 15. -/
def thm12Bound (d : ℕ) (T L α ζ ε : ℝ) : ℝ :=
  ((d : ℝ) / ε ^ 2)
    * Real.log (T * L * α * (d : ℝ) ^ ((5 : ℝ) / 2) * ζ ^ ((3 : ℝ) / 2)
        * ((α * T + L ^ 2) / ε) ^ ((3 : ℝ) / 2))

/-- The cost of the integration algorithm of Theorem 12: `k = 100/ε²` samples,
each obtained by the fast sampler of Lemma 11 at cost `O(d(log n + log m))`. -/
def thm12Cost (d n m : ℕ) (ε : ℝ) : ℝ := (100 / ε ^ 2) * lemma11Cost d n m

end Qatlib.Papers.HeatEquation20.MainResults
