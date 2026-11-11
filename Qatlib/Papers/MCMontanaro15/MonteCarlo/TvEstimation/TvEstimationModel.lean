/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MCMontanaro15.MonteCarlo.MonteCarloDefs
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDistTV

set_option backward.isDefEq.respectTransparency false

/-!
# Section 4 objects: estimating the total variation distance from samples

Source: A. Montanaro, *Quantum speedup of Monte Carlo methods*,
arXiv:1504.06987v3, Section 4 (pp. 21–22).  Fixed PDF SHA256
`361ac540aeba94c89ad19bbd1c122c3a46e43b073522e155653dfb055e76c616`.

The source's §4 subroutine (printed as "Algorithm 5") draws `x` from the
averaged law `r = (p + q) / 2`, runs amplitude estimation with `t` queries to
read estimates `p̃(x)`, `q̃(x)` of the two masses, and outputs

`d̃(x) = |p̃(x) − q̃(x)| / (p̃(x) + q̃(x))`.

The objects below fix exactly that pipeline: the averaged sampling law
`avgLaw`, the exact integrand `tvIntegrand`, the estimator `TvEstimator` with
its per-seed output `TvEstimator.integrand`, and the three resource ledgers the
source multiplies (§4, p. 22):

* `tvGridIterations` — the amplitude-estimation depth `t = ⌈10√2π n^{1/2} ε^{−3/2}⌉`;
* `tvSubroutineSamples` — the subroutine's `O(√n ε^{−3/2} log(1/ε))` samples;
* `tvRepetitions` / `tvTotalSamples` / `tvHeadlineSamples` — the `O(1/ε)`
  repetitions of Theorem 3 and the paper's headline `O((√n/ε^{5/2}) log(1/ε) log(1/δ))`.

Nothing here asserts accuracy or cost: each definition is the vocabulary the
theorems in `TvEstimation` quantify over.
-/

set_option autoImplicit false

namespace Qatlib.Papers.MCMontanaro15.MonteCarlo.TvEstimation

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open scoped BigOperators

section Law

variable {X : Type} [Fintype X]

/-! ## The averaged sampling law `r = (p+q)/2` and the exact integrand -/

/-- The averaged law `r = (p + q) / 2` of Algorithm 5's first step. -/
noncomputable def avgLaw (p q : FinDist X) : FinDist X where
  prob x := (p.prob x + q.prob x) / 2
  nonneg x := by
    have hp := p.nonneg x
    have hq := q.nonneg x
    linarith
  sum_one := by
    calc ∑ x, (p.prob x + q.prob x) / 2
        = ∑ x, (p.prob x / 2 + q.prob x / 2) := by
          apply Finset.sum_congr rfl
          intro x _
          ring
      _ = (∑ x, p.prob x) / 2 + (∑ x, q.prob x) / 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_div, Finset.sum_div]
      _ = 1 := by
          rw [p.sum_one, q.sum_one]
          norm_num

/-- The mass of the averaged law at a point is `(p(x) + q(x)) / 2`. -/
theorem avgLaw_prob (p q : FinDist X) (x : X) :
    (avgLaw p q).prob x = (p.prob x + q.prob x) / 2 := rfl

/-- The source's integrand `d(x) = |p(x) − q(x)| / (p(x) + q(x))`, with the
value `0` at points where both masses vanish. -/
noncomputable def tvIntegrand (p q : FinDist X) (x : X) : ℝ :=
  if p.prob x + q.prob x = 0 then 0 else |p.prob x - q.prob x| / (p.prob x + q.prob x)

/-- At a point where both masses vanish the integrand is `0`. -/
theorem tvIntegrand_of_sum_eq_zero (p q : FinDist X) (x : X)
    (h : p.prob x + q.prob x = 0) : tvIntegrand p q x = 0 := by
  simp [tvIntegrand, h]

/-- At a point with positive total mass the integrand is the displayed quotient. -/
theorem tvIntegrand_of_sum_ne_zero (p q : FinDist X) (x : X)
    (h : p.prob x + q.prob x ≠ 0) :
    tvIntegrand p q x = |p.prob x - q.prob x| / (p.prob x + q.prob x) := by
  simp [tvIntegrand, h]

/-- The integrand is nonnegative: the output of Algorithm 5 is a `[0,1]` value. -/
theorem tvIntegrand_nonneg (p q : FinDist X) (x : X) : 0 ≤ tvIntegrand p q x := by
  unfold tvIntegrand
  split_ifs with h
  · exact le_refl 0
  · have hp := p.nonneg x
    have hq := q.nonneg x
    have hpos : 0 < p.prob x + q.prob x := lt_of_le_of_ne (by linarith) (Ne.symm h)
    positivity

/-- The integrand takes values in `[0,1]`, the bound the source uses when it
replaces one term of the sum by `1`. -/
theorem tvIntegrand_le_one (p q : FinDist X) (x : X) : tvIntegrand p q x ≤ 1 := by
  unfold tvIntegrand
  split_ifs with h
  · norm_num
  · have hp := p.nonneg x
    have hq := q.nonneg x
    have hpos : 0 < p.prob x + q.prob x := lt_of_le_of_ne (by linarith) (Ne.symm h)
    have habs : |p.prob x - q.prob x| ≤ p.prob x + q.prob x := by
      rw [abs_sub_le_iff]
      constructor <;> linarith
    rw [div_le_one hpos]
    exact habs

end Law

/-! ## The estimator law of Algorithm 5 -/

section Estimator

variable {X : Type}

/-- One run of Algorithm 5: a seed law for the amplitude-estimation randomness
together with the two read-out families `p̃(·)`, `q̃(·)`, each a `[0,1]` value. -/
structure TvEstimator (X : Type*) (L : ℕ) where
  /-- The law of the seed driving the two amplitude-estimation calls. -/
  seedLaw : FinDist (Fin L)
  /-- The amplitude-estimation read-out for the mass of `p` at `x`. -/
  pe : X → Fin L → ℝ
  /-- The amplitude-estimation read-out for the mass of `q` at `x`. -/
  qe : X → Fin L → ℝ
  /-- Amplitude estimation returns a probability, hence a nonnegative value. -/
  pe_nonneg : ∀ x s, 0 ≤ pe x s
  /-- Amplitude estimation returns a probability, hence a value at most one. -/
  pe_le_one : ∀ x s, pe x s ≤ 1
  /-- Amplitude estimation returns a probability, hence a nonnegative value. -/
  qe_nonneg : ∀ x s, 0 ≤ qe x s
  /-- Amplitude estimation returns a probability, hence a value at most one. -/
  qe_le_one : ∀ x s, qe x s ≤ 1

/-- The output of Algorithm 5 at outcome `x` and seed `s`:
`d̃(x) = |p̃(x) − q̃(x)| / (p̃(x) + q̃(x))`, with the value `0` if both read-outs vanish. -/
noncomputable def TvEstimator.integrand {L : ℕ} (A : TvEstimator X L)
    (x : X) (s : Fin L) : ℝ :=
  if A.pe x s + A.qe x s = 0 then 0 else |A.pe x s - A.qe x s| / (A.pe x s + A.qe x s)

/-- The measured output is nonnegative. -/
theorem TvEstimator.integrand_nonneg {L : ℕ} (A : TvEstimator X L) (x : X) (s : Fin L) :
    0 ≤ A.integrand x s := by
  unfold TvEstimator.integrand
  split_ifs with h
  · exact le_refl 0
  · have hp := A.pe_nonneg x s
    have hq := A.qe_nonneg x s
    have hpos : 0 < A.pe x s + A.qe x s := lt_of_le_of_ne (by linarith) (Ne.symm h)
    positivity

/-- The measured output is at most one, because both read-outs are probabilities. -/
theorem TvEstimator.integrand_le_one {L : ℕ} (A : TvEstimator X L) (x : X) (s : Fin L) :
    A.integrand x s ≤ 1 := by
  unfold TvEstimator.integrand
  split_ifs with h
  · norm_num
  · have hp := A.pe_nonneg x s
    have hq := A.qe_nonneg x s
    have hpos : 0 < A.pe x s + A.qe x s := lt_of_le_of_ne (by linarith) (Ne.symm h)
    have habs : |A.pe x s - A.qe x s| ≤ A.pe x s + A.qe x s := by
      rw [abs_sub_le_iff]
      constructor <;> linarith
    rw [div_le_one hpos]
    exact habs

end Estimator

section Means

variable {X : Type} [Fintype X]

/-- The expectation of the read-out over the seed law: the mean output of
Algorithm 5 at outcome `x`. -/
noncomputable def TvEstimator.conditionalMean {L : ℕ} (A : TvEstimator X L)
    (x : X) : ℝ :=
  A.seedLaw.expect (fun s => A.integrand x s)

/-- The expectation of Algorithm 5's output over `x ~ r` and the seed: the
source's `Ẽ`. -/
noncomputable def TvEstimator.outputMean {L : ℕ} (p q : FinDist X)
    (A : TvEstimator X L) : ℝ :=
  (avgLaw p q).expect (fun x => A.conditionalMean x)

/-- The exact value `E = ‖p − q‖` the subroutine is aiming at. -/
noncomputable def tvExactMean (p q : FinDist X) : ℝ :=
  (avgLaw p q).expect (tvIntegrand p q)

/-- Mass of the seed outcomes on which `G` fails, as the expectation of the
indicator of the complement of `G`. -/
noncomputable def badMass {L : ℕ} (μ : FinDist (Fin L)) (G : Fin L → Prop) : ℝ := by
  classical
  exact μ.expect (fun s => if G s then 0 else 1)

/-! ## The amplitude-estimation guarantee and the source's error event -/

/-- The source's per-outcome amplitude-estimation guarantee (Theorem 2 of the
paper): at outcome `x` the read-out of the mass of a distribution `w` is within
`2π√(w(1−w))/t + π²/t²` of the true mass. -/
def aeClose (w : X → ℝ) (t : ℝ) (a : ℝ) (x : X) : Prop :=
  |a - w x| ≤ 2 * Real.pi * Real.sqrt (w x * (1 - w x)) / t + Real.pi ^ 2 / t ^ 2

/-- The seed outcomes at outcome `x` on which *both* amplitude-estimation calls
of Algorithm 5 obey Theorem 2's error bound. -/
def aeGood {L : ℕ} (p q : FinDist X) (t : ℝ) (A : TvEstimator X L)
    (x : X) (s : Fin L) : Prop :=
  aeClose p.prob t (A.pe x s) x ∧ aeClose q.prob t (A.qe x s) x

/-! ## The resource ledgers of §4 -/

/-- The amplitude-estimation depth of §4: `t = ⌈10√2π n^{1/2} ε^{−3/2}⌉`,
stated as its real value `10√2π√n / (ε√ε)` (the source's ceiling only helps). -/
noncomputable def tvGridIterations (n : ℕ) (eps : ℝ) : ℝ :=
  10 * Real.sqrt 2 * Real.pi * Real.sqrt n / (eps * Real.sqrt eps)

/-- The subroutine's sample count `O(√n ε^{−3/2} log(1/ε))`. -/
noncomputable def tvSubroutineSamples (n : ℕ) (eps : ℝ) : ℝ :=
  Real.sqrt n / (eps * Real.sqrt eps) * Real.log (1 / eps)

/-- Theorem 3's repetition count at additive accuracy `ε` and failure `δ`:
`O((1/ε) log(1/δ))`, valid because the subroutine's output lies in `[0,1]`. -/
noncomputable def tvRepetitions (eps delta : ℝ) : ℝ :=
  (1 / eps) * Real.log (1 / delta)

/-- The whole §4 pipeline at internal precision `ε/8`: the subroutine runs at
precision `ε/8` (so its bias is at most `ε/2`), then Theorem 3 repeats it
`O((1/ε) log(1/δ))` times to bring the failure down to `δ`. -/
noncomputable def tvTotalSamples (n : ℕ) (eps delta : ℝ) : ℝ :=
  tvSubroutineSamples n (eps / 8) * tvRepetitions eps delta

/-- The paper's headline complexity `O((√n/ε^{5/2}) log(1/ε) log(1/δ))`. -/
noncomputable def tvHeadlineSamples (n : ℕ) (eps delta : ℝ) : ℝ :=
  Real.sqrt n / (eps ^ 2 * Real.sqrt eps) * Real.log (1 / eps) * Real.log (1 / delta)

end Means

end Qatlib.Papers.MCMontanaro15.MonteCarlo.TvEstimation
