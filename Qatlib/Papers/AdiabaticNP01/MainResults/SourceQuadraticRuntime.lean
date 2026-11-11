/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabaticNP01.MainResults.SourceRepetition
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Topology.Order.OrderClosed

set_option backward.isDefEq.respectTransparency false

/-!
# AdiabaticNP01 — quadratic running time on gusa Exact Cover instances (Claim `c001`)

Source: E. Farhi, J. Goldstone, S. Gutmann, J. Lapan, A. Lundgren, D. Preda,
arXiv:quant-ph/0104129v1 (2001), §1 p. 2, §9 "The median time to achieve
probability 1/8" p. 7, §10 "Probabilities of success at a proposed running
time" p. 8, and Figures 1–2.

Claim `c001`: *"For our randomly generated instances of Exact Cover we find that
the quantum algorithm succeeds in a time that grows only quadratically in the
length of the input."*  The paper's operational statement (§9, p. 7) is:

* for each `n` between 10 and 20, 75 gusa instances were simulated, and the
  **median time to reach success probability 1/8** was recorded;
* a quadratic fit `T(n) = a n² + b n + c` to these medians is the solid line of
  Figure 1 (§9, p. 7);
* at the proposed instance-independent runtime `T(n)` the medians are close to
  `1/8` and the lowest probabilities do not decrease appreciably with `n`
  (§10, p. 8, Figure 2).

Because Figure 1 is a plot and the individual median values are not tabulated in
the paper, the Lean formalisation separates the two ingredients:

* `exists_quadratic_upper_bound_on_finite_sample`: on any finite sample the
  recorded medians are dominated by *some* quadratic with positive leading
  coefficient (this is the finite-sample content of "the solid line is a
  quadratic fit to the data"); the paper's empirical assertion that the natural
  fit is quadratic is a numerical observation, not a theorem;
* `quadratic_runtime_of_persistent_fit`: **if** the quadratic bound persists for
  all `n ≥ 10` — the paper's explicit hypothesis "imagine that this quadratic
  behavior actually persists", §1 p. 2 — **then** the median runtime is `O(n²)`;
* `repetitions_reach_target_at_quadratic_time`: at runtime `T(n)` with per-run
  success probability at least `1/8` on `10 ≤ n ≤ 20`, a fixed number of
  repetitions (independent of `n`) achieves any target confidence, using §10.

No `sorry`, no `admit`, no additional axioms.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.AdiabaticNP01.MainResults

open Asymptotics

/-- The quadratic runtime model `T(n) = a n² + b n + c` of the fit in Figure 1
(§9, p. 7). -/
def QuadraticFit (a b c : ℝ) (n : ℕ) : ℝ :=
  a * (n : ℝ) ^ 2 + b * (n : ℝ) + c

/-- For `n ≥ 1` the quadratic fit is bounded by `(|a| + |b| + |c|) n²`. -/
theorem quadraticFit_le_abs (a b c : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    QuadraticFit a b c n ≤ (|a| + |b| + |c|) * (n : ℝ) ^ 2 := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by linarith
  have hsq : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have ha : a * (n : ℝ) ^ 2 ≤ |a| * (n : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_right (le_abs_self a) (sq_nonneg _)
  have hb : b * (n : ℝ) ≤ |b| * (n : ℝ) :=
    mul_le_mul_of_nonneg_right (le_abs_self b) hn0
  have hnle : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hb2 : |b| * (n : ℝ) ≤ |b| * (n : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_left hnle (abs_nonneg b)
  have hc : c ≤ |c| * (n : ℝ) ^ 2 := by
    calc c ≤ |c| := le_abs_self c
      _ = |c| * 1 := by ring
      _ ≤ |c| * (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hsq (abs_nonneg c)
  unfold QuadraticFit
  nlinarith [ha, hb, hb2, hc]

/-- A quadratic fit is `O(n²)` at infinity. -/
theorem quadraticFit_isBigO (a b c : ℝ) :
    (fun n : ℕ => QuadraticFit a b c n) =O[Filter.atTop] (fun n : ℕ => (n : ℝ) ^ 2) := by
  refine IsBigO.of_bound (|a| + |b| + |c|) ?_
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
  have hle := quadraticFit_le_abs a b c hn
  have hneg : -QuadraticFit a b c n ≤ (|a| + |b| + |c|) * (n : ℝ) ^ 2 := by
    have h' := quadraticFit_le_abs (-a) (-b) (-c) (n := n) hn
    have hcoef : (|-a| + |-b| + |-c| : ℝ) = |a| + |b| + |c| := by simp
    rw [hcoef] at h'
    unfold QuadraticFit at h'
    have hring : (-a) * (n : ℝ) ^ 2 + (-b) * (n : ℝ) + (-c)
        = -QuadraticFit a b c n := by unfold QuadraticFit; ring
    rwa [hring] at h'
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (sq_nonneg (n : ℝ))]
  exact abs_le.mpr ⟨by linarith [hneg], hle⟩

/-- If a runtime function is nonnegative and eventually dominated by a quadratic
fit, its growth is `O(n²)`.  This is the formal content of "the running time grows
only quadratically in the length of the input" (§1, p. 2), under the persistence
hypothesis made in the paper. -/
theorem quadratic_runtime_of_persistent_fit (med : ℕ → ℝ) (a b c : ℝ)
    (hmed0 : ∀ n, 0 ≤ med n)
    (hfit : ∀ᶠ n : ℕ in Filter.atTop, med n ≤ QuadraticFit a b c n) :
    med =O[Filter.atTop] (fun n : ℕ => (n : ℝ) ^ 2) := by
  refine IsBigO.of_bound (|a| + |b| + |c|) ?_
  filter_upwards [hfit, Filter.eventually_ge_atTop (1 : ℕ)] with n hfn hn
  have hle := quadraticFit_le_abs a b c hn
  rw [Real.norm_of_nonneg (hmed0 n), Real.norm_of_nonneg (sq_nonneg (n : ℝ))]
  exact le_trans hfn hle

/-- On the finite sample `n ∈ {10, …, 20}` every recorded median runtime admits a
quadratic upper bound with positive leading coefficient.  (The individual medians
of Figure 1 are not tabulated; the paper reports only the quadratic fit, so the
Lean statement records the finite-sample domination that any fit provides.) -/
theorem exists_quadratic_upper_bound_on_finite_sample (med : ℕ → ℝ) :
    ∃ a b c : ℝ, 0 < a ∧ ∀ n ∈ Finset.Icc 10 20, med n ≤ QuadraticFit a b c n := by
  let s : Finset ℕ := Finset.Icc 10 20
  have hs : s.Nonempty := ⟨10, by simp [s]⟩
  let M : ℝ := s.sup' hs (fun n => |med n|)
  have hM0 : 0 ≤ M := by
    have h10 : |med 10| ≤ M := Finset.le_sup' (fun n => |med n|) (by simp [s])
    exact le_trans (abs_nonneg _) h10
  refine ⟨M + 1, 0, 0, by linarith, ?_⟩
  intro n hn
  have hM : |med n| ≤ M := Finset.le_sup' (fun n => |med n|) hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
    have : 1 ≤ n := by
      have := (Finset.mem_Icc.mp hn).1
      omega
    exact_mod_cast this
  have hsq : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hMsq : M ≤ M * (n : ℝ) ^ 2 := by
    calc M = M * 1 := by ring
      _ ≤ M * (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hsq hM0
  have hbound : M ≤ (M + 1) * (n : ℝ) ^ 2 := by nlinarith [hMsq, hsq]
  calc med n ≤ |med n| := le_abs_self _
    _ ≤ M := hM
    _ ≤ (M + 1) * (n : ℝ) ^ 2 := hbound
    _ = QuadraticFit (M + 1) 0 0 n := by unfold QuadraticFit; ring

/-- §10, p. 8: at the quadratic runtime `T(n)`, with per-run success probability at
least `1/8` for every `10 ≤ n ≤ 20`, a repetition count `k` independent of `n`
achieves any target confidence `1 − ε` on all those instance sizes.  Together with
`quadratic_runtime_of_persistent_fit` this is the formal content of Claim `c001`:
quadratic runtime plus fixed repetition gives a fixed confidence. -/
theorem repetitions_reach_target_at_quadratic_time
    (p : ℕ → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hp_lo : ∀ n ∈ Finset.Icc 10 20, (1 / 8 : ℝ) ≤ p n)
    (hp_hi : ∀ n ∈ Finset.Icc 10 20, p n ≤ 1) :
    ∃ k : ℕ, ∀ n ∈ Finset.Icc 10 20, 1 - ε ≤ repetitionSuccessProbability (p n) k := by
  obtain ⟨k, hk⟩ := exists_repetitions_meeting_target
    (p := 1 / 8) (by norm_num) (by norm_num) hε
  refine ⟨k, ?_⟩
  intro n hn
  have hlo := hp_lo n hn
  have hhi := hp_hi n hn
  have hfail : failureProbability (p n) k ≤ failureProbability (1 / 8) k :=
    failureProbability_anti (by linarith) hlo hhi k
  unfold repetitionSuccessProbability
  linarith [hk, hfail]

/-- **Claim `c001` — quadratic runtime on gusa instances.**  The recorded median
runtimes are eventually quadratic (`hfit`, the persistence hypothesis of §1 p. 2),
with positive leading coefficient, and at the proposed runtime `T(n)` the per-run
success probability on `10 ≤ n ≤ 20` is at least `1/8` and at most `1`.  Then the
median runtime is `O(n²)` and a fixed number of repetitions attains any target
confidence on the whole observed range. -/
theorem main_quadratic_runtime
    (med p : ℕ → ℝ) (a b c : ℝ) (ha : 0 < a)
    (hmed0 : ∀ n, 0 ≤ med n)
    (hfit : ∀ᶠ n : ℕ in Filter.atTop, med n ≤ QuadraticFit a b c n)
    {ε : ℝ} (hε : 0 < ε)
    (hp_lo : ∀ n ∈ Finset.Icc 10 20, (1 / 8 : ℝ) ≤ p n)
    (hp_hi : ∀ n ∈ Finset.Icc 10 20, p n ≤ 1) :
    (med =O[Filter.atTop] (fun n : ℕ => (n : ℝ) ^ 2)) ∧
      (∃ k : ℕ, ∀ n ∈ Finset.Icc 10 20,
        1 - ε ≤ repetitionSuccessProbability (p n) k) :=
  ⟨quadratic_runtime_of_persistent_fit med a b c hmed0 hfit,
    repetitions_reach_target_at_quadratic_time p hε hp_lo hp_hi⟩

end Qatlib.Papers.AdiabaticNP01.MainResults
