/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QIntegration00.MainResults.RandomQuantum

@[expose] public section

/-!
# Approximate oracle error in randomized integration

Novak's Section 4 combines the sampling, oracle, and quantum estimation errors.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QIntegration00.MainResults

open scoped Classical BigOperators
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib.Papers.QIntegration00.MainResults.RandomQuantum

/-- A pointwise error bound is preserved by averaging a nonempty finite sample. -/
theorem avgOracle_error {X : Type} {n : ℕ} (hn : 0 < n) (f g : X → ℝ)
    {δ : ℝ} (h : ∀ x, |f x - g x| ≤ δ) (ω : Fin n → X) :
    |FinDist.avg f ω - FinDist.avg g ω| ≤ δ := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [FinDist.avg, FinDist.avg, ← sub_div, ← Finset.sum_sub_distrib,
    abs_div, abs_of_pos hn', div_le_iff₀ hn']
  calc
    |∑ k, (f (ω k) - g (ω k))| ≤ ∑ k, |f (ω k) - g (ω k)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin n, δ := Finset.sum_le_sum fun k _ => h (ω k)
    _ = δ * n := by simp [mul_comm]

/-- With the oracle, sampling, and conditional estimation errors each at most
`ε/3`, the finite-distribution estimator is within `ε` with probability at least
`3/4` under the Section 4 sample-size and good-event hypotheses. -/
theorem section4_oracle {X : Type} [Fintype X] [DecidableEq X] {n : ℕ}
    (p : FinDist X) (f ftilde : X → ℝ) (hf : ∀ x, |f x| ≤ 1) (hn : 0 < n)
    {ε : ℝ} (hε : 0 < ε) (hn72 : 72 ≤ (n : ℝ) * ε ^ 2)
    (horacle : ∀ x, |f x - ftilde x| ≤ ε / 3) {A : (Fin n → X) → ℝ}
    (hquant : 7 / 8 ≤ FinDist.probEvent (L := n) p
      (fun ω => |A ω - FinDist.avg ftilde ω| ≤ ε / 3)) :
    3 / 4 ≤ FinDist.probEvent (L := n) p (fun ω => |A ω - p.expect f| ≤ ε) := by
  have hboth := two_good_event_mass p (good_event_mass p f hf hn hε hn72) hquant
  apply hboth.trans
  refine probEvent_mono p _ _ (fun ω hω => ?_)
  have hs := le_of_not_gt hω.1
  have ho := avgOracle_error hn f ftilde horacle ω
  rw [abs_sub_comm] at ho
  have hfirst := triangle_three hω.2 ho
  calc
    |A ω - p.expect f| =
      |(A ω - FinDist.avg f ω) + (FinDist.avg f ω - p.expect f)| := by
        congr 1
        ring
    _ ≤ |A ω - FinDist.avg f ω| + |FinDist.avg f ω - p.expect f| := abs_add_le _ _
    _ ≤ ε := by linarith

end Qatlib.Papers.QIntegration00.MainResults
