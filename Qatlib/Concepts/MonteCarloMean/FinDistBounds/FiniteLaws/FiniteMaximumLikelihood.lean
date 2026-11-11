/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteLaws.FiniteLikelihoodConcentration

/-!
# Maximum likelihood decoding over finite candidates

This module implements a finite maximum score scan and uses it to define `decode`, a maximum
likelihood decoder for a nonempty indexed family. It proves maximality, a support based error
bound, and a sum of exponential error bounds from bounded log likelihood ratios. The statistical
decision setting is described in [Helstrom1976].

## Main statements

* `decode_maximal`: The selected candidate has record likelihood at least as large as every
  other candidate.
* `support_error_bound`: Under the true candidate law, maximum likelihood decoding error is at
  most the sum over incorrect candidates of the true mass on their supports raised to the record
  length.
* `log_error_bound`: For positive record length and strictly positive candidate masses, the
  specified bounded log ratios and negative mean gaps bound decoding error by the sum of `exp
  (-2 * n * (d c) ^ 2 / (b c - a c) ^ 2)` over incorrect candidates.

## References

* [Helstrom, 1976][Helstrom1976]
-/

set_option autoImplicit false
namespace Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteMaximumLikelihood
open scoped Classical BigOperators
noncomputable section
variable {X : Type} [Fintype X] [DecidableEq X]

/-- A recursive maximum score scan over a list, starting from a given candidate and retaining
the current candidate on ties. -/
def scan {C : Type} (score : C → ℝ) : C → List C → C
  | best, [] => best
  | best, c::cs => scan score (if score best < score c then c else best) cs

/-- The score of one comparison step is at least the score of the current candidate. -/
private theorem step_ge_left {C : Type} (score : C → ℝ) (b c : C) :
    score b ≤ score (if score b < score c then c else b) := by split_ifs <;> linarith

/-- The score of one comparison step is at least the score of the challenger. -/
private theorem step_ge_right {C : Type} (score : C → ℝ) (b c : C) :
    score c ≤ score (if score b < score c then c else b) := by split_ifs <;> linarith

/-- The candidate returned by the score scan has score at least that of its starting candidate. -/
theorem scan_ge_start {C : Type} (score : C → ℝ) (cs : List C) (b : C) :
    score b ≤ score (scan score b cs) := by
  induction cs generalizing b with
  | nil => exact le_refl _
  | cons c cs ih => exact (step_ge_left score b c).trans (ih _)

/-- The candidate returned by the score scan has score at least that of every member of the
scanned list. -/
theorem scan_ge_member {C : Type} (score : C → ℝ) (cs : List C) (b c : C)
    (hc : c ∈ cs) : score c ≤ score (scan score b cs) := by
  induction cs generalizing b with
  | nil => simp at hc
  | cons a cs ih =>
    rcases List.mem_cons.mp hc with rfl | h
    · exact (step_ge_right score b c).trans (scan_ge_start score cs _)
    · exact ih _ h

/-- A maximum likelihood candidate for the observed record, obtained by scanning all indices in
the nonempty family and starting at index zero. -/
def decode {m n : ℕ} (q : Fin (m+1) → Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) (w : Fin n → X) : Fin (m+1) :=
  scan (fun c => (q c).probOf w) 0 (List.ofFn (fun c : Fin (m+1) => c))

omit [DecidableEq X] in

/-- The selected candidate has record likelihood at least as large as every other candidate. -/
theorem decode_maximal {m n : ℕ} (q : Fin (m+1) → Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X)
    (w : Fin n → X) (c : Fin (m+1)) :
    (q c).probOf w ≤ (q (decode q w)).probOf w :=
  scan_ge_member (fun c => (q c).probOf w) (List.ofFn (fun c : Fin (m+1) => c)) 0 c
    (List.mem_ofFn.mpr ⟨c, rfl⟩)

/-- Under the true candidate law, maximum likelihood decoding error is at most the sum over
incorrect candidates of the true mass on their supports raised to the record length. -/
theorem support_error_bound {m n : ℕ} (q : Fin (m+1) → Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X)
    (truth : Fin (m+1)) :
    (q truth).probEvent (fun w : Fin n → X => decode q w ≠ truth) ≤
      ∑ c with c ≠ truth,
        (∑ x with (q c).prob x ≠ 0, (q truth).prob x)^n := by
  exact FiniteLikelihood.decoder_error_bound (q truth) q truth (decode q)
    (fun w _ => decode_maximal q w truth)

omit [DecidableEq X] in

/-- Inclusion of decidable sample record events implies monotonicity of their probabilities. -/
private theorem event_mono (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) {n : ℕ}
    (E F : (Fin n → X) → Prop) [DecidablePred E] [DecidablePred F]
    (h : ∀ w, E w → F w) : p.probEvent E ≤ p.probEvent F := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro w hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h w (Finset.mem_filter.mp hw).2⟩
  · intro w _ _
    exact Finset.prod_nonneg fun i _ => p.nonneg _

/-- For positive record length and strictly positive candidate masses, the specified bounded log
ratios and negative mean gaps bound decoding error by the sum of `exp (-2 * n * (d c) ^ 2 /
(b c - a c) ^ 2)` over incorrect candidates. -/
theorem log_error_bound {m n : ℕ} (q : Fin (m+1) → Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X)
    (truth : Fin (m+1)) (a b d : Fin (m+1) → ℝ)
    (hpos : ∀ c x, 0 < (q c).prob x) (hn : 0 < n)
    (hab : ∀ c, c ≠ truth → a c < b c) (hd : ∀ c, c ≠ truth → 0 < d c)
    (hrange : ∀ c, c ≠ truth → ∀ x,
      Real.log ((q c).prob x)-Real.log ((q truth).prob x) ∈ Set.Icc (a c) (b c))
    (hmean : ∀ c, c ≠ truth → (q truth).expect
      (fun x => Real.log ((q c).prob x)-Real.log ((q truth).prob x)) = -d c) :
    (q truth).probEvent (fun w : Fin n → X => decode q w ≠ truth) ≤
      ∑ c with c ≠ truth, Real.exp (-2*(n : ℝ)*(d c)^2/(b c-a c)^2) := by
  let E := fun c (w : Fin n → X) => c ≠ truth ∧
    (q truth).probOf w ≤ (q c).probOf w
  have hu := (q truth).union_bound E
  have hm := event_mono (q truth) (fun w => decode q w ≠ truth)
    (fun w => ∃ c, E c w) (fun w hw => ⟨decode q w, hw, decode_maximal q w truth⟩)
  suffices hb : (∑ c, (q truth).probEvent (E c)) ≤
      ∑ c with c ≠ truth, Real.exp (-2*(n : ℝ)*(d c)^2/(b c-a c)^2) by
    exact hm.trans (hu.trans hb)
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro c _
  by_cases hc : c = truth
  · subst c
    simp [E, Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent]
  · rw [if_pos hc]
    exact (event_mono (q truth) (E c)
      (fun w => (q truth).probOf w ≤ (q c).probOf w) (fun _ h => h.2)).trans
      (FiniteLikelihoodConcentration.log_likelihood_bound (q truth) (q c) n
        (a c) (b c) (d c) (hpos truth) (hpos c) hn (hab c hc) (hd c hc)
        (hrange c hc) (hmean c hc))

end
end Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteMaximumLikelihood
