/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# PathPhase — Proposition 1: the state prepared by one execution of the `G_φ` course

Grice--Meyer, *A quantum algorithm for Viterbi decoding of classical convolutional
codes*, fixed arXiv:1405.7479v2 (PDF dated 2015-06-20), Section 2.1 (definitions of
`P(i,j|y)`, `P(y|i,j)` and `P_{i,j}(y) = P(i,j|y) P(y|i,j)`), Section 2.2, Eq. (5)-(6)
and Proposition 1 with the displayed induction proof on printed pp. 5-6, plus Eq. (1)
on p. 3.

The source executes the course (6) of `N` blocks `V_{y_1}, …, V_{y_N}`, where one block
acts as `|i⟩|0⟩ ↦ Σ_j e^{i f(P_{i,j}(y))} |i⟩|j⟩` (Section 2.1, gateway to Eq. (5)),
and it claims:

> **Proposition 1.** Fixing a set of emissions `{y_i}`, the state of the system after
> one execution of (6) is `|ψ_f⟩ = Σ_{π ∈ F^N} e^{i ∏_j f(π_j)} |π⟩`, where `∏_j π_j`
> is the probability of the path `π ∈ Q^N` being taken.

The source's proof is the induction "assume the assertion for `N-1` steps, feed the last
qubit of `|ψ_{N-1}⟩` into `V_{y_N}`, and collect terms", whose displayed intermediate
state carries the phase `e^{i Σ_{j=1}^{N-1} f(π_j)}` — that is, the *exponent* accumulates
additively along the path while the *phase factors* multiply.

Formalized here, with `α` the hidden-state alphabet `Q`:

* `pathProb` — the path probability `∏_j π_j` of the source, i.e. the product of the
  per-step transition probabilities along the path;
* `ampAfter` — the amplitude assigned to a path by executing the blocks of (6) one at a
  time, so that the `(N+1)`-step path inherits the amplitude of its `N`-step prefix
  times the last block's marking phase; this is the source's induction step, and
  `ampAfter_one` is the source's base case (a single `V_y` block);
* `prop1_ampAfter_eq_prod` — Proposition 1 in path form: the amplitude of `π` is the
  product over steps of the marking phases `e^{i f(π_s)}`, i.e. `e^{i ∏_j f(π_j)}` read as
  a product of phase factors;
* `prop1_amp_eq_exp_log` — with the source's strictly increasing marking function
  `f = log`, the phase exponent is `log` of the path probability `∏_j π_j`, so the
  amplitude is `e^{i log ∏_j π_j}`: both occurrences of the source's `∏_j` are unified.

Not covered here: the tensor-factor-level Hilbert-space statement `|π⟩` itself (the
frozen register model is the natural interface, and the source's statement is about the
amplitude of each path), and the `G_{F^N}` amplification step, which is Section 2.2's
separate amplitude-amplification discussion.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.ViterbiDecode14.MainResults

variable {α : Type*}

/-- The marking phase `e^{i f(P_{i,j}(y))}` that one `V_y` block attaches to the
transition `i → j` at step `s`, evaluated on the path `π : Fin (N+1) → α` (Section 2.1
and Eq. (5): the block is block diagonal in the control slot with these entries). -/
def stepPhase {N : ℕ} (w : Fin N → α → α → ℝ) (f : ℝ → ℝ) (s : Fin N)
    (π : Fin (N+1) → α) : ℂ :=
  Complex.exp (Complex.I * ((f (w s (π (Fin.castSucc s)) (π (Fin.succ s)))) : ℂ))

/-- The path probability `∏_j π_j` of the source: the product of the per-step
transition probabilities `P_{i,j}(y_s)` along the admissible path `π`. -/
def pathProb {N : ℕ} (w : Fin N → α → α → ℝ) (π : Fin (N+1) → α) : ℝ :=
  ∏ s : Fin N, w s (π (Fin.castSucc s)) (π (Fin.succ s))

/-- The amplitude attached to the path `π` after `N` blocks of the course (6), built
step by step exactly as the source's induction builds the state: the amplitude of an
`(N+1)`-step path is the amplitude of its `N`-step prefix times the marking phase of
the last block. -/
def ampAfter : (N : ℕ) → (Fin N → α → α → ℝ) → (ℝ → ℝ) → ((Fin (N+1) → α) → ℂ)
  | 0, _, _ => fun _ => 1
  | N + 1, w, f => fun π =>
      ampAfter N (fun s => w (Fin.castSucc s)) f (fun t => π (Fin.castSucc t)) *
        stepPhase w f (Fin.last N) π

/-- The source's base case: one execution of a single block `V_{y_1}` attaches to the
transition `i → j` precisely the phase `e^{i f(P_{i,j}(y_1))}`. -/
theorem ampAfter_one (w : Fin 1 → α → α → ℝ) (f : ℝ → ℝ) (π : Fin 2 → α) :
    ampAfter 1 w f π = stepPhase w f 0 π := by
  simp [ampAfter]

/-- Proposition 1 in path form: after `N` blocks of the course (6), the amplitude of the
path `π` is `∏_j e^{i f(π_j)}`, the product of the per-step marking phases, i.e. the
source's `e^{i ∏_j f(π_j)}` with the phase factors multiplying and the exponents adding. -/
theorem prop1_ampAfter_eq_prod :
    ∀ (N : ℕ) (w : Fin N → α → α → ℝ) (f : ℝ → ℝ) (π : Fin (N+1) → α),
      ampAfter N w f π = ∏ s : Fin N, stepPhase w f s π
  | 0, _, _, _ => by simp [ampAfter]
  | N + 1, w, f, π => by
    show ampAfter N (fun s => w (Fin.castSucc s)) f (fun t => π (Fin.castSucc t)) *
        stepPhase w f (Fin.last N) π = ∏ s, stepPhase w f s π
    rw [prop1_ampAfter_eq_prod N (fun s => w (Fin.castSucc s)) f
      (fun t => π (Fin.castSucc t)), Fin.prod_univ_castSucc]
    congr 1

/-- Proposition 1 with the source's marking function `f = log`: the state prepared by
one execution of (6) assigns to each path the amplitude `e^{i log ∏_j π_j}`, whose
exponent is the logarithm of the path probability `∏_j π_j`. -/
theorem prop1_amp_eq_exp_log (N : ℕ) (w : Fin N → α → α → ℝ) (π : Fin (N+1) → α)
    (hw : ∀ s : Fin N, 0 < w s (π (Fin.castSucc s)) (π (Fin.succ s))) :
    ampAfter N w Real.log π =
      Complex.exp (Complex.I * ((Real.log (pathProb w π)) : ℂ)) := by
  rw [prop1_ampAfter_eq_prod, pathProb]
  simp only [stepPhase]
  rw [← Complex.exp_sum, Real.log_prod (fun s _ => (hw s).ne')]
  congr 1
  rw [Complex.ofReal_sum, Finset.mul_sum]

/-- The source's admissible-path condition `π ∈ F^N`: every one-step transition weight used by
the path is nonzero. -/
def admissiblePath {N : ℕ} (w : Fin N → α → α → ℝ) (π : Fin (N+1) → α) : Prop :=
  ∀ s : Fin N, w s (π (Fin.castSucc s)) (π (Fin.succ s)) ≠ 0

/-- The finite set of admissible paths, the source's `F^N`. -/
noncomputable def admissiblePaths {N : ℕ} (w : Fin N → α → α → ℝ) [Fintype α] :
    Finset (Fin (N+1) → α) :=
  @Finset.filter _ (admissiblePath w) (Classical.decPred _) Finset.univ

/-- Proposition 1 as a state in the shared `QState` representation: the state prepared by one
execution of the course (6) is the sum of the corrected phase amplitudes over the source's
admissible paths. Paths outside `F^N` receive amplitude zero. -/
def pathState {N : ℕ} (w : Fin N → α → α → ℝ) (f : ℝ → ℝ) [Fintype α] :
    Qatlib.Foundations.PureStateMath.QState (Fin (N+1) → α) :=
  fun π => @ite _ (admissiblePath w π) (Classical.propDecidable _) (ampAfter N w f π) 0

/-- Proposition 1 in the shared ket expansion: the path state is exactly
`∑_{π ∈ F^N} e^{i Σ_j f(π_j)} |π⟩`, with the source's printed product-of-exponents formula
read as the product of phase factors proved in `prop1_ampAfter_eq_prod`. -/
theorem pathState_eq_sum_ket {N : ℕ} (w : Fin N → α → α → ℝ) (f : ℝ → ℝ)
    [Fintype α] [DecidableEq α] :
    pathState w f =
      ∑ π ∈ admissiblePaths w, ampAfter N w f π •
        Qatlib.Foundations.PureStateMath.Ket (π : Fin (N+1) → α) := by
  funext x
  simp only [pathState, admissiblePaths, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Qatlib.Foundations.PureStateMath.ket_apply]
  by_cases hx : admissiblePath w x
  · simp [hx]
  · simp [hx]

/-- Each marking phase has modulus one, independently of the transition probability and of the
marking function `f`. -/
theorem stepPhase_norm {N : ℕ} (w : Fin N → α → α → ℝ) (f : ℝ → ℝ) (s : Fin N)
    (π : Fin (N+1) → α) : ‖stepPhase w f s π‖ = 1 := by
  rw [stepPhase, Complex.norm_exp]
  simp

/-- The corrected Proposition-1 amplitude of every admissible path has modulus one; probabilities
are carried by its phase, not by its magnitude. -/
theorem ampAfter_norm {N : ℕ} (w : Fin N → α → α → ℝ) (f : ℝ → ℝ)
    (π : Fin (N+1) → α) : ‖ampAfter N w f π‖ = 1 := by
  rw [prop1_ampAfter_eq_prod, Complex.norm_prod]
  simp [stepPhase_norm]

/-- The unnormalized path state of Proposition 1 has total squared norm equal to the number of
admissible paths: the source's equal-modulus phase state must still be normalized before the
Born rule is applied. -/
theorem pathState_normSq_eq_card {N : ℕ} (w : Fin N → α → α → ℝ) (f : ℝ → ℝ)
    [Fintype α] :
    ∑ π, ‖pathState w f π‖ ^ 2 = (admissiblePaths w).card := by
  have hterms : ∀ π : Fin (N+1) → α,
      ‖pathState w f π‖ ^ 2 =
        @ite _ (admissiblePath w π) (Classical.propDecidable _) (1 : ℝ) 0 := by
    intro π
    by_cases hπ : admissiblePath w π
    · simp [pathState, hπ, ampAfter_norm]
    · simp [pathState, hπ]
  calc ∑ π, ‖pathState w f π‖ ^ 2
      = ∑ π : Fin (N+1) → α,
          @ite _ (admissiblePath w π) (Classical.propDecidable _) (1 : ℝ) 0 :=
        Finset.sum_congr rfl fun π _ => hterms π
    _ = ∑ π ∈ admissiblePaths w,
          @ite _ (admissiblePath w π) (Classical.propDecidable _) (1 : ℝ) 0 := by
        exact (Finset.sum_subset (Finset.subset_univ _) fun x _ hx => by
          simp only [admissiblePaths, Finset.mem_filter, Finset.mem_univ, true_and] at hx
          simp [hx]).symm
    _ = ∑ π ∈ admissiblePaths w, (1 : ℝ) := by
        refine Finset.sum_congr rfl fun π hπ => ?_
        simp only [admissiblePaths, Finset.mem_filter, Finset.mem_univ, true_and] at hπ
        simp [hπ]
    _ = (admissiblePaths w).card := by
        rw [Finset.sum_const, Nat.smul_one_eq_cast]

end Qatlib.Papers.ViterbiDecode14.MainResults
