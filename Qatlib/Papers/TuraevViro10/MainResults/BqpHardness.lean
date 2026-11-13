/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TuraevViro10.MainResults.WrtBridge
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Error propagation and promise transfer for the reduction

This module bounds accumulated errors of approximate gate sequences and their effects on squared
matrix elements. It proves the numerical promise separation used in the Turaev–Viro reduction:
given a reduction accurate to strictly less than `1/6` and a decision procedure for the
invariant promise, the acceptance and rejection guarantees transfer to the original inputs. See
[AlagicEtAl2010].

## Main statements

* `gateRun_error_le`: Linear accumulation of uniform gate errors for an isometric ideal
  sequence.
* `eq2_of_gate_approximation`: A squared matrix-element error bound of `1/6`.
* `bqp_hardness_transfer`: Conditional transfer of the invariant promise decision guarantees.

## References

* [Alagic et al., 2010][AlagicEtAl2010]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.TuraevViro10.MainResults.BqpHardness

open Qatlib.Papers.TuraevViro10.MainResults.WrtBridge
open Qatlib.Papers.TuraevViro10.MainResults.WrtBridge.TuraevViroModel

/-- Sequential evaluation of a finite gate family, applying the last gate after the preceding
gates. -/
def gateRun {H : Type*} : ∀ {T : ℕ}, (Fin T → H → H) → H → H
  | 0, _, ψ => ψ
  | T + 1, G, ψ => G (Fin.last T) (gateRun (fun i => G i.castSucc) ψ)

/-- For an isometric ideal gate sequence and uniformly `η`-close approximate gates with `η ≥ 0`,
the output error after `T` gates is at most `T * η`. -/
theorem gateRun_error_le {H : Type*} [SeminormedAddCommGroup H] :
    ∀ {T : ℕ} (U V : Fin T → H → H) (ψ : H) (η : ℝ), 0 ≤ η →
      (∀ i z w, ‖U i z - U i w‖ = ‖z - w‖) →
      (∀ i z, ‖V i z - U i z‖ ≤ η) → ‖gateRun V ψ - gateRun U ψ‖ ≤ (T : ℝ) * η := by
  intro T
  induction T with
  | zero =>
    simp [gateRun]
  | succ T ih =>
    intro U V ψ η hη hU hV
    simp only [gateRun]
    have hsplit : ‖V (Fin.last T) (gateRun (fun i => V i.castSucc) ψ) -
        U (Fin.last T) (gateRun (fun i => U i.castSucc) ψ)‖ ≤
        ‖V (Fin.last T) (gateRun (fun i => V i.castSucc) ψ) -
          U (Fin.last T) (gateRun (fun i => V i.castSucc) ψ)‖ +
        ‖U (Fin.last T) (gateRun (fun i => V i.castSucc) ψ) -
          U (Fin.last T) (gateRun (fun i => U i.castSucc) ψ)‖ := by
      have h : V (Fin.last T) (gateRun (fun i => V i.castSucc) ψ) -
          U (Fin.last T) (gateRun (fun i => U i.castSucc) ψ) =
          (V (Fin.last T) (gateRun (fun i => V i.castSucc) ψ) -
            U (Fin.last T) (gateRun (fun i => V i.castSucc) ψ)) +
          (U (Fin.last T) (gateRun (fun i => V i.castSucc) ψ) -
            U (Fin.last T) (gateRun (fun i => U i.castSucc) ψ)) := by abel
      rw [h]
      exact norm_add_le _ _
    refine hsplit.trans ?_
    have h1 : ‖V (Fin.last T) (gateRun (fun i => V i.castSucc) ψ) -
        U (Fin.last T) (gateRun (fun i => V i.castSucc) ψ)‖ ≤ η :=
      hV (Fin.last T) _
    have h2 : ‖U (Fin.last T) (gateRun (fun i => V i.castSucc) ψ) -
        U (Fin.last T) (gateRun (fun i => U i.castSucc) ψ)‖ ≤ (T : ℝ) * η := by
      rw [hU (Fin.last T) _ _]
      exact ih (fun i => U i.castSucc) (fun i => V i.castSucc) ψ η hη
        (fun i => hU i.castSucc) (fun i => hV i.castSucc)
    have hsum : η + (T : ℝ) * η ≤ ((T + 1 : ℕ) : ℝ) * η := by
      push_cast
      nlinarith
    exact (add_le_add h1 h2).trans hsum

/-- A finite sequence of distance-preserving gates preserves distances between its initial
states. -/
theorem gateRun_dist {H : Type*} [SeminormedAddCommGroup H] :
    ∀ {T : ℕ} (U : Fin T → H → H), (∀ i z w, ‖U i z - U i w‖ = ‖z - w‖) →
      ∀ z w, ‖gateRun U z - gateRun U w‖ = ‖z - w‖ := by
  intro T
  induction T with
  | zero =>
    intro U _ z w
    simp [gateRun]
  | succ T ih =>
    intro U hU z w
    simp only [gateRun]
    rw [hU (Fin.last T) _ _, ih (fun i => U i.castSucc) (fun i => hU i.castSucc) z w]

/-- The change in an inner product with fixed first argument is bounded by the norm of that
argument times the change in the second argument. -/
theorem norm_inner_sub_le {H : Type*} [SeminormedAddCommGroup H]
    [InnerProductSpace ℂ H] (ψ φ φ' : H) :
    ‖inner ℂ ψ φ - inner ℂ ψ φ'‖ ≤ ‖ψ‖ * ‖φ - φ'‖ := by
  rw [← inner_sub_right]
  exact norm_inner_le_norm ψ (φ - φ')

/-- For complex numbers of norm at most one, the difference of squared norms is at most twice
their distance. -/
theorem normSq_error_le {z w : ℂ} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    |‖z‖ ^ 2 - ‖w‖ ^ 2| ≤ 2 * ‖z - w‖ := by
  have hdecomp : ‖z‖ ^ 2 - ‖w‖ ^ 2 = (‖z‖ - ‖w‖) * (‖z‖ + ‖w‖) := by ring
  rw [hdecomp, abs_mul]
  have h1 : |‖z‖ - ‖w‖| ≤ ‖z - w‖ := abs_norm_sub_norm_le z w
  have h2 : |‖z‖ + ‖w‖| ≤ 2 := by
    rw [abs_of_nonneg (by positivity)]
    linarith
  calc |‖z‖ - ‖w‖| * |‖z‖ + ‖w‖| ≤ ‖z - w‖ * 2 :=
        mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
    _ = 2 * ‖z - w‖ := by ring

/-- For a unit state and matrix elements of norm at most one, an output-vector error at most `η`
gives squared matrix-element error at most `2 * η`. -/
theorem matrixElement_normSq_error {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (ψ : H) (hψ : ‖ψ‖ = 1) (A B : H → H) {η : ℝ}
    (hclose : ‖A ψ - B ψ‖ ≤ η) (hA : ‖inner ℂ ψ (A ψ)‖ ≤ 1)
    (hB : ‖inner ℂ ψ (B ψ)‖ ≤ 1) :
    |‖inner ℂ ψ (A ψ)‖ ^ 2 - ‖inner ℂ ψ (B ψ)‖ ^ 2| ≤ 2 * η := by
  have hdiff : ‖inner ℂ ψ (A ψ) - inner ℂ ψ (B ψ)‖ ≤ η := by
    refine (norm_inner_sub_le ψ (A ψ) (B ψ)).trans ?_
    rw [hψ, one_mul]
    exact hclose
  exact (normSq_error_le hA hB).trans (mul_le_mul_of_nonneg_left hdiff (by norm_num))

/-- For complex numbers in the unit disk, the squared-norm error is at most twice the sum of the
absolute real and imaginary component errors. -/
theorem normSq_error_of_quadrature_error {z w : ℂ} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    |‖z‖ ^ 2 - ‖w‖ ^ 2| ≤ 2 * (|z.re - w.re| + |z.im - w.im|) := by
  refine (normSq_error_le hz hw).trans ?_
  have hnorm : ‖z - w‖ ≤ |z.re - w.re| + |z.im - w.im| := by
    simpa using Complex.norm_le_abs_re_add_abs_im (z - w)
  linarith

/-- For a unit initial state, an isometric ideal gate sequence, uniformly `η`-close
approximants, and bounded final matrix elements, `T * η ≤ 1/12` implies squared
matrix-element error at most `1/6`. See [AlagicEtAl2010]. -/
theorem eq2_of_gate_approximation {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {T : ℕ} (U V : Fin T → H → H) (ψ : H) (η : ℝ) (hη : 0 ≤ η)
    (hψ : ‖ψ‖ = 1) (hU : ∀ i z w, ‖U i z - U i w‖ = ‖z - w‖)
    (hV : ∀ i z, ‖V i z - U i z‖ ≤ η)
    (hUle : ‖inner ℂ ψ (gateRun U ψ)‖ ≤ 1)
    (hVle : ‖inner ℂ ψ (gateRun V ψ)‖ ≤ 1)
    (hprec : (T : ℝ) * η ≤ 1 / 12) :
    |‖inner ℂ ψ (gateRun U ψ)‖ ^ 2 - ‖inner ℂ ψ (gateRun V ψ)‖ ^ 2| ≤ 1 / 6 := by
  have hstate : ‖gateRun V ψ - gateRun U ψ‖ ≤ (T : ℝ) * η :=
    gateRun_error_le U V ψ η hη hU hV
  have hbound :=
    matrixElement_normSq_error ψ hψ (gateRun U) (gateRun V)
      (by simpa [norm_sub_rev] using hstate) hUle hVle
  linarith

/-- If `p ≥ 5/6` and `|p - ntv| < 1/6`, then `ntv > 2/3`. -/
theorem gap_upper {p ntv : ℝ} (h : |p - ntv| < 1 / 6) (hyes : 5 / 6 ≤ p) :
    2 / 3 < ntv := by
  rw [abs_lt] at h
  linarith

/-- If `p ≤ 1/6` and `|p - ntv| < 1/6`, then `ntv < 1/3`. -/
theorem gap_lower {p ntv : ℝ} (h : |p - ntv| < 1 / 6) (hno : p ≤ 1 / 6) :
    ntv < 1 / 3 := by
  rw [abs_lt] at h
  linarith

/-- No real number lies simultaneously above `2/3` and below `1/3`. -/
theorem promise_sets_disjoint (v : ℝ) : ¬ ((2 / 3 : ℝ) < v ∧ v < 1 / 3) := by
  intro h
  linarith [h.1, h.2]

/-- Given a reduction with normalized-invariant error strictly below `1/6`, a procedure deciding
the invariant promises above `2/3` and below `1/3` accepts inputs with acceptance
probability at least `5/6` and rejects those with probability at most `1/6`. See
[AlagicEtAl2010]. -/
theorem bqp_hardness_transfer {P ι C : Type*} [Fintype P] (M : TuraevViroModel P ι)
    (acceptProb : C → ℝ) (red : C → ℕ × ι)
    (hfaithful : ∀ c, |acceptProb c -
      M.normalizedTvInvariant (red c).1 (red c).2| < 1 / 6)
    (decide : ℕ → ι → Bool)
    (hdecide : ∀ g x, ((2 : ℝ) / 3 < M.normalizedTvInvariant g x → decide g x = true) ∧
      (M.normalizedTvInvariant g x < 1 / 3 → decide g x = false)) :
    ∀ c, (5 / 6 ≤ acceptProb c → decide (red c).1 (red c).2 = true) ∧
      (acceptProb c ≤ 1 / 6 → decide (red c).1 (red c).2 = false) := by
  intro c
  constructor
  · intro hyes
    exact (hdecide (red c).1 (red c).2).1 (gap_upper (hfaithful c) hyes)
  · intro hno
    exact (hdecide (red c).1 (red c).2).2 (gap_lower (hfaithful c) hno)

/-- A reduction accurate to strictly less than `1/6` sends acceptance probabilities at least
`5/6` above the normalized-invariant threshold `2/3`, and those at most `1/6` below `1/3`.
See [AlagicEtAl2010]. -/
theorem converse_promise_separation {P ι C : Type*} [Fintype P]
    (M : TuraevViroModel P ι) (acceptProb : C → ℝ) (red : C → ℕ × ι)
    (hfaithful : ∀ c, |acceptProb c -
      M.normalizedTvInvariant (red c).1 (red c).2| < 1 / 6) :
    (∀ c, 5 / 6 ≤ acceptProb c → 2 / 3 < M.normalizedTvInvariant (red c).1 (red c).2) ∧
      (∀ c, acceptProb c ≤ 1 / 6 → M.normalizedTvInvariant (red c).1 (red c).2 < 1 / 3) :=
  ⟨fun c h => gap_upper (hfaithful c) h, fun c h => gap_lower (hfaithful c) h⟩

end Qatlib.Papers.TuraevViro10.MainResults.BqpHardness
