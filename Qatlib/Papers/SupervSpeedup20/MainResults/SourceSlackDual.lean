/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SupervSpeedup20.MainResults.Definitions

set_option backward.isDefEq.respectTransparency false

/-!
# Lemmas 17 and 18 — slack norm and dual norm bounds

Fixed source: arXiv:2010.02174 (v1, 5 Oct 2020).

* **Lemma 17** (p. 22, Eq. (D22)–(D25)): for the ground-truth hyperplane `w*`
  of Definition 15 the slack variables `ξ*_i = max{1 − y_i⟨w*,x_i⟩, 0}` satisfy
  `E‖ξ*‖² ≤ 4mΔ`.

  The source proof is reproduced literally: `Pr[ξ*_i = 0] = 1 − Δ` (from
  Definition 15 / Eq. (D16)), `ξ*_i ≤ 2` (from `|y⟨w*,x⟩| ≤ 1`), hence
  `E[ξ*_i²] ≤ 4Δ`, and summing over the `m` iid coordinates gives `4mΔ`.

* **Lemma 18** (p. 22–23, Eq. (D26)–(D27)): the dual solution satisfies
  `E‖α⁰‖² = O(1/Δ² + mΔ)`.
  The algebraic chain (D27), whose two inputs are the KKT relation `α = λξ`
  and the primal optimality of `w⁰`, is proved exactly
  (`lemma18_dual_norm_chain`); the expectation step is then composed with
  Lemma 17 (`source_lemma18`, `source_lemma18_form`).  The remaining gap
  — turning the KKT conditions and the primal program (D17) into the two
  scalar hypotheses — is recorded in the docstring of `source_lemma18` and in
  the PR's claim table.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SupervSpeedup20.MainResults

open Finset DlogWorld
open scoped BigOperators

namespace DlogWorld

variable {W : DlogWorld}

/-- The label enters the signed score only as a sign, so the absolute value of
the signed score is independent of the label. -/
theorem abs_label_mul_eq (b c : Bool) (x : ℝ) :
    |labelOf b * x| = |labelOf c * x| := by
  cases b <;> cases c <;> simp [labelOf]

/-- The bound `|y⟨w*,x⟩| ≤ 1` of Definition 15 / Eq. (D16) holds for either
label: replacing `y` by `−y` does not change the absolute value. -/
theorem abs_signedScore_le_one {s : ZMod W.N} {Δ : ℝ}
    (GT : W.GroundTruthHyperplane s Δ) (b : Bool) (t : ZMod W.N) :
    |W.signedScore GT.w b t| ≤ 1 := by
  have h := GT.hbound t
  have hb : W.signedScore GT.w b t = labelOf b * W.score GT.w t := rfl
  have hc : W.signedScore GT.w (W.conceptClass s (W.logEquiv.symm t)) t =
      labelOf (W.conceptClass s (W.logEquiv.symm t)) * W.score GT.w t := rfl
  rw [hb, hc] at *
  exact (abs_label_mul_eq b (W.conceptClass s (W.logEquiv.symm t))
    (W.score GT.w t)).trans_le h

/-- Pointwise slack bound `(ξ*)² ≤ 4·1{ξ* ≠ 0}` of Eq. (D24)–(D25): either the
margin is at least `1` and the slack vanishes, or `|y⟨w*,x⟩| ≤ 1` bounds the
slack by `2`. -/
theorem slack_sq_le_four_indicator {w : ZMod W.N → ℝ} {b : Bool} {t : ZMod W.N}
    (hb : |W.signedScore w b t| ≤ 1) :
    W.slackOf w b t ^ 2 ≤ 4 * (if ¬ (1 ≤ W.signedScore w b t) then (1 : ℝ) else 0) := by
  unfold DlogWorld.slackOf
  by_cases h : 1 ≤ W.signedScore w b t
  · have h1 : 1 - W.signedScore w b t ≤ 0 := by linarith
    rw [max_eq_right h1, if_neg (not_not.mpr h)]
    norm_num
  · have h1 : 0 ≤ 1 - W.signedScore w b t := by
      have := (abs_le.mp hb).2
      linarith
    rw [max_eq_left h1, if_pos h]
    have hlo := (abs_le.mp hb).1
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 3 - W.signedScore w b t by linarith)
      (show (0 : ℝ) ≤ W.signedScore w b t + 1 by linarith)]

end DlogWorld

/-- **Lemma 17 (source p. 22, Eq. (D22)–(D25)).**  For the ground-truth
hyperplane `w*` of Definition 15 and an iid training law whose coordinates each
satisfy the Definition 15 guarantee `Pr[y⟨w*,x⟩ ≥ 1] = 1 − Δ` (hypothesis
`hbad`, see Eq. (D24)), the expected squared slack norm is at most `4mΔ`. -/
theorem source_lemma17 {W : DlogWorld} (s : ZMod W.N) (m : ℕ) (Δ : ℝ)
    (GT : W.GroundTruthHyperplane s Δ)
    (L : FinLaw (Fin m → ZMod W.N × Bool))
    (hbad : ∀ i : Fin m,
      L.probOf (fun S => ¬ (1 ≤ W.signedScore GT.w (S i).2 (S i).1)) = Δ) :
    L.expect (fun S => ∑ i : Fin m, W.slackOf GT.w (S i).2 (S i).1 ^ 2) ≤
      4 * (m : ℝ) * Δ := by
  have hsingle : ∀ i : Fin m,
      L.expect (fun S => W.slackOf GT.w (S i).2 (S i).1 ^ 2) ≤ 4 * Δ := by
    intro i
    have h1 : L.expect (fun S => W.slackOf GT.w (S i).2 (S i).1 ^ 2) ≤
        L.expect (fun S => 4 * (if ¬ (1 ≤ W.signedScore GT.w (S i).2 (S i).1)
          then (1 : ℝ) else 0)) := by
      refine FinLaw.expect_mono L (fun S => ?_)
      exact DlogWorld.slack_sq_le_four_indicator
        (DlogWorld.abs_signedScore_le_one GT (S i).2 (S i).1)
    have h2 : L.expect (fun S => 4 * (if ¬ (1 ≤ W.signedScore GT.w (S i).2 (S i).1)
          then (1 : ℝ) else 0)) =
        4 * L.probOf (fun S => ¬ (1 ≤ W.signedScore GT.w (S i).2 (S i).1)) := by
      rw [FinLaw.expect_const_mul]
      congr 1
      exact FinLaw.expect_indicator L _
    rw [h2, hbad i] at h1
    linarith
  calc L.expect (fun S => ∑ i : Fin m, W.slackOf GT.w (S i).2 (S i).1 ^ 2)
      = ∑ i : Fin m, L.expect (fun S => W.slackOf GT.w (S i).2 (S i).1 ^ 2) := by
        rw [FinLaw.expect_sum]
    _ ≤ ∑ _i : Fin m, 4 * Δ := Finset.sum_le_sum fun i _ => hsingle i
    _ = 4 * (m : ℝ) * Δ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- **Lemma 18, algebraic chain (source Eq. (D27)).**  With the KKT relation
`α⁰ = λξ⁰` (`hα`) and the primal optimality of the solution `w⁰, ξ⁰`
(`hopt`, twice the primal objective inequality of (D17) at the feasible
ground-truth point), the dual squared norm is bounded by
`λ‖w*‖² + λ²‖ξ*‖²`. -/
theorem lemma18_dual_norm_chain
    {lam w0Sq xi0Sq wStarSq xiStarSq alphaSq : ℝ}
    (hlam : 0 < lam)
    (hα : alphaSq = lam ^ 2 * xi0Sq)
    (hw0 : 0 ≤ w0Sq)
    (hopt : w0Sq + lam * xi0Sq ≤ wStarSq + lam * xiStarSq) :
    alphaSq ≤ lam * wStarSq + lam ^ 2 * xiStarSq := by
  rw [hα]
  have h1 : lam ^ 2 * xi0Sq ≤ lam * (w0Sq + lam * xi0Sq) := by
    nlinarith [mul_nonneg hlam.le hw0]
  have h2 : lam * (w0Sq + lam * xi0Sq) ≤ lam * (wStarSq + lam * xiStarSq) :=
    mul_le_mul_of_nonneg_left hopt hlam.le
  calc lam ^ 2 * xi0Sq ≤ lam * (w0Sq + lam * xi0Sq) := h1
    _ ≤ lam * (wStarSq + lam * xiStarSq) := h2
    _ = lam * wStarSq + lam ^ 2 * xiStarSq := by ring

/-- **Lemma 18 (source p. 22–23, Eq. (D26)–(D27)), expected form.**  Applying
the D27 chain at every training set and taking expectations, the dual norm is
bounded by `λ‖w*‖² + 4λ²mΔ`.

The two hypotheses `hα` and `hopt` are the paper's two named ingredients: the
KKT identity `α⁰_i = λξ⁰_i` (summed over the `m` coordinates) and the primal
optimality of `w⁰` in (D17).  Their derivation from the explicit primal/dual
programs is the part of the source argument not formalised here; the file
`SourceSlackDual` proves everything downstream of them. -/
theorem source_lemma18 {W : DlogWorld} (s : ZMod W.N) (m : ℕ) (Δ lam : ℝ)
    (hlam : 0 < lam)
    (GT : W.GroundTruthHyperplane s Δ)
    (L : FinLaw (Fin m → ZMod W.N × Bool))
    (hbad : ∀ i : Fin m,
      L.probOf (fun S => ¬ (1 ≤ W.signedScore GT.w (S i).2 (S i).1)) = Δ)
    (alphaSq w0Sq xi0Sq : (Fin m → ZMod W.N × Bool) → ℝ)
    (wStarSq : ℝ)
    (hα : ∀ S, alphaSq S = lam ^ 2 * xi0Sq S)
    (hw0 : ∀ S, 0 ≤ w0Sq S)
    (hopt : ∀ S, w0Sq S + lam * xi0Sq S ≤
      wStarSq + lam * (∑ i : Fin m, W.slackOf GT.w (S i).2 (S i).1 ^ 2)) :
    L.expect alphaSq ≤ lam * wStarSq + 4 * lam ^ 2 * (m : ℝ) * Δ := by
  have hpoint : ∀ S, alphaSq S ≤ lam * wStarSq +
      lam ^ 2 * (∑ i : Fin m, W.slackOf GT.w (S i).2 (S i).1 ^ 2) := by
    intro S
    exact lemma18_dual_norm_chain hlam (hα S) (hw0 S) (hopt S)
  have h17 := source_lemma17 s m Δ GT L hbad
  calc L.expect alphaSq
      ≤ L.expect (fun S => lam * wStarSq +
          lam ^ 2 * (∑ i : Fin m, W.slackOf GT.w (S i).2 (S i).1 ^ 2)) :=
        FinLaw.expect_mono L hpoint
    _ = lam * wStarSq + lam ^ 2 *
          L.expect (fun S => ∑ i : Fin m, W.slackOf GT.w (S i).2 (S i).1 ^ 2) := by
        rw [FinLaw.expect_add]
        congr 1
        · exact FinLaw.expect_const L (lam * wStarSq)
        · exact FinLaw.expect_const_mul L (lam ^ 2) _
    _ ≤ lam * wStarSq + lam ^ 2 * (4 * (m : ℝ) * Δ) := by
        have h := mul_le_mul_of_nonneg_left h17 (sq_nonneg lam)
        linarith
    _ = lam * wStarSq + 4 * lam ^ 2 * (m : ℝ) * Δ := by ring

/-- **Lemma 18, source form (D26).**  With the paper's `‖w*‖² ≤ 1/Δ²` (from
`‖w*‖ = O(Δ⁻¹)`, p. 21), the bound reads `E‖α⁰‖² ≤ λ/Δ² + 4λ²mΔ`, i.e.
`O(1/Δ² + mΔ)` for constants `λ`. -/
theorem source_lemma18_form {W : DlogWorld} (s : ZMod W.N) (m : ℕ) (Δ lam : ℝ)
    (hlam : 0 < lam) (hΔ : 0 < Δ)
    (GT : W.GroundTruthHyperplane s Δ)
    (L : FinLaw (Fin m → ZMod W.N × Bool))
    (hbad : ∀ i : Fin m,
      L.probOf (fun S => ¬ (1 ≤ W.signedScore GT.w (S i).2 (S i).1)) = Δ)
    (alphaSq w0Sq xi0Sq : (Fin m → ZMod W.N × Bool) → ℝ)
    (wStarSq : ℝ)
    (hα : ∀ S, alphaSq S = lam ^ 2 * xi0Sq S)
    (hw0 : ∀ S, 0 ≤ w0Sq S)
    (hopt : ∀ S, w0Sq S + lam * xi0Sq S ≤
      wStarSq + lam * (∑ i : Fin m, W.slackOf GT.w (S i).2 (S i).1 ^ 2))
    (hstar : wStarSq ≤ 1 / Δ ^ 2) :
    L.expect alphaSq ≤ lam / Δ ^ 2 + 4 * lam ^ 2 * (m : ℝ) * Δ := by
  have hmain := source_lemma18 s m Δ lam hlam GT L hbad alphaSq w0Sq xi0Sq wStarSq hα hw0 hopt
  have h1 : lam * wStarSq ≤ lam * (1 / Δ ^ 2) := mul_le_mul_of_nonneg_left hstar hlam.le
  have h2 : lam * (1 / Δ ^ 2) = lam / Δ ^ 2 := by ring
  linarith

end Qatlib.Papers.SupervSpeedup20.MainResults
