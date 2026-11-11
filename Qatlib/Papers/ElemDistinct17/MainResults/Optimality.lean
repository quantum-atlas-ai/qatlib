/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ElemDistinct17.MainResults.ReducedSubspace

set_option backward.isDefEq.respectTransparency false

/-!
# Element Distinctness Revisited — exact optimality steps of Theorem 3.1

Source: arXiv:1711.11336v3 (13 Jun 2018), proof of Theorem 3.1, pp. 9–10.

The proof of Theorem 3.1 selects the two parameters by two *exact* one-variable
optimisations, before taking any asymptotics:

* Eq. (26), p. 9: `t₂` is chosen to minimise the dominant term
  `⟨k,0|ψ_k⟩² / (1 - cos(t₂ φ_k))`, i.e. to maximise `1 - cos(t₂ φ_k)`.
  Since `1 - cos x ≤ 2` with equality at `x = π`, the choice `t₂ = π/φ_k`
  is a global maximiser.
* Eq. (25), p. 10: the success probability at the optimal `t₂` is
  `p(t) = (1/(4b)) sin²(λt)`; its maximum is `1/(4b)`, attained at
  `t = π/(2λ)`, and this is the *first* such time on `t ≥ 0`.
* `p_succ = 1/(4b)`, Eq. (25).

These exact statements are proved here; the remaining asymptotic expansions
(26), (27), (28) are in `Theorem31.lean`.
-/

set_option autoImplicit false

namespace Qatlib.Papers.ElemDistinct17.MainResults

/-- `1 - cos x ≤ 2`, with equality at `x = π`.  This is the inequality behind
the choice `t₂ = π/φ_k`, Eq. (26), p. 9. -/
theorem one_sub_cos_le_two (x : ℝ) : 1 - Real.cos x ≤ 2 := by
  have h := Real.neg_one_le_cos x
  linarith

/-- `sin² x ≤ 1`. -/
theorem sin_sq_le_one (x : ℝ) : Real.sin x ^ 2 ≤ 1 := by
  have h1 : Real.sin x ≤ 1 := Real.sin_le_one x
  have h2 : -1 ≤ Real.sin x := Real.neg_one_le_sin x
  have hprod : 0 ≤ (1 - Real.sin x) * (1 + Real.sin x) := by
    apply mul_nonneg <;> linarith
  nlinarith [hprod]

/-- **Eq. (26), exact step (p. 9).**  For every `t`, the phase factor
`1 - cos(t φ_k)` is at most its value at `t₂ = π/φ_k`, namely `2`.  Thus the
paper's choice `t₂ = π/φ_k` maximises `1 - cos(t₂ φ_k)`, equivalently minimises
the dominant denominator `1 - cos(t₂ φ_k)`. -/
theorem one_sub_cos_le_at_t2Opt (k N r : ℕ) (hphi : phi N r k ≠ 0) (t : ℝ) :
    1 - Real.cos (t * phi N r k) ≤
      1 - Real.cos (t2Opt k N r * phi N r k) := by
  rw [cos_t2Opt_phase k N r hphi]
  have h := Real.neg_one_le_cos (t * phi N r k)
  linarith

/-- At `t₂ = π/φ_k` the dominant denominator is exactly `2`. -/
theorem denominator_at_t2Opt (k N r : ℕ) (hphi : phi N r k ≠ 0) :
    1 - Real.cos (t2Opt k N r * phi N r k) = 2 := by
  rw [cos_t2Opt_phase k N r hphi]
  norm_num

/-- `λ · t₁ = π/2` with `t₁ = π/(2λ)`, when `λ ≠ 0`. -/
theorem t1Opt_mul_lambda (k N r : ℕ)
    (hlam : lambdaParam k N r (t2Opt k N r) ≠ 0) :
    lambdaParam k N r (t2Opt k N r) * t1Opt k N r = Real.pi / 2 := by
  unfold t1Opt
  field_simp

/-- At `t₁ = π/(2λ)` the sine attains one: `sin(λ t₁) = 1`. -/
theorem sin_at_t1Opt (k N r : ℕ) (hlam : lambdaParam k N r (t2Opt k N r) ≠ 0) :
    Real.sin (lambdaParam k N r (t2Opt k N r) * t1Opt k N r) = 1 := by
  rw [t1Opt_mul_lambda k N r hlam, Real.sin_pi_div_two]

/-- **Eq. (28), exact step (p. 10).**  `t₁ = π/(2λ)` is the *first* time
`t ≥ 0` at which `sin(λ t)` reaches its maximum `1`. -/
theorem sin_lt_one_before_t1Opt (k N r : ℕ)
    (hlam : 0 < lambdaParam k N r (t2Opt k N r))
    {t : ℝ} (ht0 : 0 ≤ t) (ht : t < t1Opt k N r) :
    Real.sin (lambdaParam k N r (t2Opt k N r) * t) < 1 := by
  set lam := lambdaParam k N r (t2Opt k N r) with hlamdef
  have hne : lam ≠ 0 := ne_of_gt hlam
  have hphase : lam * t1Opt k N r = Real.pi / 2 := t1Opt_mul_lambda k N r hne
  have hlt : lam * t < Real.pi / 2 := by
    rw [← hphase]
    exact mul_lt_mul_of_pos_left ht hlam
  have hge : -(Real.pi / 2) ≤ lam * t := by
    have hnonneg : 0 ≤ lam * t := mul_nonneg hlam.le ht0
    linarith [Real.pi_pos]
  have hsin := Real.strictMonoOn_sin ⟨hge, le_of_lt hlt⟩
    ⟨by linarith [Real.pi_pos], le_refl (Real.pi / 2)⟩ hlt
  simpa [Real.sin_pi_div_two] using hsin

/-- The success probability as a function of the main-block repetition count,
Eq. (25), p. 10: `p(t) = (1/(4b)) sin²(λt)`, evaluated at the optimal `t₂`. -/
noncomputable def phaseProbability (k N r : ℕ) (t : ℝ) : ℝ :=
  1 / (4 * bParam k N r (t2Opt k N r)) *
    Real.sin (lambdaParam k N r (t2Opt k N r) * t) ^ 2

/-- **Eq. (25), maximum step (p. 10).**  For `b > 0`, the probability
`(1/(4b)) sin²(λt)` never exceeds `p_succ = 1/(4b)`. -/
theorem phaseProbability_le_pSucc (k N r : ℕ)
    (hb : 0 < bParam k N r (t2Opt k N r)) (t : ℝ) :
    phaseProbability k N r t ≤ pSucc k N r := by
  unfold phaseProbability pSucc
  have hcoef : 0 ≤ 1 / (4 * bParam k N r (t2Opt k N r)) := by positivity
  have hs := sin_sq_le_one (lambdaParam k N r (t2Opt k N r) * t)
  calc
    1 / (4 * bParam k N r (t2Opt k N r)) *
        Real.sin (lambdaParam k N r (t2Opt k N r) * t) ^ 2
        ≤ 1 / (4 * bParam k N r (t2Opt k N r)) * 1 :=
          mul_le_mul_of_nonneg_left hs hcoef
    _ = 1 / (4 * bParam k N r (t2Opt k N r)) := by ring

/-- At the first maximiser `t₁ = π/(2λ)` the probability equals `1/(4b)`. -/
theorem phaseProbability_t1Opt (k N r : ℕ)
    (hlam : lambdaParam k N r (t2Opt k N r) ≠ 0) :
    phaseProbability k N r (t1Opt k N r) = pSucc k N r := by
  unfold phaseProbability pSucc
  rw [sin_at_t1Opt k N r hlam]
  ring

end Qatlib.Papers.ElemDistinct17.MainResults
