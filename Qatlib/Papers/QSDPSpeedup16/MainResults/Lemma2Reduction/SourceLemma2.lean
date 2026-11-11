/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QSDPSpeedup16.MainResults.SdpModel
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 2 (source restatement: Lemma 18, Appendix A)

Brandão–Svore, *Quantum Speed-ups for Semidefinite Programming*, fixed
arXiv:1609.05537v5 (PDF SHA-256
746714c3d97424df74d7f5956107687f73c6501403e35af757421328dfb030b7).
Lemma 2 is printed on p. 5; its proof is Appendix A, Lemma 18, pp. 21–22,
Eqs. (98)–(108).

The paper's Lemma 2 reduces an arbitrary SDP to one with all `bᵢ ≥ 1`:

* coefficients are lifted to `b' = snoc b (R+1)` in dimension `m+1` with size
  parameter `2R+1` (Eq. (98) and its objective line);
* a `δ`-optimal solution `y` of the lifted SDP truncates to a `δ`-optimal
  solution of the original SDP (Eq. (99)–(108));
* the associated SDP with cost rescaled by `1/r` must be solved to additive
  error `δ/r`, and scaling the sampled solution by `r` restores additive
  error `δ` (last paragraph, p. 22).

What is **encoded** here: the coefficient lifting, the lifted-objective
truncation/optimality transfer with the exact Appendix-A witness of Eq. (102),
the witness's nonnegativity and mass conditions, and the two sampling
transformations (coordinate truncation and `r`-scaling) at the level of a
finite probability law.

What is **not** encoded: the `n → n+1` block-matrix lifting
`[[Aᵢ,0],[0,1]]`, `[[0,0],[0,1]]`, `[[C,0],[0,r]]` of Eq. (98), the resulting
positive-semidefinite feasibility transfer, and the DIMACS sampling/measurement
channel used to obtain samples in the first place.  Those are algorithmic
obligations of the source proof; the scalar reduction they feed is proved here.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QSDPSpeedup16.MainResults.Lemma2Reduction

open Qatlib.Papers.QSDPSpeedup16.MainResults.SdpModel

/-- Lemma 18, Eqs. (102)–(108), optimality-transfer step.  If `y` is a `δ`-optimal
solution of the lifted SDP whose witness of Eq. (102) is built from an optimal
original solution `z` (objective `opt`, mass at most `r`), and the lifted sample
has `y_last ≥ r`, then the truncation of `y` is `δ`-optimal for the original SDP:
`∑ bᵢ yᵢ ≤ opt + δ`.

The hypothesis `hdelta` is the source's `δ`-optimality of `y` against the lifted
optimum, using that the witness Eq. (102) is feasible for the lifted SDP (its
feasibility is exactly the block-matrix lifting not encoded here). -/
theorem lemma2_truncation {m : ℕ} (b : Fin m → ℝ) (R δ opt : ℝ) (z : Fin m → ℝ)
    (y : Fin (m + 1) → ℝ)
    (hz : sdpObjective b z = opt)
    (hdelta : liftedObjective b R y ≤ liftedObjective b R (liftWitness z y) + δ) :
    sdpObjective b (truncate y) ≤ opt + δ := by
  have hsplit := liftedObjective_eq_truncate b R y
  have hwit := liftedObjective_liftWitness b R z y
  rw [hz] at hwit
  rw [hsplit, hwit] at hdelta
  linarith

/-- Lemma 2, coefficient lifting plus truncation.  A `δ`-optimal solution of the lifted
SDP (98) truncates to a `δ`-optimal solution of the original SDP, and the lifted
objective coefficients are `snoc b (R+1)` with every entry at least one. -/
theorem sourceLemma2 {m : ℕ} (b : Fin m → ℝ) (R r δ opt : ℝ) (z : Fin m → ℝ)
    (y : Fin (m + 1) → ℝ) (hb : ∀ i, 1 ≤ b i) (hR : 0 ≤ R)
    (hz0 : ∀ i, 0 ≤ z i) (hz : sdpObjective b z = opt) (hy : ∀ i, 0 ≤ y i)
    (hy_last : r ≤ y (Fin.last m)) (hz_sum : ∑ i : Fin m, z i ≤ r)
    (hdelta : liftedObjective b R y ≤ liftedObjective b R (liftWitness z y) + δ) :
    ∃ liftedB : Fin (m + 1) → ℝ,
      (∀ i, 1 ≤ liftedB i) ∧ liftedB (Fin.last m) = R + 1 ∧
      (∀ i : Fin m, liftedB i.castSucc = b i) ∧
      (∀ i, 0 ≤ liftWitness z y i) ∧
      r ≤ ∑ i : Fin (m + 1), liftWitness z y i ∧
      sdpObjective b (truncate y) ≤ opt + δ := by
  obtain ⟨liftedB, h1, h2, h3⟩ := exists_liftedCoefficients b R hb hR
  exact ⟨liftedB, h1, h2, h3,
    liftWitness_nonneg z y hz0 hy hy_last hz_sum,
    liftWitness_sum_ge z y hy hy_last,
    lemma2_truncation b R δ opt z y hz hdelta⟩

/-- Lemma 2, sampling by coordinate truncation: a finite probability law whose every atom
is a `δ`-optimal solution of the lifted SDP pushes forward along `truncate` to a law whose
every atom is a `δ`-optimal solution of the original SDP.  This is the "given the ability
to sample … one can sample" step of Lemma 2 at the scalar objective level. -/
theorem lemma2_sampleTruncation {m Ω : ℕ} (b : Fin m → ℝ) (R r δ opt : ℝ)
    (z : Fin m → ℝ) (law : Fin Ω → Fin (m + 1) → ℝ)
    (hz0 : ∀ i, 0 ≤ z i) (hz : sdpObjective b z = opt)
    (hy : ∀ ω i, 0 ≤ law ω i) (hy_last : ∀ ω, r ≤ law ω (Fin.last m))
    (hz_sum : ∑ i : Fin m, z i ≤ r)
    (hdelta : ∀ ω, liftedObjective b R (law ω) ≤
      liftedObjective b R (liftWitness z (law ω)) + δ) :
    ∃ law' : Fin Ω → Fin m → ℝ,
      (∀ ω, (∀ i, 0 ≤ liftWitness z (law ω) i) ∧
        r ≤ ∑ i : Fin (m + 1), liftWitness z (law ω) i) ∧
      (∀ ω, sdpObjective b (law' ω) ≤ opt + δ) ∧
      ∀ ω i, law' ω i = law ω i.castSucc := by
  refine ⟨fun ω => truncate (law ω), ?_, ?_, ?_⟩
  · intro ω
    exact ⟨liftWitness_nonneg z (law ω) hz0 (hy ω) (hy_last ω) hz_sum,
      liftWitness_sum_ge z (law ω) (hy ω) (hy_last ω)⟩
  · intro ω
    exact lemma2_truncation b R δ opt z (law ω) hz (hdelta ω)
  · intro ω i
    rfl

/-- Lemma 2 / Appendix A, final paragraph (p. 22): solving the associated SDP whose cost
is rescaled by `1/r` to additive error `δ/r` gives additive error `δ` after scaling the
solution by `r`.  In objective values: `v ≤ opt/r + δ/r` implies `r * v ≤ opt + δ`. -/
theorem lemma2_rescale_tolerance (r δ opt v : ℝ) (hr : 0 < r)
    (hv : v ≤ opt / r + δ / r) :
    r * v ≤ opt + δ := by
  have h := mul_le_mul_of_nonneg_left hv hr.le
  have he : r * (opt / r + δ / r) = opt + δ := by
    field_simp
  linarith

/-- Lemma 2, sampling by `r`-scaling: a finite law over `(δ/r)`-optimal solutions of the
rescaled SDP pushes forward along `y ↦ r * y` to a law over `δ`-optimal solutions of the
original SDP. -/
theorem lemma2_sampleScaling {m Ω : ℕ} (b : Fin m → ℝ) (r δ opt : ℝ)
    (law : Fin Ω → Fin m → ℝ) (hr : 0 < r)
    (h : ∀ ω, sdpObjective b (law ω) ≤ opt / r + δ / r) :
    ∃ law' : Fin Ω → Fin m → ℝ,
      (∀ ω, sdpObjective b (law' ω) ≤ opt + δ) ∧
      ∀ ω i, law' ω i = r * law ω i := by
  refine ⟨fun ω i => r * law ω i, ?_, ?_⟩
  · intro ω
    have hscale : sdpObjective b (fun i => r * law ω i) =
        r * sdpObjective b (law ω) := by
      unfold sdpObjective
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hscale]
    exact lemma2_rescale_tolerance r δ opt (sdpObjective b (law ω)) hr (h ω)
  · intro ω i
    rfl

/-- Lemma 2, §2.2 relative-tolerance rescale (printed p. 5): if a solution vector
`bsol` satisfies the normalized objective bound `∑ bsolᵢ (bᵢ/α) ≤ 1 + δ` at guess
`α > 0`, then its original objective obeys `∑ bsolᵢ bᵢ ≤ (1+δ)α`. -/
theorem lemma2_coefficient_rescale {m : ℕ} (b bsol : Fin m → ℝ) (α δ : ℝ)
    (hα : 0 < α) (h : ∑ i, bsol i * (b i / α) ≤ 1 + δ) :
    ∑ i, bsol i * b i ≤ (1 + δ) * α := by
  have hrew : (∑ i, bsol i * (b i / α)) * α = ∑ i, bsol i * b i := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    field_simp
  have hmul := mul_le_mul_of_nonneg_right h hα.le
  rw [hrew] at hmul
  exact hmul

end Qatlib.Papers.QSDPSpeedup16.MainResults.Lemma2Reduction
