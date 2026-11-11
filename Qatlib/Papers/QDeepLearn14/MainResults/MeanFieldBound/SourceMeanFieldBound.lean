/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Mean-field bound on the Gibbs distribution (Lemma 1)

Source: "Quantum Deep Learning", arXiv:1412.3489v2, Lemma 1, p.9 (eqs. A3, A4) and
Definition 2 (eq. A1), p.9.

The paper's Lemma 1 states that for the mean-field approximation `Q(v,h)` to the
Gibbs distribution `P(v,h) = e^{-E(v,h)}/Z` of a Boltzmann machine, and for the
mean-field partition function `Z_Q` of Definition 1, every configuration satisfies

  `P(v,h) ≤ e^{-E(v,h)}/Z_Q ≤ κ Q(v,h)`.

The lower inequality is Lemma 1 of the paper: Jensen's inequality shows `Z_Q ≤ Z`
(eq. A3), hence `e^{-E}/Z ≤ e^{-E}/Z_Q` (eq. A4). The upper inequality is the
promise of Definition 2 (eq. A1).

We model the configuration space as an arbitrary finite type `Ω`; `E : Ω → ℝ` is
the energy and `Q : Ω → ℝ` the mean-field probability mass function. `Z_Q` is the
variational quantity `exp(∑_x Q x · log(e^{-E x}/Q x))` of Definition 1. The
quantum state-preparation circuit itself is not modelled — the paper grants it as
a primitive; only the closed-form inequality is proved here.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.QDeepLearn14.MainResults.MeanFieldBound

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

/-- Mean-field variational log-partition function (Definition 1 of
arXiv:1412.3489): `logZQ Q E = ∑_x Q x · log(e^{-E x} / Q x)`. -/
def meanFieldLogPartition (Q E : Ω → ℝ) : ℝ :=
  ∑ x, Q x * Real.log (Real.exp (- E x) / Q x)

/-- Mean-field partition-function approximation `Z_Q = exp(logZQ)` (Definition 1
of arXiv:1412.3489). -/
def meanFieldPartition (Q E : Ω → ℝ) : ℝ :=
  Real.exp (meanFieldLogPartition Q E)

/-- Boltzmann partition function `Z = ∑_x e^{-E x}`. -/
def boltzmannPartition (E : Ω → ℝ) : ℝ :=
  ∑ x, Real.exp (- E x)

/-- The Boltzmann partition function is positive on a nonempty configuration
space. -/
theorem boltzmannPartition_pos (E : Ω → ℝ) : 0 < boltzmannPartition E := by
  unfold boltzmannPartition
  exact Finset.sum_pos (fun x _ => Real.exp_pos _) Finset.univ_nonempty

/-- Lemma 1, lower half (arXiv:1412.3489 eq. A3): the mean-field approximation
`Z_Q` never exceeds the true partition function `Z`. This is Jensen's inequality
applied to the concave logarithm. -/
theorem meanFieldPartition_le_boltzmannPartition
    (E Q : Ω → ℝ) (hQpos : ∀ x, 0 < Q x) (hQsum : ∑ x, Q x = 1) :
    meanFieldPartition Q E ≤ boltzmannPartition E := by
  have hconcave : ConcaveOn ℝ (Set.Ioi 0) Real.log :=
    strictConcaveOn_log_Ioi.concaveOn
  have hnonneg : ∀ x ∈ (Finset.univ : Finset Ω), 0 ≤ Q x := fun x _ => (hQpos x).le
  have hsum' : ∑ x ∈ (Finset.univ : Finset Ω), Q x = 1 := by
    simpa using hQsum
  have hmem : ∀ x ∈ (Finset.univ : Finset Ω),
      (Real.exp (- E x) / Q x) ∈ Set.Ioi 0 := by
    intro x _
    exact Set.mem_Ioi.mpr (div_pos (Real.exp_pos _) (hQpos x))
  have hjensen := hconcave.le_map_sum (s := Set.Ioi 0) (t := Finset.univ)
    (w := Q) (p := fun x => Real.exp (- E x) / Q x) hnonneg hsum' hmem
  -- `hjensen : ∑ x, Q x • log(...) ≤ log (∑ x, Q x • (e^{-E x}/Q x))`
  have hjensen' : meanFieldLogPartition Q E ≤ Real.log (boltzmannPartition E) := by
    have hL : ∑ x, Q x • Real.log (Real.exp (- E x) / Q x)
        = meanFieldLogPartition Q E := by
      unfold meanFieldLogPartition
      simp [smul_eq_mul]
    have hR : (∑ x, Q x • (Real.exp (- E x) / Q x)) = boltzmannPartition E := by
      unfold boltzmannPartition
      apply Finset.sum_congr rfl
      intro x _
      rw [smul_eq_mul]
      field_simp [ne_of_gt (hQpos x)]
    rw [hL, hR] at hjensen
    exact hjensen
  calc meanFieldPartition Q E = Real.exp (meanFieldLogPartition Q E) := rfl
    _ ≤ Real.exp (Real.log (boltzmannPartition E)) := Real.exp_le_exp.mpr hjensen'
    _ = boltzmannPartition E := Real.exp_log (boltzmannPartition_pos E)

/-- **Lemma 1** of arXiv:1412.3489 (p.9): for every configuration `x` we have
`P x ≤ e^{-E x}/Z_Q ≤ κ Q x`, where `P x = e^{-E x}/Z` and `Z_Q` is the
mean-field approximation of `Z` (Definition 1). The lower bound is Jensen
(`Z_Q ≤ Z`, eq. A3/A4); the upper bound is the promise of Definition 2 (eq. A1). -/
theorem lemma1_gibbs_sandwich
    (E Q : Ω → ℝ) (κ ZQ : ℝ)
    (hQpos : ∀ x, 0 < Q x) (hQsum : ∑ x, Q x = 1)
    (hZQpos : 0 < ZQ) (hZQ : ZQ = meanFieldPartition Q E)
    (hBound : ∀ x, Real.exp (- E x) / ZQ ≤ κ * Q x) :
    ∀ x, Real.exp (- E x) / boltzmannPartition E ≤ Real.exp (- E x) / ZQ ∧
         Real.exp (- E x) / ZQ ≤ κ * Q x := by
  have hZQleZ : ZQ ≤ boltzmannPartition E := by
    rw [hZQ]
    exact meanFieldPartition_le_boltzmannPartition E Q hQpos hQsum
  have hZpos : 0 < boltzmannPartition E := boltzmannPartition_pos E
  intro x
  refine ⟨?_, hBound x⟩
  have hax : 0 < Real.exp (- E x) := Real.exp_pos _
  rw [div_le_div_iff₀ hZpos hZQpos]
  exact mul_le_mul_of_nonneg_left hZQleZ (le_of_lt hax)

end Qatlib.Papers.QDeepLearn14.MainResults.MeanFieldBound
