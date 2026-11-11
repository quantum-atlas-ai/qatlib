/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

/-!
# Exact split-mass transfer on a block

Formal core of the amplitude-transfer step of *Harnessing problem structure for
end-to-end quantum speed-ups* (arXiv:2609.40105v1), Methods “Amplitude transfer
between compatible blocks” (Eq. (10)) and Supplementary Section II.2
(Eq. (S13)).

For one variable set `I` with residual constraint `β`, the paper assigns a
nonnegative mass `M α` to every admissible interface label `α`.  The ordered
labels are expanded by local two-level updates whose angles are fixed by the
residual masses `R j = M α_j + … + M α_{s-1}` via

`θ_j = arcsin sqrt (R_{j+1} / R_j)`.

The updates are chained: the first label keeps mass `R_1 cos²θ_1 = M α_1` and
transfers `R_1 sin²θ_1 = R_2` to the second label, which then repeats the same
step.  The declarations below prove that this chain realises exactly the
normalised split probabilities `M α_j / R_1`, that the total mass is one, and
that the uniform choice `M ≡ 1` gives the uniform law `1/s`.

These are the probability-accounting lemmas of Theorem 1 (Claim `c001`) and of
the uniform demand-assignment construction of Corollary 1 (Claim `c003`); the
circuit, depth and gate-count parts are separate resource ledgers.
-/

namespace Qatlib.Papers.ProbStructure26.StatePrep

open Finset

/-- Residual split mass `R j = M j + M (j+1) + … + M (s-1)` of the ordered
interface labels `j, …, s-1` of one block. -/
def residualMass (M : ℕ → ℝ) (s j : ℕ) : ℝ :=
  ∑ t ∈ Finset.Ico j s, M t

/-- Empty residual mass: past the last label the remaining mass vanishes. -/
theorem residualMass_self (M : ℕ → ℝ) (s : ℕ) : residualMass M s s = 0 := by
  simp [residualMass]

/-- The residual mass is the current label mass plus the mass of the remaining
labels, which is the accounting identity behind Eq. (S13). -/
theorem residualMass_succ {M : ℕ → ℝ} {s j : ℕ} (hj : j < s) :
    residualMass M s j = M j + residualMass M s (j + 1) := by
  unfold residualMass
  rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
  have h1 : s - j = (s - (j + 1)) + 1 := by omega
  rw [h1, Finset.sum_range_succ', add_comm]
  congr 1
  · apply Finset.sum_congr rfl
    intro k _
    congr 1
    omega

/-- A residual mass is nonnegative whenever all label masses are. -/
theorem residualMass_nonneg {M : ℕ → ℝ} {s : ℕ} (hM : ∀ t < s, 0 ≤ M t) (j : ℕ) :
    0 ≤ residualMass M s j := by
  unfold residualMass
  exact Finset.sum_nonneg (fun t ht => hM t (Finset.mem_Ico.mp ht).2)

/-- The split angle of update `j`, `θ_j = arcsin sqrt (R_{j+1} / R_j)`, exactly
as in Eq. (10) and Eq. (S13). -/
noncomputable def splitAngle (M : ℕ → ℝ) (s j : ℕ) : ℝ :=
  Real.arcsin (Real.sqrt (residualMass M s (j + 1) / residualMass M s j))

/-- The transferred fraction `sin² θ_j` equals the residual-mass ratio
`R_{j+1} / R_j` that Eq. (S13) requires. -/
theorem sin_sq_splitAngle {M : ℕ → ℝ} {s j : ℕ} (hj : j < s)
    (hM : ∀ t, t < s → 0 ≤ M t) (hpos : 0 < residualMass M s j) :
    Real.sin (splitAngle M s j) ^ 2 =
      residualMass M s (j + 1) / residualMass M s j := by
  have hsplit := residualMass_succ (M := M) hj
  have hnext : 0 ≤ residualMass M s (j + 1) := residualMass_nonneg hM (j + 1)
  have hratio : 0 ≤ residualMass M s (j + 1) / residualMass M s j := by positivity
  have hMj : 0 ≤ M j := hM j hj
  have hle : residualMass M s (j + 1) / residualMass M s j ≤ 1 := by
    rw [div_le_one hpos]
    linarith
  have hsq : -1 ≤ Real.sqrt (residualMass M s (j + 1) / residualMass M s j) := by
    have := Real.sqrt_nonneg (residualMass M s (j + 1) / residualMass M s j)
    linarith
  rw [splitAngle, Real.sin_arcsin hsq (Real.sqrt_le_one.mpr hle),
    Real.sq_sqrt hratio]

/-- The retained fraction `cos² θ_j` equals `M α_j / R_j`: update `j` deposits
exactly the mass of label `j`. -/
theorem cos_sq_splitAngle {M : ℕ → ℝ} {s j : ℕ} (hj : j < s)
    (hM : ∀ t, t < s → 0 ≤ M t) (hpos : 0 < residualMass M s j) :
    Real.cos (splitAngle M s j) ^ 2 = M j / residualMass M s j := by
  have hsplit := residualMass_succ (M := M) hj
  have hnext : 0 ≤ residualMass M s (j + 1) := residualMass_nonneg hM (j + 1)
  have hratio : 0 ≤ residualMass M s (j + 1) / residualMass M s j := by positivity
  have hMj : 0 ≤ M j := hM j hj
  have hle : residualMass M s (j + 1) / residualMass M s j ≤ 1 := by
    rw [div_le_one hpos]
    linarith
  have hnonneg : 0 ≤ 1 - residualMass M s (j + 1) / residualMass M s j := by linarith
  rw [splitAngle, Real.cos_arcsin, Real.sq_sqrt hratio, Real.sq_sqrt hnonneg]
  have hne : residualMass M s j ≠ 0 := ne_of_gt hpos
  field_simp
  linarith

/-- Telescoping of the residual-mass ratios: the fraction of the initial mass
still carried when update `j` starts is `R_j / R_0`. -/
theorem prod_residual_ratio {M : ℕ → ℝ} {s : ℕ} (hs : 0 < s)
    (hpos : ∀ t, t < s → 0 < residualMass M s t) :
    ∀ j ≤ s,
      (∏ t ∈ Finset.range j, (residualMass M s (t + 1) / residualMass M s t)) =
        residualMass M s j / residualMass M s 0 := by
  intro j hj
  induction j with
  | zero =>
      rw [Finset.prod_range_zero]
      exact (div_self (ne_of_gt (hpos 0 hs))).symm
  | succ k ih =>
      rw [Finset.prod_range_succ, ih (by omega)]
      have hk : residualMass M s k ≠ 0 := ne_of_gt (hpos k (by omega))
      have h0 : residualMass M s 0 ≠ 0 := ne_of_gt (hpos 0 hs)
      rw [div_mul_div_comm]
      field_simp

/-- Chained split-mass transfer: after the ordered updates of one block, the
mass delivered to label `j` is exactly `M j / R_0`, i.e. the conditional split
probability `p(α_j)` of Eq. (9) and Eq. (S13). -/
theorem chained_population {M : ℕ → ℝ} {s j : ℕ} (hj : j < s)
    (hpos : ∀ t, t < s → 0 < residualMass M s t) :
    (∏ t ∈ Finset.range j, (residualMass M s (t + 1) / residualMass M s t)) *
        (M j / residualMass M s j) = M j / residualMass M s 0 := by
  rw [prod_residual_ratio (by omega) hpos j (by omega)]
  have hjpos : residualMass M s j ≠ 0 := ne_of_gt (hpos j hj)
  have h0pos : residualMass M s 0 ≠ 0 := ne_of_gt (hpos 0 (by omega))
  field_simp

/-- The chained updates distribute unit total mass over the ordered labels,
so the prepared state is normalised. -/
theorem chained_population_sum_one {M : ℕ → ℝ} {s : ℕ} (hs : 0 < s)
    (hpos : ∀ t, t < s → 0 < residualMass M s t) :
    (∑ j ∈ Finset.range s,
        (∏ t ∈ Finset.range j, (residualMass M s (t + 1) / residualMass M s t)) *
          (M j / residualMass M s j)) = 1 := by
  have hterm : ∀ j ∈ Finset.range s,
      (∏ t ∈ Finset.range j, (residualMass M s (t + 1) / residualMass M s t)) *
          (M j / residualMass M s j) = M j / residualMass M s 0 := by
    intro j hj
    exact chained_population (by simpa using hj) hpos
  rw [Finset.sum_congr rfl hterm]
  rw [← Finset.sum_div]
  have hzero : residualMass M s 0 = ∑ j ∈ Finset.range s, M j := by
    unfold residualMass
    rw [Finset.sum_Ico_eq_sum_range]
    simp
  rw [hzero]
  exact div_self (by rw [← hzero]; exact ne_of_gt (hpos 0 hs))

/-- Residual mass of the constant unit mass profile is the number of remaining
labels. -/
theorem residualMass_const_one (s j : ℕ) (hj : j ≤ s) :
    residualMass (fun _ => (1 : ℝ)) s j = (s - j : ℝ) := by
  unfold residualMass
  rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one, Nat.cast_sub hj]

/-- Uniform split masses give the uniform law: every label of a block with `s`
labels receives probability `1/s`.  This is the per-row uniform law used by the
demand-assignment construction of Corollary 1. -/
theorem uniform_population {s j : ℕ} (hs : 0 < s) (hj : j < s) :
    (∏ t ∈ Finset.range j,
        (residualMass (fun _ => (1 : ℝ)) s (t + 1) / residualMass (fun _ => (1 : ℝ)) s t)) *
        (1 / residualMass (fun _ => (1 : ℝ)) s j) = 1 / (s : ℝ) := by
  have hpos : ∀ t, t < s → 0 < residualMass (fun _ => (1 : ℝ)) s t := by
    intro t ht
    rw [residualMass_const_one s t (by omega)]
    have : (t : ℝ) < (s : ℝ) := by exact_mod_cast ht
    linarith
  have hmain := chained_population (M := fun _ => (1 : ℝ)) (s := s) hj hpos
  rw [hmain]
  have h0R : residualMass (fun _ => (1 : ℝ)) s 0 = (s : ℝ) := by
    simpa using residualMass_const_one s 0 (by omega)
  rw [h0R]


/-- Split mass concentrated on the prescribed label `k`: the distribution that
puts probability one on a single feasible basis state. -/
def pointMass (k : ℕ) : ℕ → ℝ := fun t => if t = k then 1 else 0

/-- Residual mass of a point mass is one for every label at or below the
prescribed label. -/
theorem residualMass_point (k j : ℕ) (hj : j ≤ k) :
    residualMass (pointMass k) (k + 1) j = 1 := by
  unfold residualMass pointMass
  rw [Finset.sum_eq_single k]
  · simp
  · intro t _ htk
    simp [htk]
  · intro hknot
    simp only [Finset.mem_Ico, not_and, not_lt] at hknot
    omega

/-- Corollary S1, prescribed basis state: concentrating all split mass on the
unique label of a prescribed feasible string prepares that basis state with
probability one, i.e. the chain of Eq. (S13) also covers `|x*⟩`. -/
theorem prescribed_label_probability (k : ℕ) :
    (∏ t ∈ Finset.range k,
        (residualMass (pointMass k) (k + 1) (t + 1) / residualMass (pointMass k) (k + 1) t)) *
        (pointMass k k / residualMass (pointMass k) (k + 1) k) = 1 := by
  have hpos : ∀ t, t < k + 1 → 0 < residualMass (pointMass k) (k + 1) t := by
    intro t ht
    rw [residualMass_point k t (by omega)]
    norm_num
  have h := chained_population (M := pointMass k) (s := k + 1) (j := k) (by omega) hpos
  rw [h, residualMass_point k 0 (Nat.zero_le k)]
  simp [pointMass]

end Qatlib.Papers.ProbStructure26.StatePrep
