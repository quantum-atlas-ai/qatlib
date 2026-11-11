/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Recommender18.MainResults.SqEstimation.SourceInnerProduct
import Qatlib.Concepts.SqEstimation.RejectionSample.SQRejectionAndNorm

set_option backward.isDefEq.respectTransparency false

/-!
# Proposition 4.3 — sampling from a linear combination by rejection sampling

Fixed arXiv:1807.04271, Proposition 4.3 (pp. 12–13).  Given query and sample
access to the columns `V^{(j)}` of `V ∈ ℝ^{n×k}` (with their norms), and given
`w ∈ ℝ^k`, one can output a sample from `Vw` with expected query and time
complexity `O(k² C(V,w))`, where

`C(V,w) = (Σ_j w_j² ‖V^{(j)}‖²) / ‖Vw‖²`.

Formalisation: the paper's Algorithm 1 is exactly the frozen rejection sampler.
We take the sampler's trial distribution `p` and conditional coins `coin`
(whose existence and laws are supplied by the frozen
`sq_rejection_linear_combination_access` from column access) and the weight
vector `w`; the paper's measure `C` is `Cweight`.  The frozen theorem
`sq_rejection_actual_capped_law_and_cost` then gives, for a cutoff `B` chosen so
that the timeout probability is at most `δ`:

* the per-coordinate output law is `(1 − (1−1/φ)^B)·(Vw)_i² / ‖Vw‖²`;
* the success probability is at least `1 − δ`;
* the expected primitive count is at most `4φ = 4k·C(V,w)`; since each trial
  queries all `k` coordinates of `Vw`, the expected number of queries is at most
  `4k²·C(V,w)`, matching the paper's `O(k²C)`.

The identity `φ = k·C(V,w)` (the extra factor `k` coming from the combined
envelope `sqLinearEnvelope`) is proved below as `phi_eq`.
-/

open scoped BigOperators
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SqEstimation.RejectionSample

namespace Qatlib.Papers.Recommender18.MainResults.SqEstimation

noncomputable section

/-- Squared norm of the `j`-th column of `V`. -/
def colEnergy {n k : ℕ} (V : Fin n → Fin k → ℝ) (j : Fin k) : ℝ := ∑ i, (V i j) ^ 2

/-- `Σ_j w_j² ‖V^{(j)}‖²`, the numerator of `C(V,w)`. -/
def colmulEnergy {n k : ℕ} (V : Fin n → Fin k → ℝ) (w : Fin k → ℝ) : ℝ :=
  ∑ j, (w j) ^ 2 * colEnergy V j

/-- `(Vw)_i = Σ_j V_{ij} w_j`. -/
def mulVec {n k : ℕ} (V : Fin n → Fin k → ℝ) (w : Fin k → ℝ) (i : Fin n) : ℝ :=
  ∑ j, V i j * w j

/-- `‖Vw‖²`. -/
def linEnergy {n k : ℕ} (V : Fin n → Fin k → ℝ) (w : Fin k → ℝ) : ℝ :=
  ∑ i, (mulVec V w i) ^ 2

/-- Paper's cancellation measure `C(V,w)`. -/
def Cweight {n k : ℕ} (V : Fin n → Fin k → ℝ) (w : Fin k → ℝ) : ℝ :=
  colmulEnergy V w / linEnergy V w

/-- The target vector `Vw` as a complex vector (the frozen SQ framework is
complex-valued). -/
def linTarget {n k : ℕ} (V : Fin n → Fin k → ℝ) (w : Fin k → ℝ) : Fin n → ℂ :=
  fun i => ((mulVec V w i : ℝ) : ℂ)

/-- The combined SQ envelope `sqLinearEnvelope` for the columns of `V` with
coefficients `w`.  Its squared norm includes the factor `k = card (Fin k)`. -/
def linEnv {n k : ℕ} (V : Fin n → Fin k → ℝ) (w : Fin k → ℝ) : Fin n → ℂ :=
  sqLinearEnvelope (fun j => ((w j : ℝ) : ℂ)) (fun j i => ((V i j : ℝ) : ℂ))

/-- The complex linear-combination target is exactly `sqLinearValue`. -/
theorem linTarget_eq {n k : ℕ} (V : Fin n → Fin k → ℝ) (w : Fin k → ℝ) (i : Fin n) :
    linTarget V w i =
      sqLinearValue (fun j => ((w j : ℝ) : ℂ)) (fun j i => ((V i j : ℝ) : ℂ)) i := by
  unfold linTarget mulVec sqLinearValue
  push_cast
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The squared norm of the target is `‖Vw‖²`. -/
theorem targetEnergy_eq {n k : ℕ} (V : Fin n → Fin k → ℝ) (w : Fin k → ℝ) :
    (∑ i, Complex.normSq (linTarget V w i)) = linEnergy V w := by
  simp [linTarget, linEnergy, Complex.normSq_ofReal, sq]

/-- The squared norm of the combined envelope at coordinate `i`. -/
theorem linEnv_normSq {n k : ℕ} (V : Fin n → Fin k → ℝ) (w : Fin k → ℝ) (i : Fin n) :
    Complex.normSq (linEnv V w i) = (k : ℝ) * ∑ j, (w j) ^ 2 * (V i j) ^ 2 := by
  unfold linEnv
  rw [sqLinearEnvelope_normSq]
  have hcard : (Fintype.card (Fin k) : ℝ) = (k : ℝ) := by simp
  rw [hcard]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_ofReal]
  ring

/-- Squared norm of the combined envelope, in terms of `C`'s numerator. -/
theorem envEnergy_eq {n k : ℕ} (V : Fin n → Fin k → ℝ) (w : Fin k → ℝ) :
    (∑ i, Complex.normSq (linEnv V w i)) = (k : ℝ) * colmulEnergy V w := by
  simp only [linEnv_normSq]
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  unfold colmulEnergy
  apply Finset.sum_congr rfl
  intro j _
  rw [colEnergy, Finset.mul_sum]

/-- The rejection-sampling overhead `φ` equals `k · C(V,w)`. -/
theorem phi_eq {n k : ℕ} (V : Fin n → Fin k → ℝ) (w : Fin k → ℝ)
    (hT : 0 < linEnergy V w) :
    (∑ i, Complex.normSq (linEnv V w i)) /
        (∑ i, Complex.normSq (linTarget V w i)) = (k : ℝ) * Cweight V w := by
  rw [envEnergy_eq, targetEnergy_eq]
  unfold Cweight
  field_simp

/-- The combined envelope dominates the target (finite Cauchy–Schwarz). -/
theorem linEnvelope_dominates {n k : ℕ} (V : Fin n → Fin k → ℝ) (w : Fin k → ℝ)
    (hcol : ∀ j, 0 < colEnergy V j) (i : Fin n) :
    Complex.normSq (linTarget V w i) ≤ Complex.normSq (linEnv V w i) := by
  have hcol' : ∀ j, SQEnvelope (fun i => ((V i j : ℝ) : ℂ))
      (fun i => ((V i j : ℝ) : ℂ)) := by
    intro j
    refine ⟨?_, fun i => le_rfl⟩
    have h := hcol j
    simpa [colEnergy, Complex.normSq_ofReal, sq] using h
  have h := sqLinearEnvelope_dominates (fun j => ((w j : ℝ) : ℂ))
    (fun j i => ((V i j : ℝ) : ℂ)) (fun j i => ((V i j : ℝ) : ℂ)) hcol' i
  unfold linEnv
  rwa [← linTarget_eq V w i] at h

/-- Exponential tail: for overhead `φ ≥ 1` and `δ > 0` there is a positive
cutoff `B` with timeout probability `(1 − 1/φ)^B ≤ δ`. -/
theorem exists_timeout_iterations {phi δ : ℝ} (hphi : 1 ≤ phi) (hδ : 0 < δ) :
    ∃ B : ℕ, 0 < B ∧ (1 - 1 / phi) ^ B ≤ δ := by
  have hphi0 : 0 < phi := lt_of_lt_of_le zero_lt_one hphi
  have hinv : 0 < 1 / phi := by positivity
  have hinv_le_one : 1 / phi ≤ 1 := by
    rw [div_le_one hphi0]
    exact hphi
  have hr0 : 0 ≤ 1 - 1 / phi := by linarith
  have hr1 : 1 - 1 / phi < 1 := by linarith
  have habs : |1 - 1 / phi| < 1 := by
    rw [abs_of_nonneg hr0]
    exact hr1
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hδ habs
  have hn_abs : |1 - 1 / phi| ^ n < δ := by
    simpa [Real.norm_eq_abs] using hn
  have hn' : (1 - 1 / phi) ^ n < δ := by
    rwa [abs_of_nonneg hr0] at hn_abs
  refine ⟨n + 1, Nat.succ_pos n, le_of_lt ?_⟩
  have hmono : (1 - 1 / phi) ^ (n + 1) ≤ (1 - 1 / phi) ^ n := by
    rw [pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg hr0 n) hr1.le
  calc (1 - 1 / phi) ^ (n + 1) ≤ (1 - 1 / phi) ^ n := hmono
    _ < δ := hn'

/-- Fixed arXiv:1807.04271, Proposition 4.3 (pp. 12–13).  For the rejection
sampler with trial law `p` and coins `coin` matching the column-access mixture
(the two displayed hypotheses), and for any `δ > 0`, some positive cutoff `B`
makes the timeout probability at most `δ`; then the output mass on coordinate
`i` is `(1 − (1−1/φ)^B)·(Vw)_i²/‖Vw‖²` (hence `Vw`'s ℓ₂ law in the limit), the
success probability is at least `1 − δ`, and the expected query cost is at most
`4k² C(V,w)`. -/
theorem proposition_4_3 {n k : ℕ} (V : Fin n → Fin k → ℝ) (w : Fin k → ℝ)
    (hcol : ∀ j, 0 < colEnergy V j) (hT : 0 < linEnergy V w)
    (p : FinDist (Fin n)) (coin : Fin n → FinDist Bool)
    (hp : ∀ i, p.prob i = Complex.normSq (linEnv V w i) /
      (∑ i, Complex.normSq (linEnv V w i)))
    (hc : ∀ i, (coin i).prob true = sqRatio (linTarget V w) (linEnv V w) i)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ B : ℕ, 0 < B ∧
      (∀ i, sqRejectMass p coin B (some i) =
        (1 - (1 - 1 / ((k : ℝ) * Cweight V w)) ^ B) *
          (mulVec V w i) ^ 2 / linEnergy V w) ∧
      (1 - δ ≤ ∑ ω ∈ Finset.univ.filter
        (fun ω : Fin B → Fin n × Bool => (sqRejectRun ω).1 ≠ none),
        sqTrialProduct p coin ω) ∧
      (k : ℝ) * sqRejectExpectedCost p coin B ≤ 4 * (k : ℝ) ^ 2 * Cweight V w := by
  classical
  have hen : SQEnvelope (linTarget V w) (linEnv V w) :=
    ⟨by rw [targetEnergy_eq]; exact hT, linEnvelope_dominates V w hcol⟩
  have htargetpos : 0 < ∑ i, Complex.normSq (linTarget V w i) := by
    rw [targetEnergy_eq]
    exact hT
  have hphi1 : 1 ≤ (∑ i, Complex.normSq (linEnv V w i)) /
      (∑ i, Complex.normSq (linTarget V w i)) :=
    (one_le_div htargetpos).mpr (sqEnvelope_energy _ _ hen).2
  obtain ⟨B, hBpos, hB⟩ := exists_timeout_iterations hphi1 hδ
  have hcapped := sq_rejection_actual_capped_law_and_cost (Fin n)
    (linTarget V w) (linEnv V w) p coin B hen hp hc
  refine ⟨B, hBpos, ?_, ?_, ?_⟩
  · intro i
    have h := hcapped.2.2.1 i
    rw [phi_eq V w hT] at h
    rw [sqRejectMass_eq_filter, h, targetEnergy_eq]
    have hnorm : Complex.normSq (linTarget V w i) = (mulVec V w i) ^ 2 := by
      simp [linTarget, Complex.normSq_ofReal, sq]
    rw [hnorm]
  · have h := hcapped.2.2.2.2.2 δ hδ
    rw [phi_eq V w hT] at hB
    apply h
    rw [phi_eq V w hT]
    exact hB
  · have h := hcapped.2.2.2.2.1
    calc (k : ℝ) * sqRejectExpectedCost p coin B
        ≤ (k : ℝ) * (4 * ((∑ i, Complex.normSq (linEnv V w i)) /
            (∑ i, Complex.normSq (linTarget V w i)))) :=
          mul_le_mul_of_nonneg_left h (Nat.cast_nonneg k)
      _ = (k : ℝ) * (4 * ((k : ℝ) * Cweight V w)) := by rw [phi_eq V w hT]
      _ = 4 * (k : ℝ) ^ 2 * Cweight V w := by ring

end

end Qatlib.Papers.Recommender18.MainResults.SqEstimation
