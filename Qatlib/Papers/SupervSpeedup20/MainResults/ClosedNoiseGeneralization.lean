/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SupervSpeedup20.MainResults.Definitions

@[expose] public section


/-!
# Lemma 19 and Lemma 21 — noise robustness and generalization of the SVM classifier

Fixed source: arXiv:2010.02174 (v1, 5 Oct 2020).

* **Lemma 19** (p. 22, eq. (D29)): with `R = O(m⁴)` measurement shots per kernel
  entry, with probability at least `0.99` over the random training set and the
  measurement noise, the noisy classifier value `h'(x)` and the noiseless value
  `h(x)` differ by at most `0.01` for every `x ∈ X`.
* **Lemma 21** (p. 25, eq. (D36)): for any hyperplane `w` satisfying the primal
  constraints of (D17), with probability `1 − δ` over a training set of size `m`
  the test error `Pr_{x∼X}[y⟨w,x⟩ < 0.1]` is at most
  `Õ((‖w‖₂² + ‖ξ‖₂² + log(1/δ))/m)`.

This file proves the deterministic perturbation inequality at the heart of
Lemma 19 — entrywise kernel noise of size `ε` moves the classifier value by at
most `(∑ᵢ αᵢ)·ε`, which is exactly what the paper applies to the
high-probability bounds (D31) — together with the elementary properties of the
test-error functional of Lemma 21.  The statistical packaging of both lemmas
(Markov's inequality over the joint training/noise law; the fat-shattering and
Rademacher bound of [33] behind (D36)) is recorded in the audits below.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SupervSpeedup20.MainResults

open Finset
open scoped BigOperators

/-! ## The pre-sign classifier value of Eq. (D28) -/

/-- The pre-sign SVM classifier value `h(x) = ∑ᵢ αᵢ yᵢ K(x, xᵢ)` of Eq. (D28),
for a kernel row `K t : Fin m → ℝ` over the training set. -/
def classifierVal {I : Type} {m : ℕ} (α y : Fin m → ℝ) (K : I → Fin m → ℝ)
    (t : I) : ℝ :=
  ∑ i, α i * y i * K t i

/-- Difference of two classifier values, in linear-in-the-kernel form. -/
theorem classifierVal_sub {I : Type} {m : ℕ} (α y : Fin m → ℝ)
    (K K' : I → Fin m → ℝ) (t : I) :
    classifierVal α y K' t - classifierVal α y K t =
      ∑ i, α i * y i * (K' t i - K t i) := by
  unfold classifierVal
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Lemma 19, core inequality (source p. 22, proof of (D29)).**  If every
kernel entry is perturbed by at most `ε` and the dual coefficients are
nonnegative with labels `yᵢ ∈ {±1}`, then

`|h'(x) − h(x)| ≤ (∑ᵢ αᵢ) · ε`

for every `x`.  The paper evaluates the right-hand side with the
high-probability bound (D31) on `‖Q' − Q‖_F` and `‖α‖₂²`; see
`source_lemma19`. -/
theorem classifierVal_perturbation {I : Type} {m : ℕ} (α y : Fin m → ℝ)
    (K K' : I → Fin m → ℝ) (t : I) (ε : ℝ)
    (hy : ∀ i, |y i| = 1) (hα : ∀ i, 0 ≤ α i)
    (hε : ∀ i, |K' t i - K t i| ≤ ε) :
    |classifierVal α y K' t - classifierVal α y K t| ≤ (∑ i, α i) * ε := by
  rw [classifierVal_sub]
  calc |∑ i, α i * y i * (K' t i - K t i)|
      ≤ ∑ i, |α i * y i * (K' t i - K t i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, α i * ε := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h1 : |α i * y i * (K' t i - K t i)| = α i * |K' t i - K t i| := by
          rw [abs_mul, abs_mul, hy i, abs_of_nonneg (hα i)]
          ring
        rw [h1]
        exact mul_le_mul_of_nonneg_left (hε i) (hα i)
    _ = (∑ i, α i) * ε := (Finset.sum_mul Finset.univ α ε).symm

/-- A noiseless kernel `K` together with a noisy estimate `K'` and the
entrywise perturbation bound of eqs. (D30)–(D31). -/
structure KernelPair (I : Type) where
  K : I → I → ℝ
  K' : I → I → ℝ
  /-- The entrywise noise level `ε` supplied by (D31). -/
  eps : ℝ
  heps_nonneg : 0 ≤ eps
  hdiff : ∀ t t', |K' t t' - K t t'| ≤ eps

namespace DlogWorld

end DlogWorld

/-! ## The test-error functional of Lemma 21 -/

namespace DlogWorld

attribute [local instance] NoisyHalfspaceProblem.instFintype NoisyHalfspaceProblem.instDecEq

/-- The test error `Pr_{x∼U}[y⟨w,x⟩ < 0.1]` of a hyperplane `w` on the noisy
halfspace problem, i.e. the left-hand side of eq. (D36). -/
def marginError (P : NoisyHalfspaceProblem) (w : Fin P.dim → ℝ) : ℝ := by
  letI := P.instFintype
  letI := P.instDecEq
  exact (Finset.univ.filter (fun y =>
    labelOf (P.lab y) * (∑ j, w j * P.vec y j) < 1 / 10)).sum P.unif

/-- The margin test error is nonnegative. -/
theorem marginError_nonneg (P : NoisyHalfspaceProblem) (w : Fin P.dim → ℝ) :
    0 ≤ marginError P w := by
  let := P.instFintype
  let := P.instDecEq
  exact Finset.sum_nonneg fun y _ => P.hunif_nonneg y

/-- The margin test error is at most one. -/
theorem marginError_le_one (P : NoisyHalfspaceProblem) (w : Fin P.dim → ℝ) :
    marginError P w ≤ 1 := by
  let := P.instFintype
  let := P.instDecEq
  unfold marginError
  rw [← P.hunif_sum]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun y _ _ => P.hunif_nonneg y)

/-- The generalization bound of eq. (D36) for a hyperplane `w` and slack vector
`ξ`: `Pr[y⟨w,x⟩ < 0.1] ≤ C·(‖w‖₂² + ‖ξ‖₂² + log(1/δ))/m`.  The source's
`Õ(·)` is represented by the constant `C`. -/
def GeneralizationBoundAt (P : NoisyHalfspaceProblem) (m : ℕ) (δ C : ℝ)
    (w : Fin P.dim → ℝ) (ξ : P.Y → ℝ) : Prop := by
  letI := P.instFintype
  letI := P.instDecEq
  exact marginError P w ≤
    C * ((∑ j, w j ^ 2) + (∑ y, ξ y ^ 2) + Real.log (1 / δ)) / (m : ℝ)

end DlogWorld

end Qatlib.Papers.SupervSpeedup20.MainResults
