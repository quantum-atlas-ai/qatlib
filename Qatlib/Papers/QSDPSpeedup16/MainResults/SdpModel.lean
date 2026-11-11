/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Scalar SDP model for Brandão–Svore, *Quantum Speed-ups for Semidefinite Programming*

Fixed source: arXiv:1609.05537v5 (PDF SHA-256
746714c3d97424df74d7f5956107687f73c6501403e35af757421328dfb030b7).
Printed Eq. (2), p. 3; Appendix A (Lemma 18), pp. 21–22.

The model records only the scalar objective layer of the source SDP that is used by
Lemma 2 / Lemma 18: the objective `∑ bᵢ yᵢ`, the lifted objective of Eq. (98)
`∑ᵢ bᵢ yᵢ + (R+1)∑ᵢ yᵢ`, and the coordinate truncation `(y₁,…,y_{m+1}) ↦ (y₁,…,y_m)`.
The positive-semidefinite constraint `∑ yᵢ Aᵢ ⪰ C`, the `n → n+1` block lifting of the
source, and the DIMACS-style sampling/measurement channel are *not* encoded here; they
belong to the algorithmic layer and are documented at the using theorems.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QSDPSpeedup16.MainResults.SdpModel

/-- Objective of the source SDP (2): `∑ bᵢ yᵢ`. -/
def sdpObjective {m : ℕ} (b y : Fin m → ℝ) : ℝ :=
  ∑ i, b i * y i

/-- Objective of the lifted SDP of Appendix A, Eq. (98):
`∑_{i<m} bᵢ yᵢ + (R+1) ∑_{i≤m} yᵢ`. -/
def liftedObjective {m : ℕ} (b : Fin m → ℝ) (R : ℝ) (y : Fin (m + 1) → ℝ) : ℝ :=
  (∑ i : Fin m, b i * y i.castSucc) + (R + 1) * ∑ i : Fin (m + 1), y i

/-- Coordinate truncation `(y₁,…,y_{m+1}) ↦ (y₁,…,y_m)` used in Lemma 18 to pass from a
solution of the lifted SDP back to the original SDP. -/
def truncate {m : ℕ} (y : Fin (m + 1) → ℝ) : Fin m → ℝ :=
  fun i => y i.castSucc

/-- The Appendix-A test solution Eq. (102): first `m` coordinates are the optimal
solution `z` of the original SDP, the last coordinate is `∑ yᵢ − ∑ zᵢ`. -/
def liftWitness {m : ℕ} (z : Fin m → ℝ) (y : Fin (m + 1) → ℝ) : Fin (m + 1) → ℝ :=
  Fin.snoc z ((∑ i : Fin (m + 1), y i) - ∑ i : Fin m, z i)

/-- The lifted objective splits as the truncated objective plus
`(R+1) ∑_{i≤m} yᵢ`. -/
theorem liftedObjective_eq_truncate {m : ℕ} (b : Fin m → ℝ) (R : ℝ)
    (y : Fin (m + 1) → ℝ) :
    liftedObjective b R y = sdpObjective b (truncate y) + (R + 1) * ∑ i : Fin (m + 1), y i := by
  unfold liftedObjective sdpObjective truncate
  rfl

/-- The truncated objective is at most the lifted objective when `R ≥ 0` and all
coordinates of `y` are nonnegative (the lifted objective carries the extra
nonnegative mass term `(R+1) ∑ yᵢ`). -/
theorem sdpObjective_truncate_le_liftedObjective {m : ℕ} (b : Fin m → ℝ) (R : ℝ)
    (y : Fin (m + 1) → ℝ) (hR : 0 ≤ R) (hy : ∀ i, 0 ≤ y i) :
    sdpObjective b (truncate y) ≤ liftedObjective b R y := by
  rw [liftedObjective_eq_truncate]
  have hsum : 0 ≤ ∑ i : Fin (m + 1), y i := Finset.sum_nonneg (fun i _ => hy i)
  have hcoef : 0 ≤ R + 1 := by linarith
  have hmul : 0 ≤ (R + 1) * ∑ i : Fin (m + 1), y i := mul_nonneg hcoef hsum
  linarith

/-- The lifted objective of the Appendix-A witness Eq. (102) equals the original
optimal value plus `(R+1) ∑ yᵢ`. -/
theorem liftedObjective_liftWitness {m : ℕ} (b : Fin m → ℝ) (R : ℝ) (z : Fin m → ℝ)
    (y : Fin (m + 1) → ℝ) :
    liftedObjective b R (liftWitness z y) =
      sdpObjective b z + (R + 1) * ∑ i : Fin (m + 1), y i := by
  unfold liftedObjective liftWitness sdpObjective
  simp only [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
  ring

/-- The Appendix-A witness is nonnegative: its first `m` coordinates are `z ≥ 0`, and
its last coordinate `∑ yᵢ − ∑ zᵢ` is nonnegative because the lifted sample has
`y_last ≥ r ≥ ∑ zᵢ`. -/
theorem liftWitness_nonneg {m : ℕ} (z : Fin m → ℝ) (y : Fin (m + 1) → ℝ) {r : ℝ}
    (hz : ∀ i, 0 ≤ z i) (hy : ∀ i, 0 ≤ y i) (hy_last : r ≤ y (Fin.last m))
    (hz_sum : ∑ i : Fin m, z i ≤ r) :
    ∀ i, 0 ≤ liftWitness z y i := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [liftWitness, Fin.snoc_last]
    have hsum_ge : ∑ i : Fin m, z i ≤ ∑ i : Fin (m + 1), y i := by
      rw [Fin.sum_univ_castSucc]
      have hnonneg : 0 ≤ ∑ i : Fin m, y i.castSucc :=
        Finset.sum_nonneg (fun i _ => hy i.castSucc)
      linarith
    linarith
  · simp only [liftWitness, Fin.snoc_castSucc]
    exact hz j

/-- The total mass of the Appendix-A witness is the total mass `∑ yᵢ` of the lifted
sample, hence at least `r`. -/
theorem liftWitness_sum_ge {m : ℕ} (z : Fin m → ℝ) (y : Fin (m + 1) → ℝ) {r : ℝ}
    (hy : ∀ i, 0 ≤ y i) (hy_last : r ≤ y (Fin.last m)) :
    r ≤ ∑ i : Fin (m + 1), liftWitness z y i := by
  simp only [liftWitness, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
  have hnonneg : 0 ≤ ∑ i : Fin m, y i.castSucc :=
    Finset.sum_nonneg (fun i _ => hy i.castSucc)
  linarith

/-- Coefficient lifting `b' = snoc b (R+1)` of Appendix A: if `bᵢ ≥ 1` and `R ≥ 0`, the
lifted coefficient vector of the SDP (98) has all entries at least one, extends `b`, and
its last entry is `R+1`. -/
theorem exists_liftedCoefficients {m : ℕ} (b : Fin m → ℝ) (R : ℝ)
    (hb : ∀ i, 1 ≤ b i) (hR : 0 ≤ R) :
    ∃ liftedB : Fin (m + 1) → ℝ,
      (∀ i, 1 ≤ liftedB i) ∧ liftedB (Fin.last m) = R + 1 ∧
      ∀ i : Fin m, liftedB i.castSucc = b i := by
  refine ⟨Fin.snoc b (R + 1), ?_, ?_, ?_⟩
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last]
      linarith
    · simp only [Fin.snoc_castSucc]
      exact hb j
  · simp only [Fin.snoc_last]
  · intro i
    simp only [Fin.snoc_castSucc]

end Qatlib.Papers.QSDPSpeedup16.MainResults.SdpModel
